//! P5 atomic batch publication (P2 T12; docs/atomic-pub-log.md) for a published rename.
//!
//! Four commands, each run by the process that holds the key it needs:
//!
//! | Command | Keys | Effect |
//! |---|---|---|
//! | `batch-validate` | controller (authority seed) | signs the intent, issues every member's job bound to it, validates them in order with one `ValidateBatch`, places the markers and tombstones, writes the unsigned batch file |
//! | `batch-sign` | one workspace's own key file | checks the intent and that workspace's members, signs their certificates |
//! | `batch-publish` | none needed | assembles the members and certificates and runs `Store::publish_batch` |
//! | `batch-status` | none needed | reads the batch record and every member's marker or tombstone |
//!
//! The coordinator never holds a member key: each workspace signs only its own members, in
//! its own process, from its own key file (P5 provisions `keys-<agent>.json` with that
//! workspace's seed alone). T12 then checks every member's guards in one transaction, so a
//! stale owner, epoch or head on any member rejects the whole batch.
//!
//! Placement follows `ws-plan` (`Paralean.Copy.plan`): a member that keeps a name of a group
//! it replaces revises that name (the old revision is the parent, the old root path and
//! lineage key are kept); a renamed member is inserted after the group it replaces. Its
//! Lamport time is above every replaced or deleted record and the caller's floor (the
//! largest time the working copies know).

use std::collections::BTreeSet;
use std::fs;
use std::io::Write;
use std::time::{Duration, Instant};

use paralean_control::checker::{base_id, CheckerConfig};
use paralean_store::receipt::{self, Policy, TargetBinding};
use paralean_store::{
    AgentId, Anchor, BatchIntent, BatchItem, BatchMember, BatchPackage, Id, JobEnvelope, KeyFile, Kind, Marker, Name,
    Object, Opaque, Package, PreparedTarget, Receipt, Revision, Signed, SignedBatch, SignedJob, Store, StoreError,
    Tombstone, TombstoneCert, Verdict, WorkspaceId, Writer, MAX_BATCH_MEMBERS,
};
use paralean_validator_api::{decode_receipt, rpc, ValidatorRequest, ValidatorResponse};
use serde_json::{json, Value};

use crate::targets::{ms, need, open, parse_hash, parse_id, Cache, R};

const FORMAT: &str = "paralean-p5-batch/1";

pub async fn run(args: &[String]) -> R<Value> {
    match args.first().map(String::as_str) {
        Some("batch-validate") => batch_validate(args).await,
        Some("batch-sign") => batch_sign(args).await,
        Some("batch-publish") => batch_publish(args).await,
        Some("batch-status") => batch_status(args).await,
        _ => Err("unknown batch bridge command".into()),
    }
}

fn hexed(b: &[u8]) -> Value {
    json!(hex::encode(b))
}
fn unhex(v: &Value, what: &str) -> R<Vec<u8>> {
    hex::decode(v.as_str().ok_or_else(|| format!("{what} must be hex"))?).map_err(|_| format!("{what} is not hex"))
}
fn str_of<'a>(v: &'a Value, field: &str) -> R<&'a str> {
    v.get(field).and_then(Value::as_str).ok_or_else(|| format!("member {field} missing"))
}

/// A workspace's ID from the key file, without touching its seed.
fn workspace_id(kf: &KeyFile, name: &str) -> R<WorkspaceId> {
    let entry = kf.workspaces.get(name).ok_or("workspace is not in the key file")?;
    WorkspaceId::from_hex(&entry.id).ok_or("bad workspace ID in key file".into())
}

/// A file created only if its name is unused, private from creation.
fn write_new(path: &str, bytes: &[u8]) -> R<()> {
    use std::os::unix::fs::OpenOptionsExt;
    let mut f = fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(path)
        .map_err(|e| format!("{path}: {e}"))?;
    f.write_all(bytes).and_then(|_| f.sync_all()).map_err(|e| format!("{path}: {e}"))
}

/// The group and capsule payloads of a member, read from its working copy's cache and
/// checked against their content IDs (the cache is worker-controlled).
fn payloads(cache_dir: &str, group: &Id, capsule: &Id) -> R<(Opaque, Opaque)> {
    let c = Cache::new(cache_dir);
    let g = Opaque::new(Kind::Group, fs::read(c.object(group)).map_err(|e| format!("payload {group}: {e}"))?);
    let cap = Opaque::new(Kind::Capsule, fs::read(c.capsule(capsule)).map_err(|e| format!("capsule {capsule}: {e}"))?);
    if g.id() != *group || cap.id() != *capsule {
        return Err("cached payload differs from its content ID".into());
    }
    Ok((g, cap))
}

// ---------------------------------------------------------------- batch-validate

/// One publication member of the spec, resolved against the store.
struct Planned {
    ws: String,
    wid: WorkspaceId,
    cache: String,
    group: Opaque,
    capsule: Opaque,
    deps: Vec<Id>,
    file: String,
    names: Vec<Name>,
    /// The published groups this member supersedes (same position, same author).
    replaces: Vec<(Id, Marker)>,
    targets: Vec<PreparedTarget>,
    bindings: Vec<TargetBinding>,
}

/// `batch-validate --spec SPEC --validator ADDR --out BATCH`
///
/// SPEC is `{"request", "lamport_floor", "members": [...]}` in commit order. A publication
/// member is `{"kind": "publish", "ws", "cache", "group", "capsule", "deps", "file",
/// "names", "replaces", "target"}` (`target`: null or `{"name", "epoch",
/// "statement_hash"}`, the frozen contract and the epoch the controller dispatched); a
/// deletion is `{"kind": "tombstone", "ws", "target"}`, deleting that group's current
/// position. Nothing becomes visible: the payloads and issued jobs are unpublished.
async fn batch_validate(args: &[String]) -> R<Value> {
    let t = Instant::now();
    let (store, kf) = open()?;
    let authority = kf.authority_signer().ok_or("authority seed required for a batch intent")?;
    let spec: Value = serde_json::from_slice(&fs::read(need(args, "--spec")?).map_err(|e| e.to_string())?)
        .map_err(|e| format!("invalid batch spec: {e}"))?;
    let request = spec.get("request").and_then(Value::as_str).ok_or("spec.request missing")?.as_bytes().to_vec();
    if request.is_empty() || request.len() > 128 {
        return Err("batch request must be 1..128 bytes".into());
    }
    let floor = spec.get("lamport_floor").and_then(Value::as_u64).ok_or("spec.lamport_floor missing")?;
    let rows = spec.get("members").and_then(Value::as_array).ok_or("spec.members must be an array")?;
    if rows.is_empty() || rows.len() > MAX_BATCH_MEMBERS {
        return Err(format!("a batch has 1 to {MAX_BATCH_MEMBERS} members"));
    }
    let checker = CheckerConfig::from_env()?;
    let checker_id = parse_id(kf.checkers.first().ok_or("no checker pin")?)?;
    if checker.version()?.id() != checker_id {
        return Err("configured checker differs from key pin".into());
    }
    let federation = store.ae_federation().await.map_err(|e| e.to_string())?;

    // Resolve every member against the store first: the intent names exact positions.
    enum Row { Publish(Box<Planned>), Tombstone { ws: String, wid: WorkspaceId, target: Id, position: Id, marker: Marker } }
    let mut planned = Vec::with_capacity(rows.len());
    let mut lamport = floor;
    for row in rows {
        let ws = str_of(row, "ws")?.to_owned();
        let wid = workspace_id(&kf, &ws)?;
        let author = AgentId(wid.0);
        match str_of(row, "kind")? {
            "publish" => {
                let cache_dir = str_of(row, "cache")?.to_owned();
                let (group, capsule) = payloads(&cache_dir, &parse_id(str_of(row, "group")?)?, &parse_id(str_of(row, "capsule")?)?)?;
                let ids = |field: &str| -> R<Vec<Id>> {
                    row.get(field).and_then(Value::as_array).ok_or_else(|| format!("member {field} missing"))?
                        .iter().map(|v| parse_id(v.as_str().ok_or("ID must be hex")?)).collect()
                };
                let names: Vec<Name> = row.get("names").and_then(Value::as_array).ok_or("member names missing")?
                    .iter().map(|v| v.as_str().map(Name::parse).ok_or("name must be a string")).collect::<Result<_, _>>()?;
                if names.is_empty() || names.iter().any(|n| n.0.is_empty()) {
                    return Err("a batch member must declare a name".into());
                }
                let file = str_of(row, "file")?.to_owned();
                let mut replaces = Vec::new();
                for old in ids("replaces")? {
                    let (_, m) = store.marker(&old).await.map_err(|e| e.to_string())?.ok_or("replaced group is not published")?;
                    if (m.author != author || m.file_path != file) && !cfg!(feature = "mutate-batch-any-replaced") {
                        return Err("a batch member replaces only its own workspace's declaration in the same file".into());
                    }
                    lamport = lamport.max(m.lamport);
                    replaces.push((old, m));
                }
                let (mut targets, mut bindings) = (Vec::new(), Vec::new());
                if let Some(target) = row.get("target").filter(|v| !v.is_null()) {
                    let n = Name::parse(str_of(target, "name")?);
                    if !names.contains(&n) {
                        return Err("target binding names no declared member".into());
                    }
                    // Writer::prepare_target's reads, without the workspace's seed.
                    if let Some(cfg) = &federation {
                        if cfg.target_homes.get(&n) != Some(&cfg.deployment) {
                            return Err(format!("target {n} is assigned to a foreign federation home"));
                        }
                    }
                    let rec = store.target(&n).await.map_err(|e| e.to_string())?.ok_or("target record absent")?;
                    if rec.owner != wid && !cfg!(feature = "mutate-batch-any-owner") {
                        return Err(format!("target {n} is owned by another workspace"));
                    }
                    if Some(rec.epoch) != target.get("epoch").and_then(Value::as_u64) && !cfg!(feature = "mutate-batch-any-epoch") {
                        return Err(format!("target {n} epoch changed after controller dispatch"));
                    }
                    let statement = parse_hash(str_of(target, "statement_hash")?)?;
                    bindings.push(TargetBinding { name: n.clone(), epoch: rec.epoch, statement });
                    targets.push(PreparedTarget { name: n, epoch: rec.epoch, head: rec.head });
                }
                planned.push(Row::Publish(Box::new(Planned {
                    ws, wid, cache: cache_dir, group, capsule, deps: ids("deps")?, file, names, replaces, targets, bindings,
                })));
            }
            "tombstone" => {
                let target = parse_id(str_of(row, "target")?)?;
                let (position, marker) = store.marker(&target).await.map_err(|e| e.to_string())?
                    .ok_or("deleted group is not published")?;
                // W3: an author deletes its own position; this path takes no controller grant.
                if marker.author != author && !cfg!(feature = "mutate-batch-any-deleter") {
                    return Err("a batch deletes only its own workspace's declaration".into());
                }
                lamport = lamport.max(marker.lamport);
                planned.push(Row::Tombstone { ws, wid, target, position, marker });
            }
            other => return Err(format!("unknown batch member kind {other:?}")),
        }
    }
    let intent = SignedBatch::sign(BatchIntent {
        request,
        members: planned.iter().map(|r| match r {
            Row::Publish(p) => BatchMember::Publish { group: p.group.id(), writer: p.wid },
            Row::Tombstone { wid, target, position, .. } => BatchMember::Tombstone { target: *target, position: Some(*position), writer: *wid },
        }).collect(),
    }, &authority);
    let batch = intent.id();

    // Each publication: its payloads where the validator reads them, then its job.
    let mut jobs = Vec::new();
    for row in &planned {
        let Row::Publish(p) = row else { continue };
        store.s3.put_opaque(&p.group).await.map_err(|e| e.to_string())?;
        store.s3.put_opaque(&p.capsule).await.map_err(|e| e.to_string())?;
        let job = Signed::sign(JobEnvelope {
            request: rand::random::<[u8; 16]>().to_vec(),
            group: p.group.id(),
            capsule: p.capsule.id(),
            deps: p.deps.clone(),
            base: base_id(&checker.lean_githash),
            policy: Policy::v1().id(),
            checker: checker_id,
            worker: p.wid,
            targets: p.bindings.clone(),
            deadline_ms: 1_800_000,
            memory_mb: 0,
            batch: Some(batch),
        }, &authority);
        jobs.push(store.meta.issue_job(&job).await.map_err(|e| e.to_string())?);
    }
    // Dependency order is commit order: an earlier member's receipt serves a later one.
    // A batch of deletions alone has nothing to check.
    let responses = if jobs.is_empty() { vec![] } else {
        let request = ValidatorRequest::ValidateBatch { jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect() };
        let response: ValidatorResponse = rpc::call_authenticated_any(need(args, "--validator")?, &request, &authority,
            &store.ring.validators, Duration::from_secs(1800)).await.map_err(|e| e.to_string())?;
        let ValidatorResponse::Batch { responses } = response else {
            return Err(format!("validator gave no batch answer: {response:?}"));
        };
        responses
    };
    if responses.len() != jobs.len() {
        return Err("validator answered another number of jobs".into());
    }
    let mut receipts = Vec::new();
    let publications = planned.iter().filter_map(|r| match r { Row::Publish(p) => Some(p), _ => None });
    for ((p, job), response) in publications.zip(&jobs).zip(responses) {
        let receipt = match response {
            ValidatorResponse::Receipt { receipt } => decode_receipt(&receipt)?,
            other => return Ok(json!({"accepted": false, "group": p.group.id().hex(),
                "reason": format!("validator gave no receipt: {other:?}")})),
        };
        if let Verdict::Rejected(reason) = &receipt.body.verdict {
            return Ok(json!({"accepted": false, "group": p.group.id().hex(), "reason": reason}));
        }
        // The strict verifier, the binding to exactly this job and the pins.
        receipt::check(&receipt, job, &p.group.id(), &p.targets, &store.ring).map_err(|e| e.to_string())?;
        receipts.push(receipt);
    }

    let mut members = Vec::new();
    let mut publications = jobs.into_iter().zip(receipts);
    for row in &planned {
        lamport = lamport.checked_add(1).ok_or("Lamport clock overflow")?;
        match row {
            Row::Publish(p) => {
                let (job, receipt) = publications.next().ok_or("missing receipt")?;
                let (marker, revisions) = place(p, &store, &receipt, lamport).await?;
                members.push(json!({"kind": "publish", "ws": p.ws, "workspace": p.wid.hex(), "cache": p.cache,
                    "group": p.group.id().hex(), "capsule": p.capsule.id().hex(),
                    "job": hexed(&job.to_bytes()), "receipt": hexed(&receipt.to_bytes()),
                    "marker": hexed(&marker.preimage()),
                    "revisions": revisions.iter().map(|r| hexed(&r.preimage())).collect::<Vec<_>>(),
                    "targets": p.targets.iter().map(|t| json!({"name": t.name.to_string(), "epoch": t.epoch,
                        "head": t.head.map(|h| h.hex())})).collect::<Vec<_>>()}));
            }
            Row::Tombstone { ws, wid, target, position, marker } => {
                let tomb = Tombstone {
                    file_path: marker.file_path.clone(), target: *target, lamport, author: marker.author,
                    receipt: None, position: Some(*position), batch: Some(batch),
                };
                members.push(json!({"kind": "tombstone", "ws": ws, "workspace": wid.hex(),
                    "target": target.hex(), "tombstone": hexed(&tomb.preimage())}));
            }
        }
    }
    let file = json!({"format": FORMAT, "intent": hexed(&intent.to_bytes()), "members": members});
    write_new(need(args, "--out")?, file.to_string().as_bytes())?;
    Ok(json!({"accepted": true, "batch": batch.hex(), "members": planned.len(), "ms": ms(t)}))
}

/// The marker and revisions of a publication member, as `ws-plan` places them.
async fn place(p: &Planned, store: &Store, receipt: &Receipt, lamport: u64) -> R<(Marker, Vec<Revision>)> {
    let g = p.group.id();
    let author = AgentId(p.wid.0);
    let mut revisions = Vec::new();
    let mut lineage_keys = Vec::new();
    let mut revised_root = None;
    for n in &p.names {
        let mut parents = Vec::new();
        for (_, m) in &p.replaces {
            for rid in &m.revisions {
                let r = store.revision(rid).await.map_err(|e| e.to_string())?.ok_or("replaced revision absent")?;
                if r.name == *n {
                    parents.push(*rid);
                    let key = m.lineage_keys.iter().find(|k| k.0 == *n).map_or((m.lamport, m.author), |k| (k.1, k.2));
                    if !lineage_keys.iter().any(|k: &(Name, u64, AgentId)| k.0 == *n) {
                        lineage_keys.push((n.clone(), key.0, key.1));
                    }
                    revised_root.get_or_insert_with(|| m.root_path.clone());
                }
            }
        }
        if parents.is_empty() {
            lineage_keys.push((n.clone(), lamport, author));
        }
        // A target proof must list the head it was prepared against (T1).
        if let Some(head) = p.targets.iter().find(|t| t.name == *n).and_then(|t| t.head) {
            if !parents.contains(&head) {
                return Err(format!("target {n} head is not the declaration this member revises"));
            }
        }
        parents.sort();
        parents.dedup();
        revisions.push(Revision { group: g, name: n.clone(), parents, capsule: p.capsule.id(), workspace: p.wid });
    }
    let (anchor, root_path) = match revised_root {
        Some(path) => (Anchor::FileStart, path),
        None => {
            // A renamed declaration takes the place right after the one it replaces.
            let (_, m) = p.replaces.first().ok_or("an inserted member must name the declaration it replaces")?;
            let mut path = m.root_path.clone();
            let anchor = path.last().map_or(Anchor::FileStart, |x| Anchor::After(x.0));
            path.push((g, lamport, author));
            (anchor, path)
        }
    };
    let mut rids: Vec<Id> = revisions.iter().map(|r| r.id()).collect();
    rids.sort();
    let marker = Marker {
        group: g, revisions: rids, receipt: receipt.id(), file_path: p.file.clone(), anchor, lamport, author,
        root_path, lineage_keys,
    };
    marker.check().map_err(|e| format!("member file: {e}"))?;
    Ok((marker, revisions))
}

// ---------------------------------------------------------------- the batch file

/// A decoded batch file: the intent and every member, as T12 will see them.
struct BatchFile {
    intent: SignedBatch,
    members: Vec<FileMember>,
}

enum FileMember {
    Publish { ws: String, wid: WorkspaceId, package: Box<Package> },
    Tombstone { ws: String, wid: WorkspaceId, tombstone: Tombstone },
}

impl FileMember {
    fn writer(&self) -> (&str, WorkspaceId) {
        match self {
            FileMember::Publish { ws, wid, .. } | FileMember::Tombstone { ws, wid, .. } => (ws, *wid),
        }
    }
}

fn read_batch(path: &str) -> R<BatchFile> {
    let v: Value = serde_json::from_slice(&fs::read(path).map_err(|e| format!("{path}: {e}"))?)
        .map_err(|e| format!("invalid batch file: {e}"))?;
    if v.get("format").and_then(Value::as_str) != Some(FORMAT) {
        return Err("unsupported batch file format".into());
    }
    let intent = SignedBatch::from_bytes(&unhex(&v["intent"], "intent")?).map_err(|e| e.to_string())?;
    let rows = v.get("members").and_then(Value::as_array).ok_or("batch members missing")?;
    if rows.len() != intent.body.members.len() {
        return Err("batch file members differ from its intent".into());
    }
    let mut members = Vec::new();
    for row in rows {
        let ws = str_of(row, "ws")?.to_owned();
        let wid = WorkspaceId::from_hex(str_of(row, "workspace")?).ok_or("bad member workspace ID")?;
        members.push(match str_of(row, "kind")? {
            "publish" => {
                let (group, capsule) = payloads(str_of(row, "cache")?, &parse_id(str_of(row, "group")?)?,
                    &parse_id(str_of(row, "capsule")?)?)?;
                let revisions = row.get("revisions").and_then(Value::as_array).ok_or("member revisions missing")?
                    .iter().map(|r| Revision::from_preimage(&unhex(r, "revision")?).map_err(|e| e.to_string()))
                    .collect::<R<Vec<_>>>()?;
                let targets = row.get("targets").and_then(Value::as_array).ok_or("member targets missing")?
                    .iter().map(|t| Ok(PreparedTarget {
                        name: Name::parse(str_of(t, "name")?),
                        epoch: t.get("epoch").and_then(Value::as_u64).ok_or("target epoch missing")?,
                        head: t.get("head").and_then(Value::as_str).map(parse_id).transpose()?,
                    })).collect::<R<Vec<_>>>()?;
                FileMember::Publish { ws, wid, package: Box::new(Package {
                    group, chunks: vec![], capsule,
                    receipt: Receipt::from_bytes(&unhex(&row["receipt"], "receipt")?).map_err(|e| e.to_string())?,
                    job: SignedJob::from_bytes(&unhex(&row["job"], "job")?).map_err(|e| e.to_string())?,
                    revisions,
                    marker: Marker::from_preimage(&unhex(&row["marker"], "marker")?).map_err(|e| e.to_string())?,
                    targets,
                }) }
            }
            "tombstone" => FileMember::Tombstone { ws, wid,
                tombstone: Tombstone::from_preimage(&unhex(&row["tombstone"], "tombstone")?).map_err(|e| e.to_string())? },
            other => return Err(format!("unknown batch member kind {other:?}")),
        });
    }
    Ok(BatchFile { intent, members })
}

// ---------------------------------------------------------------- batch-sign

/// `batch-sign --batch BATCH --ws NAME --out CERTS`, with `PARALEAN_KEYS` naming that
/// workspace's own key file.
///
/// The workspace signs a certificate only for a member it authors, of an intent the
/// controller signed, bound to that intent, answering a controller-signed job with an
/// accepted, bound receipt. It refuses a key file holding any other seed: a coordinator
/// that passed the full controller file would otherwise sign as every workspace.
async fn batch_sign(args: &[String]) -> R<Value> {
    let (store, kf) = open()?;
    let ws = need(args, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or("workspace seed is not in the key file")?;
    let foreign = kf.authority.is_some()
        || kf.validators.values().any(|e| e.seed.is_some())
        || kf.workspaces.iter().chain(&kf.job_issuers).any(|(name, e)| name != ws && e.seed.is_some());
    if foreign && !cfg!(feature = "mutate-batch-sign-any-keys") {
        return Err("batch-sign takes the workspace's own key file, holding no other seed".into());
    }
    let file = read_batch(need(args, "--batch")?)?;
    let ring = &store.ring;
    if !file.intent.issued_by_controller(ring) && !cfg!(feature = "mutate-batch-sign-unsigned-intent") {
        return Err("batch intent is not signed by the controller".into());
    }
    let batch = file.intent.id();
    let author = AgentId(wid.0);
    let writer = Writer::new(store.clone(), wid, signer);
    let mut certs = Vec::new();
    for (i, (member, named)) in file.members.iter().zip(&file.intent.body.members).enumerate() {
        if member.writer().1 != wid {
            continue;
        }
        if member.writer().0 != ws {
            return Err("batch member names this workspace under another name".into());
        }
        let cert = match member {
            FileMember::Publish { package: p, .. } => {
                let g = p.group.id();
                if *named != (BatchMember::Publish { group: g, writer: wid }) {
                    return Err("member differs from the signed intent".into());
                }
                let j = &p.job.body;
                if (j.batch != Some(batch) || j.worker != wid || j.group != g || j.capsule != p.capsule.id())
                    && !cfg!(feature = "mutate-batch-sign-unbound-job") {
                    return Err("member job is not bound to this batch, workspace and package".into());
                }
                if !p.job.verify(&ring.authority) {
                    return Err("member job is not signed by the controller".into());
                }
                receipt::check(&p.receipt, &p.job, &g, &p.targets, ring).map_err(|e| e.to_string())?;
                let m = &p.marker;
                let mut rids: Vec<Id> = p.revisions.iter().map(|r| r.id()).collect();
                rids.sort();
                if m.group != g || m.receipt != p.receipt.id() || m.author != author || m.revisions != rids
                    || p.revisions.iter().any(|r| r.group != g || r.workspace != wid || r.capsule != p.capsule.id()) {
                    return Err("member marker or revisions do not belong to this workspace's package".into());
                }
                m.check().map_err(|e| format!("member file: {e}"))?;
                writer.sign_batch_publication(p).to_bytes()
            }
            FileMember::Tombstone { tombstone: t, .. } => {
                if *named != (BatchMember::Tombstone { target: t.target, position: t.position, writer: wid }) {
                    return Err("member differs from the signed intent".into());
                }
                if t.batch != Some(batch) || t.author != author {
                    return Err("member tombstone is not this workspace's deletion in this batch".into());
                }
                t.check().map_err(|e| format!("tombstone file: {e}"))?;
                writer.sign_batch_tombstone(t).to_bytes()
            }
        };
        certs.push(json!({"index": i, "cert": hexed(&cert)}));
    }
    if certs.is_empty() {
        return Err("batch has no member written by this workspace".into());
    }
    let out = json!({"batch": batch.hex(), "ws": ws, "workspace": wid.hex(), "certs": certs});
    write_new(need(args, "--out")?, out.to_string().as_bytes())?;
    Ok(json!({"batch": batch.hex(), "ws": ws, "signed": out["certs"].as_array().map_or(0, Vec::len)}))
}

// ---------------------------------------------------------------- batch-publish

/// Test builds only (`--features test-faults`): inject one T12 commit fault named by
/// `PARALEAN_P5_TEST_FAULT`, in the first process that creates the file
/// `PARALEAN_P5_TEST_FAULT_ONCE` (so a caller's re-run is not faulted again). The release
/// bridge has no such hook.
#[cfg(feature = "test-faults")]
fn test_faults(store: &mut Store) -> R<()> {
    use paralean_store::{CommitFault, Txn};
    let Ok(fault) = std::env::var("PARALEAN_P5_TEST_FAULT") else { return Ok(()) };
    if let Ok(once) = std::env::var("PARALEAN_P5_TEST_FAULT_ONCE") {
        if fs::OpenOptions::new().write(true).create_new(true).open(once).is_err() {
            return Ok(());
        }
    }
    let f = &store.faults;
    match fault.as_str() {
        "unknown-committed" => f.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownCommitted),
        "unknown-not-committed" => f.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownNotCommitted),
        "crash-before-commit" => f.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::CrashBeforeCommit),
        "crash-after-commit" => f.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::CrashAfterCommit),
        "unresolved" => {
            store.meta.max_attempts = 3;
            for _ in 0..3 {
                f.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownNotCommitted);
            }
        }
        other => return Err(format!("unknown test fault {other:?}")),
    }
    Ok(())
}

/// `batch-publish --batch BATCH --certs CERTS [--certs CERTS ...]`
///
/// Prints `{"outcome": "committed" | "refused" | "unresolved", ...}`. `refused` means a
/// guard failed, so T12 wrote nothing. `unresolved` means the store's retry loop could not
/// learn whether T12 committed: running this command again with the same files resolves
/// it, since T12 is idempotent through its batch record. Any other failure exits nonzero
/// and is equally unknown to the caller.
async fn batch_publish(args: &[String]) -> R<Value> {
    let t = Instant::now();
    let (store, _) = open()?;
    #[cfg(feature = "test-faults")]
    let store = { let mut store = store; test_faults(&mut store)?; store };
    let file = read_batch(need(args, "--batch")?)?;
    let batch = file.intent.id();
    let mut certs: Vec<Option<Vec<u8>>> = vec![None; file.members.len()];
    for path in args.windows(2).filter(|w| w[0] == "--certs").map(|w| w[1].as_str()) {
        let v: Value = serde_json::from_slice(&fs::read(path).map_err(|e| format!("{path}: {e}"))?)
            .map_err(|e| format!("invalid certificate file: {e}"))?;
        if v.get("batch").and_then(Value::as_str) != Some(batch.hex().as_str()) {
            return Err("certificate file belongs to another batch".into());
        }
        for c in v.get("certs").and_then(Value::as_array).ok_or("certificates missing")? {
            let i = c.get("index").and_then(Value::as_u64).ok_or("certificate index missing")? as usize;
            let slot = certs.get_mut(i).ok_or("certificate index outside the batch")?;
            if slot.replace(unhex(&c["cert"], "certificate")?).is_some() {
                return Err("two certificates for one member".into());
            }
        }
    }
    let mut items = Vec::new();
    for (member, cert) in file.members.into_iter().zip(certs) {
        let cert = cert.ok_or("a member has no certificate from its workspace")?;
        items.push(match member {
            FileMember::Publish { wid, package, .. } => {
                let cert = paralean_store::Cert::from_bytes(&cert).map_err(|e| e.to_string())?;
                // T12 checks this again in its transaction; refuse a wrong signer early.
                if cert.body.writer != wid || !store.ring.verify_writer(&wid, &cert.id(), &cert.sig) {
                    return Err("member certificate is not signed by its workspace".into());
                }
                BatchItem::Publish { package: *package, writer: wid, cert }
            }
            FileMember::Tombstone { wid, tombstone, .. } => {
                let cert = TombstoneCert::from_bytes(&cert).map_err(|e| e.to_string())?;
                if cert.body.writer != wid || !store.ring.verify_writer(&wid, &cert.id(), &cert.sig) {
                    return Err("member certificate is not signed by its workspace".into());
                }
                BatchItem::Tombstone { tombstone, writer: wid, cert, grant: None }
            }
        });
    }
    match store.publish_batch(&BatchPackage { intent: file.intent, items }).await {
        Ok(out) => Ok(json!({"outcome": "committed", "batch": batch.hex(), "fresh": out.fresh,
            "members": out.record.entries.iter().map(|e| json!({"object": e.object.hex(), "cert": e.cert.hex()}))
                .collect::<Vec<_>>(), "ms": ms(t)})),
        Err(StoreError::Guard(g)) => Ok(json!({"outcome": "refused", "batch": batch.hex(), "reason": g.to_string()})),
        Err(e @ StoreError::Unresolved { .. }) => Ok(json!({"outcome": "unresolved", "batch": batch.hex(),
            "reason": e.to_string()})),
        Err(e) => Err(e.to_string()),
    }
}

// ---------------------------------------------------------------- batch-status

/// `batch-status --batch BATCH`: the batch record and how many members are visible.
///
/// A read cannot resolve an unknown commit outcome (a lost commit may still land after
/// it); only re-running `batch-publish` can. This is for reporting and tests.
async fn batch_status(args: &[String]) -> R<Value> {
    let (store, _) = open()?;
    let file = read_batch(need(args, "--batch")?)?;
    let batch = file.intent.id();
    let record = store.batch(&batch).await.map_err(|e| e.to_string())?;
    let mut visible = BTreeSet::new();
    for (i, member) in file.members.iter().enumerate() {
        let seen = match member {
            FileMember::Publish { package, .. } => store.marker(&package.group.id()).await.map_err(|e| e.to_string())?.is_some(),
            FileMember::Tombstone { tombstone, .. } => store.tombstone(&tombstone.id()).await.map_err(|e| e.to_string())?.is_some(),
        };
        if seen {
            visible.insert(i);
        }
    }
    Ok(json!({"batch": batch.hex(), "committed": record.is_some(), "members": file.members.len(),
        "visible": visible.len()}))
}
