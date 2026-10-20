//! P5 target-aware publication through P3's signed validator jobs and P2 T1/T4.
//! This stays in P5 while the P3 remote CLI is independently developed.

#[path = "../../../p3-remote/src/cache.rs"]
mod cache;

use std::env;
use std::fs;
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use cache::{id_of, name_of_json, Cache};
use paralean_store::pce::Dec;
use paralean_control::checker::{base_id, CheckerConfig};
use paralean_store::receipt::{self, Policy, TargetBinding};
use paralean_store::{
    AgentId, Anchor, AssignEntry, BuildVerdict, Checkpoint, Controller, Faults, FederationConfig, Id, JobEnvelope, KeyFile, Kind,
    Manifest, Marker, Name, Object, Opaque, Package, Receipt, Revision, Signed, SignedJob,
    Snapshot, Store, StoreConfig, TargetAssignment, TargetCheck, TargetRecord, Verdict, Writer,
};
use paralean_store::id::sha256;
use paralean_store::pce::{Enc, Pce};
use paralean_validator_api::{decode_receipt, published_receipt, validate, ValidatorResponse};
use serde_json::{json, Value};

type R<T> = Result<T, String>;

fn need<'a>(args: &'a [String], flag: &str) -> R<&'a str> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
        .ok_or_else(|| format!("missing {flag}"))
}
fn opt<'a>(args: &'a [String], flag: &str) -> Option<&'a str> {
    args.iter()
        .position(|a| a == flag)
        .and_then(|i| args.get(i + 1))
        .map(String::as_str)
}
fn parse_id(s: &str) -> R<Id> {
    Id::from_hex(s).ok_or("invalid 32-byte ID".into())
}
fn parse_hash(s: &str) -> R<Vec<u8>> {
    let b = hex::decode(s).map_err(|_| "statement hash is not hex")?;
    if b.len() != 32 {
        return Err("statement hash must be 32 bytes".into());
    }
    Ok(b)
}
fn pkg(s: &str) -> R<(Id, Id)> {
    let (g, c) = s.split_once(':').ok_or("--pkg must be GROUP:CAPSULE")?;
    Ok((parse_id(g)?, parse_id(c)?))
}
fn name(args: &[String]) -> R<Name> {
    let n = Name::parse(need(args, "--name")?);
    if n.0.is_empty() {
        return Err("empty target name".into());
    }
    Ok(n)
}
fn open() -> R<(Store, KeyFile)> {
    let path = env::var("PARALEAN_KEYS").map_err(|_| "PARALEAN_KEYS is required")?;
    let kf: KeyFile = serde_json::from_slice(&fs::read(path).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let dep = env::var("PARALEAN_DEPLOYMENT").map_err(|_| "PARALEAN_DEPLOYMENT is required")?;
    let cfg = StoreConfig::from_env(&dep).map_err(|e| e.to_string())?;
    let store = Store::open(&cfg, kf.ring(), Faults::none()).map_err(|e| e.to_string())?;
    Ok((store, kf))
}
fn cache(args: &[String]) -> R<Cache> {
    let c = Cache::new(need(args, "--cache")?);
    c.init().map_err(|e| e.to_string())?;
    Ok(c)
}
fn workspace(
    kf: &KeyFile,
    args: &[String],
) -> R<(paralean_store::WorkspaceId, paralean_store::Signer)> {
    kf.workspace(need(args, "--ws")?)
        .ok_or("workspace is not in the key file".into())
}
fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1000.0
}

pub async fn run(args: &[String]) -> R<Value> {
    match args.first().map(String::as_str) {
        Some("policy-state") => policy_state().await,
        Some("revoke-validator") => revoke_validator(args).await,
        Some("revoke-agent-key") => revoke_agent_key(args).await,
        Some("assign-target") => assign(args).await,
        Some("observe-target") => observe_target(args).await,
        Some("fence-unfinished") => fence_unfinished(args).await,
        Some("validate-target") => validate_target(args).await,
        Some("publish-target") => publish_target(args).await,
        Some("verify-target") => verify_target(args).await,
        Some("checkpoint-targets") => checkpoint_targets(args).await,
        _ => Err("unknown target bridge command".into()),
    }
}

/// Live revocation view for every pinned validator, including validators with
/// no published groups yet. The LSP controller uses this to invalidate cached
/// elaboration before a newly revoked receipt can be reused.
async fn policy_state() -> R<Value> {
    let (store, keys) = open()?;
    let mut validators = Vec::new();
    for key in &keys.ring().validators {
        validators.push(json!({"key": hex::encode(key),
            "revoked": store.meta.is_revoked(key).await.map_err(|e| e.to_string())?}));
    }
    validators.sort_by(|a, b| a["key"].as_str().cmp(&b["key"].as_str()));
    // W3's agent-key registry: an author whose key is revoked or unregistered
    // can no longer publish. Reporting it here changes the policy identity, so
    // editor sessions are invalidated as for a validator revocation.
    let ring = keys.ring();
    let mut agents = Vec::new();
    for (name, entry) in &keys.workspaces {
        let wid = paralean_store::WorkspaceId::from_hex(&entry.id).ok_or("bad workspace ID in key file")?;
        let public: [u8; 32] = hex::decode(&entry.public).ok().and_then(|p| p.try_into().ok())
            .ok_or("bad workspace public key in key file")?;
        let (registered, revoked) = store.meta.agent_key_state(&ring, AgentId(wid.0), wid, public)
            .await.map_err(|e| e.to_string())?;
        agents.push(json!({"workspace": name, "id": wid.hex(), "public": entry.public,
            "registered": registered, "revoked": revoked}));
    }
    Ok(json!({"validators": validators, "agents": agents, "policies": keys.policies,
              "checkers": keys.checkers}))
}

/// Refuse before validator work when `wid`'s author key cannot publish. T1
/// remains the authoritative check inside the publication transaction.
async fn require_authoring(store: &Store, kf: &KeyFile, wid: paralean_store::WorkspaceId) -> R<()> {
    let entry = kf.workspaces.values().find(|e| e.id == wid.hex()).ok_or("workspace is not in the key file")?;
    let public: [u8; 32] = hex::decode(&entry.public).ok().and_then(|p| p.try_into().ok())
        .ok_or("bad workspace public key in key file")?;
    let (registered, revoked) = store.meta.agent_key_state(&kf.ring(), AgentId(wid.0), wid, public)
        .await.map_err(|e| e.to_string())?;
    if registered && !revoked { return Ok(()) }
    Err(format!("workspace agent key is {}", if revoked { "revoked" } else { "not registered" }))
}

/// Authority-only maintenance operation, used by the isolated editor policy
/// gate. Workspace keys cannot issue this signed revocation.
async fn revoke_validator(args: &[String]) -> R<Value> {
    let (store, keys) = open()?;
    let signer = keys.authority_signer().ok_or("authority seed required for revocation")?;
    let raw = hex::decode(need(args, "--key")?).map_err(|_| "invalid validator key")?;
    let key: [u8; 32] = raw.try_into().map_err(|_| "validator key must be 32 bytes")?;
    if !keys.ring().validators.contains(&key) {
        return Err("validator key is not pinned by this deployment".into());
    }
    let reason = need(args, "--reason")?;
    if reason.is_empty() || reason.len() > 256 {
        return Err("revocation reason must be 1..256 bytes".into());
    }
    let signed = receipt::SignedRevocation::sign(
        receipt::Revocation { key, reason: reason.to_owned() }, &signer);
    let fresh = store.meta.revoke_validator(&signed).await.map_err(|e| e.to_string())?;
    Ok(json!({"key": hex::encode(key), "revoked": true, "fresh": fresh}))
}

/// Authority-only: revoke a workspace's author key in W3's registry. Existing
/// publications stay; new admissions by that key are refused by T1/T8.
async fn revoke_agent_key(args: &[String]) -> R<Value> {
    let (store, keys) = open()?;
    let signer = keys.authority_signer().ok_or("authority seed required for agent-key revocation")?;
    let name = need(args, "--ws")?;
    let entry = keys.workspaces.get(name).ok_or("workspace is not in the key file")?;
    let public: [u8; 32] = hex::decode(&entry.public).ok().and_then(|p| p.try_into().ok())
        .ok_or("bad workspace public key in key file")?;
    let fresh = Controller::new(store, signer).revoke_agent_key(public).await.map_err(|e| e.to_string())?;
    Ok(json!({"workspace": name, "public": entry.public, "revoked": true, "fresh": fresh}))
}

/// A P5 checkpoint is selected from exact live revision IDs by the exporter. The
/// bridge rechecks each frozen target against its signed publication and current
/// target head before constructing the immutable P2 snapshot.
async fn checkpoint_targets(args: &[String]) -> R<Value> {
    let (store, kf) = open()?;
    let (wid, signer) = workspace(&kf, args)?;
    let authority = kf.authority_signer().ok_or("authority seed required for checkpoint")?;
    let spec: Value = serde_json::from_slice(&fs::read(need(args, "--spec")?).map_err(|e| e.to_string())?)
        .map_err(|e| format!("invalid checkpoint spec: {e}"))?;
    let raw_revisions = spec.get("revisions").and_then(Value::as_array).ok_or("spec.revisions must be an array")?;
    let mut contents = raw_revisions.iter().map(|v| parse_id(v.as_str().ok_or("revision must be hex")?)).collect::<R<Vec<_>>>()?;
    if contents.is_empty() { return Err("checkpoint needs revisions".into()); }
    contents.sort(); contents.dedup();
    if contents.len() != raw_revisions.len() { return Err("duplicate checkpoint revision".into()); }
    let mut revision_map = BTreeMap::new();
    for rid in &contents {
        let rev = store.revision(rid).await.map_err(|e| e.to_string())?.ok_or("checkpoint revision absent")?;
        revision_map.insert(*rid, rev);
    }
    let files_json = spec.get("files").and_then(Value::as_object).ok_or("spec.files must be an object")?;
    let mut files = Vec::new();
    let mut projected = BTreeSet::new();
    for (path, ids) in files_json {
        if path.is_empty() || path.starts_with('/') || path.split('/').any(|s| s == "..") || !path.ends_with(".lean") {
            return Err("invalid checkpoint source path".into());
        }
        let ids = ids.as_array().ok_or("file revisions must be an array")?
            .iter().map(|v| parse_id(v.as_str().ok_or("file revision must be hex")?)).collect::<R<Vec<_>>>()?;
        for rid in &ids {
            if !revision_map.contains_key(rid) { return Err("file names revision outside snapshot".into()); }
            if !projected.insert(*rid) { return Err("revision appears in multiple file positions".into()); }
        }
        files.push((path.clone(), ids));
    }
    if projected != contents.iter().copied().collect() { return Err("source layout does not cover snapshot contents exactly".into()); }
    let targets_json = spec.get("targets").and_then(Value::as_array).ok_or("spec.targets must be an array")?;
    if targets_json.is_empty() { return Err("checkpoint needs required targets".into()); }
    let mut assignments = Vec::new();
    let mut checks = Vec::new();
    let mut completion = Vec::new();
    let mut seen = BTreeSet::new();
    for item in targets_json {
        let n = Name::parse(item.get("name").and_then(Value::as_str).ok_or("target name missing")?);
        if n.0.is_empty() || !seen.insert(n.to_string()) { return Err("empty or duplicate target name".into()); }
        let statement = parse_hash(item.get("statement_hash").and_then(Value::as_str).ok_or("target statement_hash missing")?)?;
        let group = parse_id(item.get("group").and_then(Value::as_str).ok_or("target group missing")?)?;
        let (receipt, job) = published_receipt(&store, &group).await.map_err(|e| format!("target receipt: {e:?}"))?;
        if job.body.targets.len() != 1 { return Err("target job must bind exactly one target".into()); }
        let binding = &job.body.targets[0];
        if binding.name != n || binding.statement != statement || receipt.body.verdict != Verdict::Accepted {
            return Err("published receipt does not bind frozen target statement".into());
        }
        let record = store.target(&n).await.map_err(|e| e.to_string())?.ok_or("target record absent")?;
        let assignment = store.meta.get(store.meta.keys.assign(&n, record.epoch)).await
            .map_err(|e| e.to_string())?.ok_or("target assignment log absent")?;
        let assignment = AssignEntry::from_pce(&assignment).map_err(|e| e.to_string())?;
        if assignment.owner != record.owner || assignment.request != record.last_request {
            return Err("target assignment log differs from current record".into());
        }
        if binding.epoch != record.epoch || job.body.worker != record.owner {
            return Err("target assignment changed after validation".into());
        }
        let head = record.head.ok_or("target has no published head")?;
        let revision = revision_map.get(&head).ok_or("target head missing from checkpoint contents")?;
        if revision.group != group || revision.name != n { return Err("checkpoint does not select current target head".into()); }
        // The target record and its T4 assignment log are the authoritative source.
        // Snapshot's assignment signature is a domain-separated authority signature
        // over exactly the record's name, owner and epoch.
        let mut msg = Enc::new();
        n.encode(&mut msg); record.owner.encode(&mut msg); msg.uvarint(record.epoch);
        let assignment_id = Id(sha256(&[b"paralean-p5-target-assignment\0".as_slice(), &msg.out].concat()));
        assignments.push(TargetAssignment {
            name: n.clone(), owner: record.owner, epoch: record.epoch,
            assigned_by: authority.public().to_vec(), signature: authority.sign(&assignment_id).to_vec(),
        });
        checks.push(TargetCheck {
            target: receipt.body.target.clone().ok_or("target receipt missing target slot")?,
            group, statement_matches: true, axioms: receipt.body.axioms.clone(),
        });
        completion.push(json!({"name": n.to_string(), "owner": record.owner.hex(), "epoch": record.epoch,
            "head": head.hex(), "group": group.hex(), "statement_hash": hex::encode(&statement)}));
    }
    assignments.sort_by_key(Pce::to_pce);
    checks.sort_by(|a,b| a.target.cmp(&b.target));
    let source_root = Manifest::SourceRoot { files };
    let build = spec.get("build");
    let build_receipt = Manifest::BuildReceipt {
        exporter_bin: build.and_then(|v| v.get("exporter_bin")).and_then(Value::as_str).unwrap_or("paralean-p1-export").as_bytes().to_vec(),
        lean_commit: build.and_then(|v| v.get("lean_commit")).and_then(Value::as_str).unwrap_or("").into(),
        mathlib_commit: build.and_then(|v| v.get("mathlib_commit")).and_then(Value::as_str).unwrap_or("").into(),
        layout: source_root.id(),
        build_log_hash: match build.and_then(|v| v.get("build_log_hash")).and_then(Value::as_str) {
            Some(s) => parse_hash(s)?, None => vec![],
        },
        target_checks: checks,
        verdict: BuildVerdict::Ok,
    };
    let writer = Writer::new(store.clone(), wid, signer);
    let ctl = Controller::new(store.clone(), authority);
    let token = ctl.rotate(wid, &rand::random::<[u8; 16]>()).await.map_err(|e| e.to_string())?;
    let predecessor = opt(args, "--predecessor").map(parse_id).transpose()?;
    let snapshot = Snapshot {
        workspace: wid, base: base_id(&CheckerConfig::from_env()?.lean_githash), contents,
        predecessors: vec![], targets: assignments, source_root: source_root.id(), build_receipt: build_receipt.id(),
    };
    let snapshot_id = snapshot.id();
    let cp = Checkpoint { snapshot, source_root, build_receipt, predecessor, token };
    let catalog = writer.commit_checkpoint(&cp).await.map_err(|e| e.to_string())?;
    let stored_snapshot = store.s3.get_object::<Snapshot>(Kind::Snapshot, &snapshot_id)
        .await.map_err(|e| e.to_string())?.ok_or("committed snapshot missing")?;
    let stored_receipt = store.s3.get_object::<Manifest>(Kind::Manifest, &stored_snapshot.build_receipt)
        .await.map_err(|e| e.to_string())?.ok_or("committed build receipt missing")?;
    let stored_checks = match stored_receipt {
        Manifest::BuildReceipt { target_checks, verdict: BuildVerdict::Ok, .. } => target_checks,
        _ => return Err("committed build receipt invalid".into()),
    };
    if stored_snapshot.targets.len() != completion.len() || stored_checks.len() != completion.len() {
        return Err("committed checkpoint omitted target attestations".into());
    }
    // This post-check narrows the race before the P5 completion journal's atomic
    // target guard. The journal guard is the durable completion linearization point.
    for t in &completion {
        let n = Name::parse(t["name"].as_str().unwrap());
        let rec = store.target(&n).await.map_err(|e| e.to_string())?.ok_or("target record disappeared")?;
        if rec.epoch != t["epoch"].as_u64().unwrap() || rec.head.map(|h| h.hex()) != t["head"].as_str().map(str::to_owned) {
            return Err("target changed during checkpoint; completion must retry".into());
        }
    }
    Ok(json!({"catalog": catalog.hex(), "snapshot": snapshot_id.hex(), "rank": cp.token.rank,
        "snapshot_targets": stored_snapshot.targets.iter().map(|t| json!({
            "name": t.name.to_string(), "owner": t.owner.hex(), "epoch": t.epoch,
            "assigned_by": hex::encode(&t.assigned_by), "signature": hex::encode(&t.signature)
        })).collect::<Vec<_>>(),
        "build_receipt_target_checks": stored_checks.iter().map(|t| json!({
            "target": hex::encode(&t.target), "group": t.group.hex(),
            "statement_matches": t.statement_matches,
            "axioms": t.axioms.iter().map(ToString::to_string).collect::<Vec<_>>()
        })).collect::<Vec<_>>(),
        "completion_targets": completion }))
}

async fn assign(args: &[String]) -> R<Value> {
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, _) = workspace(&kf, args)?;
    let signer = kf
        .authority_signer()
        .ok_or("authority seed is required for target assignment")?;
    let request = need(args, "--request")?.as_bytes();
    if request.is_empty() {
        return Err("empty assignment request".into());
    }
    paralean_control::durable::claim_for_task(&store, &n).await?;
    let ctl = Controller::new(store, signer);
    let epoch = ctl
        .reassign(&n, wid, request)
        .await
        .map_err(|e| e.to_string())?;
    Ok(json!({"name": n.to_string(), "owner": wid.hex(), "epoch": epoch}))
}

fn target_json(n: &Name, rec: &TargetRecord, wid: paralean_store::WorkspaceId) -> Value {
    json!({"name": n.to_string(), "owner": rec.owner.hex(), "epoch": rec.epoch,
        "head": rec.head.map(|h| h.hex()), "assigned_to_agent": rec.owner == wid})
}

async fn observe_target(args: &[String]) -> R<Value> {
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, _) = workspace(&kf, args)?;
    let rec = store.target(&n).await.map_err(|e| e.to_string())?
        .ok_or("target record absent")?;
    Ok(target_json(&n, &rec, wid))
}

/// T4-compatible assignment fenced by the target record read at dispatch.
///
/// `areq` is checked first and the request ID must be reused after an unknown
/// commit result. The target read and all three T4 writes share one FDB
/// transaction with T1's target-head update; exactly one side can win.
async fn fence_unfinished(args: &[String]) -> R<Value> {
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, _) = workspace(&kf, args)?;
    kf.authority_signer().ok_or("authority seed required for target fence")?;
    let expected_epoch: u64 = need(args, "--expected-epoch")?.parse()
        .map_err(|_| "invalid expected target epoch")?;
    let expected_head = match need(args, "--expected-head")? {
        "none" => None,
        hex => Some(parse_id(hex)?),
    };
    let request = need(args, "--request")?.as_bytes().to_vec();
    if request.is_empty() || request.len() > 128 {
        return Err("fence request must be 1..128 bytes".into());
    }
    let keys = &store.meta.keys;
    let request_key = keys.assign_request(&n, &request);
    let target_key = keys.target(&n);
    let claim_key = paralean_control::durable::target_claim_key(&store, &n);
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        // The fence is a T4 write: it shares the claim rule with `assign`, read
        // in this transaction so a concurrent shard claim conflicts with it.
        paralean_control::durable::claim_in(&trx, &claim_key, &n).await?;
        // Mirror P2 T4's federation-home guard in this same transaction.
        // Reading the pinned config here also conflicts with a concurrent
        // federation pin; a foreign home can never be fenced locally.
        if let Some(raw) = trx.get(&keys.ae_config(), false).await.map_err(|e| e.to_string())? {
            let cfg = FederationConfig::from_pce(&raw).map_err(|e| e.to_string())?;
            if cfg.target_homes.get(&n).map(String::as_str) != Some(cfg.deployment.as_str()) {
                return Err(format!("target {n} is assigned to a foreign federation home"));
            }
        }
        // This index is the durable outcome witness if the previous commit
        // succeeded but its reply was lost. Decode exactly P2's PCE uvarint.
        if let Some(raw) = trx.get(&request_key, false).await.map_err(|e| e.to_string())? {
            let mut decoder = Dec::new(&raw);
            let request_epoch = decoder.uvarint().map_err(|e| e.to_string())?;
            decoder.end().map_err(|e| e.to_string())?;
            let assignment = trx.get(&keys.assign(&n, request_epoch), false).await
                .map_err(|e| e.to_string())?.ok_or("fence request has no assignment log")?;
            let assignment = AssignEntry::from_pce(&assignment).map_err(|e| e.to_string())?;
            if assignment.owner != wid || assignment.request != request {
                return Err("fence request index differs from assignment log".into());
            }
            let raw = trx.get(&target_key, false).await.map_err(|e| e.to_string())?
                .ok_or("target record disappeared after fence")?;
            let rec = TargetRecord::from_pce(&raw).map_err(|e| e.to_string())?;
            let outcome = if rec.epoch == request_epoch && rec.owner == wid && rec.last_request == request {
                "fenced"
            } else { "changed" };
            return Ok(json!({"outcome": outcome, "request_epoch": request_epoch,
                "name": n.to_string(), "owner": rec.owner.hex(), "epoch": rec.epoch,
                "head": rec.head.map(|h| h.hex())}));
        }
        let raw = trx.get(&target_key, false).await.map_err(|e| e.to_string())?
            .ok_or("target record absent")?;
        let rec = TargetRecord::from_pce(&raw).map_err(|e| e.to_string())?;
        if rec.owner != wid || rec.epoch != expected_epoch || rec.head != expected_head {
            return Ok(json!({"outcome": "changed", "name": n.to_string(),
                "owner": rec.owner.hex(), "epoch": rec.epoch,
                "head": rec.head.map(|h| h.hex())}));
        }
        let next = rec.epoch.checked_add(1).ok_or("target epoch overflow")?;
        let updated = TargetRecord { name: n.clone(), owner: wid, epoch: next,
            head: rec.head, last_request: request.clone() };
        trx.set(&target_key, &updated.to_pce());
        trx.set(&keys.assign(&n, next), &AssignEntry { owner: wid, request: request.clone() }.to_pce());
        let mut encoded = Enc::new();
        encoded.uvarint(next);
        trx.set(&request_key, &encoded.out);
        match trx.commit().await {
            Ok(_) => return Ok(json!({"outcome": "fenced", "request_epoch": next,
                "name": n.to_string(), "owner": wid.hex(), "epoch": next,
                "head": rec.head.map(|h| h.hex())})),
            Err(error) => { trx = error.on_error().await.map_err(|e| e.to_string())?; }
        }
    }
    Err("target fence outcome unresolved after 60 retries; reuse the same request".into())
}

async fn validate_target(args: &[String]) -> R<Value> {
    let t = Instant::now();
    let c = cache(args)?;
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, signer) = workspace(&kf, args)?;
    require_authoring(&store, &kf, wid).await?;
    let writer = Writer::new(store.clone(), wid, signer);
    let prepared = writer.prepare_target(&n).await.map_err(|e| e.to_string())?;
    let expected_epoch: u64 = need(args, "--epoch")?
        .parse()
        .map_err(|_| "invalid --epoch")?;
    if prepared.epoch != expected_epoch {
        return Err("target epoch changed after controller dispatch".into());
    }
    let statement = parse_hash(need(args, "--statement-hash")?)?;
    let (group, capsule) = pkg(need(args, "--pkg")?)?;
    let deps = opt(args, "--deps")
        .unwrap_or("")
        .split(',')
        .filter(|s| !s.is_empty())
        .map(parse_id)
        .collect::<R<Vec<_>>>()?;
    let checker = CheckerConfig::from_env()?;
    let pinned = kf.checkers.first().ok_or("no checker pin")?;
    let checker_id = parse_id(pinned)?;
    if checker.version()?.id() != checker_id {
        return Err("configured checker differs from key pin".into());
    }
    let authority = kf
        .authority_signer()
        .ok_or("authority seed required for target job")?;
    let job = Signed::sign(
        JobEnvelope {
            request: rand::random::<[u8; 16]>().to_vec(),
            group,
            capsule,
            deps,
            base: base_id(&checker.lean_githash),
            policy: Policy::v1().id(),
            checker: checker_id,
            worker: wid,
            targets: vec![TargetBinding {
                name: n.clone(),
                epoch: prepared.epoch,
                statement: statement.clone(),
            }],
            deadline_ms: 1_800_000,
            memory_mb: 0,
        },
        &authority,
    );
    let job: SignedJob = store
        .meta
        .issue_job(&job)
        .await
        .map_err(|e| e.to_string())?;
    let addr = need(args, "--validator")?;
    let response = validate(
        addr,
        &job,
        &authority,
        &store.ring.validators,
        Duration::from_secs(1800),
    )
        .await
        .map_err(|e| e.to_string())?;
    let receipt = match response {
        ValidatorResponse::Receipt { receipt } => decode_receipt(&receipt)?,
        other => return Err(format!("validator gave no receipt: {other:?}")),
    };
    let (accepted, reason) = match &receipt.body.verdict {
        Verdict::Accepted => (true, String::new()),
        Verdict::Rejected(reason) => (false, reason.clone()),
    };
    if accepted {
        receipt::check(&receipt, &job, &group, &[prepared], &store.ring)
            .map_err(|e| e.to_string())?;
    }
    c.write_new(&c.receipt(&receipt.id()), &receipt.to_bytes())
        .map_err(|e| e.to_string())?;
    c.write_new(&c.job(&job.id()), &job.to_bytes())
        .map_err(|e| e.to_string())?;
    c.log_transfer("validate-target", &group, 0, ms(t));
    Ok(
        json!({"accepted": accepted, "reason": reason, "group": group.hex(), "capsule": capsule.hex(),
        "name": n.to_string(), "epoch": job.body.targets[0].epoch,
        "statement_hash": hex::encode(statement), "receipt": receipt.id().hex(),
        "job": job.id().hex(), "ms": ms(t)}),
    )
}

async fn publish_target(args: &[String]) -> R<Value> {
    let t = Instant::now();
    let c = cache(args)?;
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, signer) = workspace(&kf, args)?;
    let writer = Writer::new(store, wid, signer);
    let prepared = writer.prepare_target(&n).await.map_err(|e| e.to_string())?;
    let expected_epoch: u64 = need(args, "--epoch")?
        .parse()
        .map_err(|_| "invalid --epoch")?;
    if prepared.epoch != expected_epoch {
        return Err("target epoch changed before publication".into());
    }
    let plan: Value =
        serde_json::from_slice(&fs::read(need(args, "--plan")?).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    let entries = plan.as_array().ok_or("plan must be an array")?;
    if entries.len() != 1 {
        return Err("target plan must contain exactly one group".into());
    }
    let e = &entries[0];
    let g = id_of(&e["group"])?;
    let cap = id_of(&e["capsule"])?;
    let rid = id_of(&e["receipt"])?;
    let jid = id_of(&e["job"])?;
    let receipt = Receipt::from_bytes(&fs::read(c.receipt(&rid)).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let job = SignedJob::from_bytes(&fs::read(c.job(&jid)).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let gbytes = fs::read(c.object(&g)).map_err(|e| e.to_string())?;
    let cbytes = fs::read(c.capsule(&cap)).map_err(|e| e.to_string())?;
    let mut revisions = Vec::new();
    for r in e["revisions"].as_array().ok_or("plan revisions missing")? {
        let mut parents = r["parents"]
            .as_array()
            .ok_or("revision parents missing")?
            .iter()
            .map(id_of)
            .collect::<R<Vec<_>>>()?;
        parents.sort();
        parents.dedup();
        revisions.push(Revision {
            group: g,
            name: name_of_json(&r["name"])?,
            parents,
            capsule: cap,
            workspace: wid,
        });
    }
    if !revisions.iter().any(|r| r.name == n) {
        return Err("plan has no revision of the target".into());
    }
    let mut rids: Vec<Id> = revisions.iter().map(|r| r.id()).collect();
    rids.sort();
    let agent = |v: &Value| -> R<AgentId> {
        AgentId::from_hex(v.as_str().ok_or("bad author")?).ok_or("bad author ID".into())
    };
    let marker = Marker {
        group: g,
        revisions: rids.clone(),
        receipt: receipt.id(),
        file_path: e["file"].as_str().ok_or("plan file missing")?.to_string(),
        anchor: if e["anchor"].is_null() {
            Anchor::FileStart
        } else {
            Anchor::After(id_of(&e["anchor"])?)
        },
        lamport: e["lamport"].as_u64().ok_or("plan Lamport clock missing")?,
        author: agent(&e["author"])?,
        root_path: e["rootPath"]
            .as_array()
            .ok_or("rootPath missing")?
            .iter()
            .map(|x| {
                Ok((
                    id_of(&x[0])?,
                    x[1].as_u64().ok_or("Lamport time")?,
                    agent(&x[2])?,
                ))
            })
            .collect::<R<_>>()?,
        lineage_keys: e["lineageKeys"]
            .as_array()
            .ok_or("lineageKeys missing")?
            .iter()
            .map(|x| {
                Ok((
                    name_of_json(&x[0])?,
                    x[1].as_u64().ok_or("Lamport time")?,
                    agent(&x[2])?,
                ))
            })
            .collect::<R<_>>()?,
    };
    if marker.author.0 != wid.0 {
        return Err("record author differs from target owner".into());
    }
    if job.body.capsule != cap {
        return Err("job capsule differs from plan".into());
    }
    if job.body.targets.len() != 1 || job.body.targets[0].name != n {
        return Err("job is not bound to exactly this target".into());
    }
    let package = Package {
        group: Opaque::new(Kind::Group, gbytes),
        chunks: vec![],
        capsule: Opaque::new(Kind::Capsule, cbytes),
        receipt,
        job,
        revisions,
        marker,
        targets: vec![prepared],
    };
    let outcome = writer.publish(&package).await.map_err(|e| e.to_string())?;
    Ok(
        json!({"group": g.hex(), "marker": outcome.marker.hex(), "fresh": outcome.fresh,
        "revisions": rids.iter().map(Id::hex).collect::<Vec<_>>(), "ms": ms(t)}),
    )
}

async fn verify_target(args: &[String]) -> R<Value> {
    let (store, _) = open()?;
    let n = name(args)?;
    let statement = parse_hash(need(args, "--statement-hash")?)?;
    let group = parse_id(need(args, "--group")?)?;
    let (receipt, job) = published_receipt(&store, &group)
        .await
        .map_err(|e| format!("receipt: {e:?}"))?;
    if receipt.body.verdict != Verdict::Accepted {
        return Err("target receipt rejected".into());
    }
    if job.body.targets.len() != 1 {
        return Err("published job must bind exactly one target".into());
    }
    let binding = &job.body.targets[0];
    if binding.name != n || binding.statement != statement {
        return Err("published job does not bind frozen target contract".into());
    }
    let record = store
        .target(&n)
        .await
        .map_err(|e| e.to_string())?
        .ok_or("target record absent")?;
    if binding.epoch != record.epoch || job.body.worker != record.owner {
        return Err("signed target job is stale for current owner or epoch".into());
    }
    let head = record.head.ok_or("target has no published head")?;
    let revision = store
        .revision(&head)
        .await
        .map_err(|e| e.to_string())?
        .ok_or("target head revision absent")?;
    if revision.group != group || revision.name != n {
        return Err("group is not the current published target head".into());
    }
    Ok(
        json!({"ok": true, "group": group.hex(), "name": n.to_string(),
        "epoch": record.epoch, "owner": record.owner.hex(),
        "statement_hash": hex::encode(statement),
        "head": head.hex()}),
    )
}
