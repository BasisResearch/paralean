//! plr: the P3 bridge between a working copy's local cache and the P2 store.
//!
//! Configuration comes from the environment, as for `paralean-p2`: `PARALEAN_FDB_CLUSTER`,
//! `PARALEAN_S3_*`, `PARALEAN_DEPLOYMENT` and `PARALEAN_KEYS` (a key file from `keys-init`).
//! Each command prints one JSON value on stdout.
//!
//! Atomic batches (docs/atomic-pub-log.md): a coordinator signs a target-free intent with
//! its job-issuer key (`batch-intent`), validates the members bound to it in order
//! (`batch-validate`), each participant signs its own members' certificates
//! (`batch-sign`), and the coordinator publishes them in one T12 (`publish-batch`). The
//! description lives in the coordinator's cache, owner-only. A participant that captures
//! against a member before the batch exists sees it through `batch-share`: the member's
//! records under a staging ID, with a receipt bound to that ID, which no transaction
//! publishes.

mod cache;
mod receipt;

use std::collections::{BTreeMap, BTreeSet};
use std::process::ExitCode;
use std::time::Instant;

use cache::*;
use paralean_store::recovery::{discover, recover_catalog};
use paralean_store::*;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use paralean_store::receipt::SignedJob;
use paralean_control::controller::{call_controller, ControlRequest, ControlResponse, TargetReq};
use std::time::Duration;
use serde_json::{json, Value};

const USAGE: &str = "usage: plr <command> [args]
  keys-init KEYFILE TRUST ROGUEKEYS --agents a,b,..   keys, pins (policy v1, this checker), trust file for Lean
  stage --cache C --pkg GROUP:CAPSULE ...          upload payload and capsule (staged, unpublished)
  validate --cache C --ws W --validator ADDR --pkg GROUP:CAPSULE --deps C1,C2,..
                                                   issue a job envelope, get the validator's receipt
           [--controller ADDR --targets NAME[:STATEMENT],...]
                                                   controller-issued target job; owner/epoch/head snapshot
           [--bind STAGING]                        the job bound to a staging ID: never published
  publish --cache C --ws W --plan FILE            T1 for each planned record, in order
  batch-share --cache C --to C2 --staging S --pkg GROUP:CAPSULE --receipt R
                                                   a validated, unpublished member's records into C2/p3/staged/S
  batch-intent --cache C --ws W --staging S --member publish:GROUP:CAPSULE:WRITER:DEP,.. |
               tombstone:TARGET:POSITION:LAMPORT:WRITER:FILE ...
                                                   sign a target-free intent (job-issuer key); description
                                                   C/p3/batches/S.json, owner-only
  batch-validate --cache C --ws W --batch FILE --validator ADDR
                                                   members' jobs bound to the intent, validated in order
  batch-sign --cache C --ws W --batch FILE [--plan PLAN]
                                                   W's certificates for its own members
  publish-batch --cache C --batch FILE             T12: every member or none
  target-get --name NAME                           inspect the owner, epoch and published head
  tombstone --cache C --ws W --file F --target G --position MARKER --lamport L [--controller]
  move --cache C --ws W --file F --target G --position MARKER --lamport L [--anchor GROUP]
  pull --cache C [--only G,..] [--seed S --max N] [--save FILE] [--replay FILE]
  fetch-group --cache C GROUP                      payload on demand (remote%)
  fetch-pkg --cache C GROUP                        a published group's records on demand
  checkpoint --cache C --ws W --revisions R,.. [--predecessor CAT] [--build-ok 0|1] [--files JSON]
  snapshot-get --cache C --ws W [--catalog CAT]   recover a committed snapshot into an empty cache
  forge --cache C --keys KEYFILE --ws W --pkg G:C [--deps ..] [--bind STAGING]
                                                   test only: a job and an accepted receipt signed with KEYFILE's keys
  check-receipt GROUP                              P3 control's consumer check of a published group
  check-receipt --cache C --staged S --receipt R GROUP
                                                   the same for a staged batch member (batch-share)";

type R<T> = std::result::Result<T, String>;

fn es<E: std::fmt::Display>(e: E) -> String {
    e.to_string()
}

fn keyfile() -> R<KeyFile> {
    let p = std::env::var("PARALEAN_KEYS").map_err(|_| "PARALEAN_KEYS is not set")?;
    serde_json::from_str(&std::fs::read_to_string(&p).map_err(|e| format!("{p}: {e}"))?).map_err(es)
}

fn open() -> R<(Store, KeyFile)> {
    let dep = std::env::var("PARALEAN_DEPLOYMENT").unwrap_or_else(|_| "default".into());
    let cfg = StoreConfig::from_env(&dep).map_err(es)?;
    let kf = keyfile()?;
    let store = Store::open(&cfg, kf.ring(), Faults::none()).map_err(es)?;
    Ok((store, kf))
}

fn flag<'a>(a: &'a [&'a str], k: &str) -> Option<&'a str> {
    a.iter().position(|x| *x == k).and_then(|i| a.get(i + 1)).copied()
}
fn flags<'a>(a: &'a [&'a str], k: &str) -> Vec<&'a str> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < a.len() {
        if a[i] == k {
            let mut j = i + 1;
            while j < a.len() && !a[j].starts_with("--") {
                out.push(a[j]);
                j += 1;
            }
            i = j;
        } else {
            i += 1;
        }
    }
    out
}
fn need<'a>(a: &'a [&'a str], k: &str) -> R<&'a str> {
    flag(a, k).ok_or(format!("missing {k}"))
}

fn pkg_arg(s: &str) -> R<(Id, Id)> {
    let (g, c) = s.split_once(':').ok_or(format!("bad --pkg {s}"))?;
    Ok((Id::from_hex(g).ok_or("bad group")?, Id::from_hex(c).ok_or("bad capsule")?))
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1000.0
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    match paralean_store::meta::run_main(run(&a)) {
        Ok(v) => {
            println!("{v}");
            ExitCode::SUCCESS
        }
        Err(e) => {
            println!("{}", json!({"error": e}));
            eprintln!("plr: {e}");
            ExitCode::from(2)
        }
    }
}

async fn run(a: &[&str]) -> R<Value> {
    match a.first().copied() {
        Some("keys-init") => keys_init(&a[1..]),
        Some("stage") => stage(&a[1..]).await,
        Some("validate") => validate(&a[1..]).await,
        Some("publish") => publish(&a[1..]).await,
        Some("batch-share") => batch_share(&a[1..]).await,
        Some("batch-intent") => batch_intent(&a[1..]).await,
        Some("batch-validate") => batch_validate(&a[1..]).await,
        Some("batch-sign") => batch_sign(&a[1..]).await,
        Some("publish-batch") => publish_batch(&a[1..]).await,
        Some("target-get") => target_get(&a[1..]).await,
        Some("tombstone") => tombstone(&a[1..]).await,
        Some("move") => move_position(&a[1..]).await,
        Some("pull") => pull(&a[1..]).await,
        Some("fetch-group") => fetch_group(&a[1..]).await,
        Some("fetch-pkg") => fetch_pkg_cmd(&a[1..]).await,
        Some("checkpoint") => checkpoint(&a[1..]).await,
        Some("snapshot-get") => snapshot_get(&a[1..]).await,
        Some("forge") => forge(&a[1..]),
        Some("check-receipt") => check_receipt(&a[1..]).await,
        _ => Err(USAGE.into()),
    }
}

// ---------------------------------------------------------------- keys and trust

fn keys_init(a: &[&str]) -> R<Value> {
    let (kpath, tpath, rpath) = (a.first().ok_or(USAGE)?, a.get(1).ok_or(USAGE)?, a.get(2).ok_or(USAGE)?);
    let agents: Vec<&str> = need(a, "--agents")?.split(',').filter(|s| !s.is_empty()).collect();
    let mut kf = KeyFile::default();
    let auth = Signer::generate();
    kf.authority = Some(hex::encode(auth.seed()));
    kf.authority_public = hex::encode(auth.public());
    let val = Signer::generate();
    kf.add_validator("v0", &val);
    for n in &agents {
        let s = Signer::generate();
        kf.workspaces.insert(n.to_string(), sign::KeyEntry { id: WorkspaceId::random().hex(), public: hex::encode(s.public()), seed: Some(hex::encode(s.seed())) });
        kf.add_job_issuer(n, &Signer::generate());
    }
    kf.register_workspace_agents();
    let checker = receipt::checker()?;
    kf.policies = vec![paralean_store::receipt::Policy::v1().id().hex()];
    kf.checkers = vec![checker.id().hex()];
    kf.write_private(kpath).map_err(es)?;
    // Each working copy's own key file: its workspace and job-issuer seeds only; every other
    // entry public (no authority, validator or other agents' seeds).
    let dir = std::path::Path::new(kpath).parent().unwrap_or(std::path::Path::new("."));
    for n in &agents {
        let mut own = kf.clone();
        own.authority = None;
        for e in own.validators.values_mut() {
            e.seed = None;
        }
        for (k, e) in own.workspaces.iter_mut().chain(own.job_issuers.iter_mut()) {
            if k != n {
                e.seed = None;
            }
        }
        own.write_private(dir.join(format!("keys-{n}.json"))).map_err(es)?;
    }
    // An untrusted validator and controller, for the forgery tests: same agents, other keys.
    let mut rogue = kf.clone();
    let rv = Signer::generate();
    rogue.validators.clear();
    rogue.add_validator("v0", &rv);
    let ra = Signer::generate();
    rogue.authority = Some(hex::encode(ra.seed()));
    rogue.authority_public = hex::encode(ra.public());
    std::fs::write(rpath, serde_json::to_string_pretty(&rogue).unwrap()).map_err(es)?;
    let tv = json!({
        "validators": [hex::encode(val.public())],
        "authority": kf.authority_public,
        "jobIssuers": kf.job_issuers.iter().map(|(n, e)| json!([n, e.public])).collect::<Vec<_>>(),
        "policies": kf.policies,
        "checkers": kf.checkers,
        "base": receipt::base()?.hex(),
        "allowedAxioms": paralean_store::receipt::ALLOWED_AXIOMS,
        "agents": agents.iter().map(|n| json!([n, kf.workspaces[*n].id])).collect::<Vec<_>>(),
    });
    std::fs::write(tpath, serde_json::to_string_pretty(&tv).unwrap()).map_err(es)?;
    Ok(tv)
}

// ---------------------------------------------------------------- staging and validation

async fn stage(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, _) = open()?;
    let mut out = Vec::new();
    for p in flags(a, "--pkg") {
        let (group, capsule) = pkg_arg(p)?;
        let t = Instant::now();
        let g = std::fs::read(c.object(&group)).map_err(|e| format!("payload {}: {e}", group))?;
        let cb = std::fs::read(c.capsule(&capsule)).map_err(|e| format!("capsule {}: {e}", capsule))?;
        let ga = st.s3.put_opaque(&Opaque::new(Kind::Group, g.clone())).await.map_err(es)?;
        let ca = st.s3.put_opaque(&Opaque::new(Kind::Capsule, cb.clone())).await.map_err(es)?;
        if ga.id() != group || ca.id() != capsule {
            return Err(format!("staged IDs differ from the local ones for {p}"));
        }
        c.log_transfer("put-group", &group, g.len(), 0.0);
        c.log_transfer("put-capsule", &capsule, cb.len(), ms(t));
        out.push(json!({"group": group.hex(), "capsule": capsule.hex(), "groupBytes": g.len(), "capsuleBytes": cb.len(), "ms": ms(t)}));
    }
    Ok(json!(out))
}

async fn validate(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let addr = need(a, "--validator")?;
    let (g, cap) = pkg_arg(need(a, "--pkg")?)?;
    let deps: Vec<Id> = flag(a, "--deps")
        .unwrap_or("")
        .split(',')
        .filter(|s| !s.is_empty())
        .map(|h| Id::from_hex(h).ok_or(format!("bad capsule {h}")))
        .collect::<R<_>>()?;
    let t = Instant::now();
    let targets = flag(a, "--targets").unwrap_or("");
    let mut prepared = Vec::new();
    let bind = flag(a, "--bind").map(|h| Id::from_hex(h).ok_or("bad --bind")).transpose()?;
    if bind.is_some() && !targets.is_empty() {
        return Err("--bind is for target-free jobs".into());
    }
    let (job, rc) = if targets.is_empty() {
        let job = receipt::issue(&kf, ws, wid, g, cap, deps, bind)?;
        let job = st.meta.issue_job(&job).await.map_err(es)?;
        let issuer = kf.job_issuer_signer(ws).ok_or(format!("no job issuer key for {ws}"))?;
        let rc = receipt::validate(addr, &job, &issuer, &st.ring.validators).await?;
        (job, rc)
    } else {
        let controller = need(a, "--controller")?;
        let authority: [u8; 32] = hex::decode(&kf.authority_public)
            .map_err(es)?
            .try_into()
            .map_err(|_| "bad controller public key")?;
        let call = |req: ControlRequest| {
            let signer = signer.clone();
            async move {
                call_controller(controller, &req, &signer, &authority, Duration::from_secs(1800))
                    .await.map_err(es)
            }
        };
        // With fixed controller shards (W4) each shard keeps its own worker
        // registry, and a target is validated by its own shard. Register with
        // every configured endpoint; one accepting shard is enough to start.
        let endpoints: Vec<String> = controller.split(',').map(str::trim)
            .filter(|s| !s.is_empty()).map(str::to_string).collect();
        let register = |endpoint: String| {
            let signer = signer.clone();
            let request = ControlRequest::Register { worker: wid.hex(), capacity_mb: 8192 };
            async move {
                call_controller(&endpoint, &request, &signer, &authority, Duration::from_secs(15)).await
            }
        };
        let mut lease = None;
        let mut refusal = None;
        for endpoint in &endpoints {
            match register(endpoint.clone()).await {
                Ok(ControlResponse::Registered { lease_ms }) => {
                    lease = Some(lease.map_or(lease_ms, |l: u64| l.min(lease_ms)))
                }
                other => refusal = Some(format!("{other:?}")),
            }
        }
        let Some(lease) = lease else {
            return Err(format!("controller registration: {}", refusal.unwrap_or_default()));
        };
        let mut requests = Vec::new();
        for target in targets.split(',').filter(|s| !s.is_empty()) {
            let (name, statement) = target.split_once(':').unwrap_or((target, ""));
            let name = Name::parse(name);
            let pt = Writer::new(st.clone(), wid, signer.clone())
                .prepare_target(&name)
                .await
                .map_err(es)?;
            prepared.push(pt);
            requests.push(TargetReq {
                name: name.to_string(),
                statement: statement.to_string(),
            });
        }
        let request = format!(
            "working-copy/{}/{}/{}",
            ws,
            g.hex(),
            hex::encode(rand::random::<[u8; 16]>())
        );
        let heartbeat = tokio::spawn({
            let signer = signer.clone();
            let authority = authority;
            let worker = wid.hex();
            async move {
                loop {
                    tokio::time::sleep(Duration::from_millis((lease / 3).max(100))).await;
                    for endpoint in &endpoints {
                        let beat = call_controller(
                            endpoint,
                            &ControlRequest::Heartbeat {
                                worker: worker.clone(),
                            },
                            &signer,
                            &authority,
                            Duration::from_secs(10),
                        )
                        .await;
                        // A shard that expired or never saw this worker re-registers it.
                        if matches!(beat, Ok(ControlResponse::Unknown)) {
                            let _ = call_controller(
                                endpoint,
                                &ControlRequest::Register { worker: worker.clone(), capacity_mb: 8192 },
                                &signer,
                                &authority,
                                Duration::from_secs(10),
                            )
                            .await;
                        }
                    }
                }
            }
        });
        let response = call(ControlRequest::Validate {
            worker: wid.hex(),
            request,
            group: g.hex(),
            capsule: cap.hex(),
            deps: deps.iter().map(Id::hex).collect(),
            targets: requests,
            memory_mb: 0,
            deadline_ms: 0,
        })
        .await;
        heartbeat.abort();
        match response? {
            ControlResponse::Receipt { receipt, job } => {
                let rc = Receipt::from_bytes(&hex::decode(receipt).map_err(es)?).map_err(es)?;
                let job = SignedJob::from_bytes(&hex::decode(job).map_err(es)?).map_err(es)?;
                if job.body.targets.len() != prepared.len()
                    || prepared.iter().any(|pt| {
                        !job.body
                            .targets
                            .iter()
                            .any(|t| t.name == pt.name && t.epoch == pt.epoch)
                    })
                {
                    return Err("target owner epoch changed during validation".into());
                }
                (job, rc)
            }
            other => return Err(format!("controller validation: {other:?}")),
        }
    };
    let el = ms(t);
    let accepted = rc.body.verdict == Verdict::Accepted;
    let reason = match &rc.body.verdict {
        Verdict::Rejected(r) => r.clone(),
        _ => String::new(),
    };
    c.write_new(&c.receipt(&rc.id()), &rc.to_bytes())
        .map_err(es)?;
    c.write_new(&c.job(&job.id()), &job.to_bytes())
        .map_err(es)?;
    c.log_transfer("validate", &g, 0, el);
    Ok(
        json!({"group": g.hex(), "capsule": cap.hex(), "accepted": accepted, "reason": reason,
        "receipt": rc.id().hex(), "job": job.id().hex(), "ms": el,
        "targets": prepared.iter().map(|p| json!({"name": name_json(&p.name), "epoch": p.epoch,
            "head": p.head.map(|h| h.hex())})).collect::<Vec<_>>() }),
    )
}

/// Test only (forgery suite): issue a job and sign an accepted receipt with the authority
/// and validator `v0` of another key file, without any check. With an untrusted key file
/// this is a rogue validator; with the trusted one, a compromised validator.
fn forge(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let kp = need(a, "--keys")?;
    let kf: KeyFile = serde_json::from_str(&std::fs::read_to_string(kp).map_err(es)?).map_err(es)?;
    let ws = need(a, "--ws")?;
    let (wid, _) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let (g, cap) = pkg_arg(need(a, "--pkg")?)?;
    let deps: Vec<Id> = flag(a, "--deps").unwrap_or("").split(',').filter(|s| !s.is_empty())
        .map(|h| Id::from_hex(h).ok_or(format!("bad capsule {h}"))).collect::<R<_>>()?;
    let bind = flag(a, "--bind").map(|h| Id::from_hex(h).ok_or("bad --bind")).transpose()?;
    let job = receipt::issue(&kf, "", wid, g, cap, deps, bind)?;
    let v = kf.validator_signer("v0").ok_or("no validator v0 seed")?;
    let rc = Receipt::sign(
        ReceiptBody {
            group: g,
            base: job.body.base,
            validator_key: v.public(),
            validator_bin: job.body.checker.0.to_vec(),
            policy: job.body.policy,
            request: Some(job.id().0.to_vec()),
            target: None,
            verdict: Verdict::Accepted,
            axioms: vec![],
        },
        &v,
    );
    c.write_new(&c.receipt(&rc.id()), &rc.to_bytes()).map_err(es)?;
    c.write_new(&c.job(&job.id()), &job.to_bytes()).map_err(es)?;
    Ok(json!({"group": g.hex(), "capsule": cap.hex(), "accepted": true, "reason": "", "receipt": rc.id().hex(), "job": job.id().hex()}))
}

// ---------------------------------------------------------------- publication

async fn target_get(a: &[&str]) -> R<Value> {
    let (st, _) = open()?;
    let name = Name::parse(need(a, "--name")?);
    let Some(record) = st.target(&name).await.map_err(es)? else {
        return Ok(json!({"name": name.to_string(), "exists": false}));
    };
    Ok(
        json!({"name": name.to_string(), "owner": record.owner.hex(), "epoch": record.epoch,
        "head": record.head.map(|h| h.hex()), "exists": true}),
    )
}

/// The revisions and marker of a plan entry (`ws-plan`) for `group`, published by `wid`
/// with receipt `rid`. The author must be the publishing workspace.
fn planned(e: &Value, g: Id, cap: Id, wid: WorkspaceId, rid: Id) -> R<(Vec<Revision>, Marker)> {
    let mut revisions = Vec::new();
    for r in e["revisions"].as_array().ok_or("revisions")? {
        let mut parents: Vec<Id> = r["parents"].as_array().ok_or("parents")?.iter().map(id_of).collect::<R<_>>()?;
        parents.sort();
        parents.dedup();
        revisions.push(Revision { group: g, name: name_of_json(&r["name"])?, parents, capsule: cap, workspace: wid });
    }
    let mut rids: Vec<Id> = revisions.iter().map(|r| r.id()).collect();
    rids.sort();
    let agent = |v: &Value| -> R<AgentId> { AgentId::from_hex(v.as_str().ok_or("agent")?).ok_or("bad agent".into()) };
    let marker = Marker {
        group: g,
        revisions: rids,
        receipt: rid,
        file_path: e["file"].as_str().ok_or("file")?.to_string(),
        anchor: if e["anchor"].is_null() { Anchor::FileStart } else { Anchor::After(id_of(&e["anchor"])?) },
        lamport: e["lamport"].as_u64().ok_or("lamport")?,
        author: agent(&e["author"])?,
        root_path: e["rootPath"].as_array().ok_or("rootPath")?.iter().map(|x| Ok((id_of(&x[0])?, x[1].as_u64().ok_or("l")?, agent(&x[2])?))).collect::<R<_>>()?,
        lineage_keys: e["lineageKeys"].as_array().ok_or("lineageKeys")?.iter().map(|x| Ok((name_of_json(&x[0])?, x[1].as_u64().ok_or("l")?, agent(&x[2])?))).collect::<R<_>>()?,
    };
    if marker.author.0 != wid.0 {
        return Err("a record's author must be the publishing workspace".into());
    }
    // W2 A-6: the path every syncing copy writes (T1 and receivers check it as well)
    marker.check().map_err(|e| format!("plan entry for {g}: {e}"))?;
    Ok((revisions, marker))
}

async fn publish(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let w = Writer::new(st.clone(), wid, signer);
    let plan: Value = serde_json::from_str(&std::fs::read_to_string(need(a, "--plan")?).map_err(es)?).map_err(es)?;
    let mut out = Vec::new();
    for e in plan.as_array().ok_or("plan: expected an array")? {
        let t = Instant::now();
        let g = id_of(&e["group"])?;
        let cap = id_of(&e["capsule"])?;
        let rid = id_of(&e["receipt"])?;
        let jid = id_of(&e["job"])?;
        let receipt = Receipt::from_bytes(&std::fs::read(c.receipt(&rid)).map_err(|e| format!("receipt {rid}: {e}"))?).map_err(es)?;
        let job = SignedJob::from_bytes(&std::fs::read(c.job(&jid)).map_err(|e| format!("job {jid}: {e}"))?).map_err(es)?;
        let gbytes = std::fs::read(c.object(&g)).map_err(|e| format!("payload {g}: {e}"))?;
        let cbytes = std::fs::read(c.capsule(&cap)).map_err(|e| format!("capsule {cap}: {e}"))?;
        let (revisions, marker) = planned(e, g, cap, wid, receipt.id())?;
        let rids = marker.revisions.clone();
        if job.body.capsule != cap {
            return Err(format!("the job of {g} names another capsule"));
        }
        let p = Package {
            group: Opaque::new(Kind::Group, gbytes),
            chunks: vec![],
            capsule: Opaque::new(Kind::Capsule, cbytes),
            receipt,
            job,
            revisions,
            marker: marker.clone(),
            targets: e["targets"].as_array().map(|ts| ts.iter().map(|t| Ok(PreparedTarget {
                name: name_of_json(&t["name"])?, epoch: t["epoch"].as_u64().ok_or("target epoch")?,
                head: if t["head"].is_null() { None } else { Some(id_of(&t["head"])?) },
            })).collect::<R<Vec<_>>>()).transpose()?.unwrap_or_default(),
        };
        let o = w.publish(&p).await.map_err(es)?;
        out.push(json!({"group": g.hex(), "marker": o.marker.hex(), "fresh": o.fresh, "revisions": rids.iter().map(|r| r.hex()).collect::<Vec<_>>(), "ms": ms(t)}));
    }
    Ok(json!(out))
}

async fn tombstone(a: &[&str]) -> R<Value> {
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let target = Id::from_hex(need(a, "--target")?).ok_or("bad target")?;
    let position = flag(a, "--position").and_then(Id::from_hex);
    let target_marker = match position {
        Some(id) => st.marker_variant(&target, &id).await.map_err(es)?,
        None => st.marker_base(&target).await.map_err(es)?.map(|(_, m)| m),
    }.ok_or("unknown tombstone target")?;
    let t = Tombstone {
        file_path: need(a, "--file")?.to_string(),
        target,
        lamport: need(a, "--lamport")?.parse().map_err(es)?,
        author: if a.contains(&"--controller") { controller_agent_id(&st.ring.authority) } else { target_marker.author },
        receipt: None,
        position,
        batch: None,
    };
    t.check().map_err(|e| format!("--file: {e}"))?;
    // T8 checks the exact signed controller grant and current fence inside its transaction.
    // Worker key files have no authority seed, so --controller requires the controller's
    // full key file in PARALEAN_KEYS.
    let writer = Writer::new(st.clone(), wid, signer);
    let fresh = if a.contains(&"--controller") {
        let authority = kf.authority_signer().ok_or("--controller requires the controller's key file")?;
        let grant = Controller::new(st, authority).deletion_grant(&t).await.map_err(es)?;
        writer.tombstone_authorized(&t, Some(grant)).await.map_err(es)?
    } else {
        writer.tombstone(&t).await.map_err(es)?
    };
    Ok(json!({"tombstone": t.id().hex(), "fresh": fresh}))
}

async fn move_position(a: &[&str]) -> R<Value> {
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let group = Id::from_hex(need(a, "--target")?).ok_or("bad target")?;
    let position = Id::from_hex(need(a, "--position")?).ok_or("bad position")?;
    let new_lamport: u64 = need(a, "--lamport")?.parse().map_err(es)?;
    let old = st.marker_variant(&group, &position).await.map_err(es)?.ok_or("unknown position")?;
    let file = need(a, "--file")?;
    if old.file_path != file || new_lamport <= old.lamport + 1 { return Err("move has invalid file or Lamport time".into()); }
    let mut next = old.clone();
    next.lamport = new_lamport;
    if let Some(anchor) = flag(a, "--anchor") {
        let ag = Id::from_hex(anchor).ok_or("bad anchor group")?;
        let d = discover(&st).await.map_err(es)?;
        let ap = d.positions.iter().filter(|((g, _), p)| *g == ag && p.marker.file_path == file
            && !d.tombstones.values().any(|t| t.tombstone.target == ag && t.tombstone.position.is_none_or(|id| id == p.marker_id)))
            .map(|(_, p)| p).min_by_key(|p| (p.marker.lamport, p.marker.author.0, p.marker_id))
            .ok_or("anchor has no live position")?;
        next.anchor = Anchor::After(ag);
        next.root_path = ap.marker.root_path.clone();
    } else {
        next.anchor = Anchor::FileStart;
        next.root_path.clear();
    }
    next.root_path.push((group, new_lamport, old.author));
    let deletion = Tombstone { file_path: file.into(), target: group, position: Some(position),
        lamport: new_lamport - 1, author: old.author, receipt: None, batch: None };
    let w = Writer::new(st, wid, signer);
    w.tombstone(&deletion).await.map_err(es)?;
    let fresh = w.move_position(&next, &deletion).await.map_err(es)?;
    Ok(json!({"group": group.hex(), "old": position.hex(), "tombstone": deletion.id().hex(),
        "marker": next.id().hex(), "fresh": fresh}))
}

// ---------------------------------------------------------------- anti-entropy

/// Write one published group's records into the cache (marker, revisions, receipt, capsule).
/// Returns the bytes written and the batch that published it (its job's binding), whose
/// batch file the caller writes after every member.
async fn deliver_marker(st: &Store, c: &Cache, mid: &Id, m: &Marker, sub: &str) -> R<(usize, Option<Id>)> {
    let mut bytes = 0;
    let mut cap = None;
    // The record's revisions and their ancestry (transitively), so a reader decides
    // supersession from what it holds even when ancestors' markers are not delivered yet.
    let mut todo: Vec<Id> = m.revisions.clone();
    let mut seen = BTreeSet::new();
    while let Some(rid) = todo.pop() {
        if !seen.insert(rid) {
            continue;
        }
        let r = st.revision(&rid).await.map_err(es)?.ok_or(format!("revision {rid} missing"))?;
        if m.revisions.contains(&rid) {
            cap = Some(r.capsule);
        }
        todo.extend(r.parents.iter().copied());
        if !c.revision(&rid).exists() {
            let v = revision_json(&rid, &r).to_string();
            bytes += v.len();
            c.write_new(&c.revision(&rid), v.as_bytes()).map_err(es)?;
        }
    }
    let cap = cap.ok_or("marker without revisions")?;
    let rc = match std::fs::read(c.receipt(&m.receipt)) {
        Ok(b) => Receipt::from_bytes(&b).map_err(es)?,
        Err(_) => {
            let rc = st.receipt(&m.receipt).await.map_err(es)?.ok_or("receipt missing")?;
            let b = rc.to_bytes();
            bytes += b.len();
            c.write_new(&c.receipt(&m.receipt), &b).map_err(es)?;
            rc
        }
    };
    // The job envelope the receipt answers, and the capsules of the closure it pins.
    let jid = rc.body.request.as_ref().and_then(|q| <[u8; 32]>::try_from(&q[..]).ok()).map(Id).ok_or("receipt without a request")?;
    let job = match std::fs::read(c.job(&jid)) {
        Ok(b) => SignedJob::from_bytes(&b).map_err(es)?,
        Err(_) => {
            let v = st.meta.get(st.meta.keys.job(&jid)).await.map_err(es)?.ok_or("job envelope missing")?;
            bytes += v.len();
            c.write_new(&c.job(&jid), &v).map_err(es)?;
            SignedJob::from_bytes(&v).map_err(es)?
        }
    };
    let mut pid = String::new();
    for cid in job.body.deps.iter().chain(std::iter::once(&cap)) {
        let cb = match std::fs::read(c.capsule(cid)) {
            Ok(b) => b,
            Err(_) => {
                let pre = st.s3.get(Kind::Capsule, cid).await.map_err(es)?.ok_or(format!("capsule {cid} absent"))?;
                let b = Kind::Capsule.domain().strip(&pre).map_err(es)?.to_vec();
                bytes += b.len();
                b
            }
        };
        pid = c.put_capsule(cid, &cb)?;
    }
    let v = checked_marker_json(mid, m, &cap, &pid, job.body.batch)?.to_string();
    bytes += v.len();
    c.write_new(&c.p3().join(sub).join(format!("m-{}.json", mid.hex())), v.as_bytes()).map_err(es)?;
    Ok((bytes, job.body.batch))
}

/// Write the batch file of a committed batch into `sub`, after its members' records; the
/// record must name `member` (a marker or tombstone ID).
async fn deliver_batch_file(st: &Store, c: &Cache, sub: &str, b: &Id, member: &Id) -> R<usize> {
    if c.batch_rec(sub, b).exists() {
        return Ok(0);
    }
    let rec = st.batch(b).await.map_err(es)?.ok_or(format!("batch {b} is not committed"))?;
    if !rec.entries.iter().any(|e| e.object == *member) {
        return Err(format!("batch {b} does not list {member}"));
    }
    let v = batch_json(&rec).to_string();
    c.write_new(&c.batch_rec(sub, b), v.as_bytes()).map_err(es)?;
    Ok(v.len())
}

/// One unit of delivery: a single record, or every record of one batch and then its file.
#[derive(Debug, PartialEq)]
struct Unit {
    batch: Option<Id>,
    /// (is a marker, record ID) still to write.
    records: Vec<(bool, Id)>,
    /// Records the unit counts for `--max`: a batch counts whole.
    size: usize,
}

/// What `pull` delivers, in order: each new record (`new`), except that the members of a
/// batch (`batches`: batch ↦ member record IDs) form one unit, which is delivered whole or
/// not at all. A batch whose file is missing (`filed` lacks it: an interrupted pull) is
/// delivered again; one the response lacks a member of is not delivered. `kept` (`--only`)
/// keeps a unit any member of which it names; `seed` shuffles units; `max` takes the
/// longest prefix of at most that many records.
fn delivery_units(new: &[(bool, Id)], batches: &BTreeMap<Id, Vec<Id>>, filed: &BTreeSet<Id>,
    response: &BTreeSet<Id>, kept: &dyn Fn(&Id) -> bool, seed: Option<u64>, max: Option<usize>) -> Vec<Unit> {
    let member_of: BTreeMap<Id, Id> = batches.iter().flat_map(|(b, ms)| ms.iter().map(move |m| (*m, *b))).collect();
    let mut units: Vec<Unit> = Vec::new();
    let mut batch_unit: BTreeMap<Id, usize> = BTreeMap::new();
    for &(is_marker, id) in new {
        match member_of.get(&id) {
            None => units.push(Unit { batch: None, records: vec![(is_marker, id)], size: 1 }),
            Some(b) => {
                let i = *batch_unit.entry(*b).or_insert_with(|| {
                    units.push(Unit { batch: Some(*b), records: vec![], size: batches[b].len() });
                    units.len() - 1
                });
                units[i].records.push((is_marker, id));
            }
        }
    }
    for (b, ms) in batches {
        if !batch_unit.contains_key(b) && !filed.contains(b) && ms.iter().any(|m| response.contains(m)) {
            units.push(Unit { batch: Some(*b), records: vec![], size: ms.len() });
        }
    }
    units.retain(|u| match u.batch {
        None => u.records.iter().any(|(_, id)| kept(id)),
        Some(b) => batches[&b].iter().all(|m| response.contains(m)) && (kept(&b) || batches[&b].iter().any(kept)),
    });
    if let Some(s) = seed {
        units.shuffle(&mut rand::rngs::StdRng::seed_from_u64(s));
    }
    if let Some(n) = max {
        let (mut total, mut keep) = (0, 0);
        while keep < units.len() && total + units[keep].size <= n {
            total += units[keep].size;
            keep += 1;
        }
        units.truncate(keep);
    }
    units
}

async fn pull(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    c.init().map_err(es)?;
    let (st, _) = open()?;
    let t = Instant::now();
    // A response: the records some replica returned. `--replay` serves an earlier saved
    // response (a lagging replica); `--save` records this one.
    let current = discover(&st).await.map_err(es)?;
    let (resp_markers, resp_tombs): (Vec<Id>, Vec<Id>) = if let Some(f) = flag(a, "--replay") {
        let v: Value = serde_json::from_str(&std::fs::read_to_string(f).map_err(es)?).map_err(es)?;
        let ids = |k: &str| -> R<Vec<Id>> { v[k].as_array().ok_or(k.to_string())?.iter().map(id_of).collect() };
        let markers = if v["positions"].is_array() { ids("positions")? } else {
            ids("groups")?.iter().filter_map(|g| current.groups.get(g).map(|p| p.marker_id)).collect()
        };
        (markers, ids("tombstones")?)
    } else {
        // Certificate discovery excludes raw, uncertified tombstones.
        (current.positions.keys().map(|(_, marker)| *marker).collect(), current.tombstones.keys().copied().collect())
    };
    if let Some(f) = flag(a, "--save") {
        let v = json!({"groups": current.groups.keys().map(Id::hex).collect::<Vec<_>>(),
            "positions": resp_markers.iter().map(Id::hex).collect::<Vec<_>>(),
            "tombstones": resp_tombs.iter().map(Id::hex).collect::<Vec<_>>()});
        std::fs::write(f, v.to_string()).map_err(es)?;
    }
    // Stale-response check: a response must cover every record this copy already knows.
    let known_groups = known_ids(&c, "id-m")?;
    let known_tombs = known_ids(&c, "id-t")?;
    let rm: BTreeSet<Id> = resp_markers.iter().copied().collect();
    let rt: BTreeSet<Id> = resp_tombs.iter().copied().collect();
    let missing = known_groups.difference(&rm).count() + known_tombs.difference(&rt).count();
    if missing > 0 {
        return Ok(json!({"stale": true, "missingKnown": missing, "delivered": 0,
            "reason": format!("response lacks {missing} record(s) this copy already knows: rejected as stale")}));
    }
    // Which new records to deliver now, and in which order.
    let mut new_groups: Vec<Id> = rm.difference(&known_groups).copied().collect();
    let mut new_tombs: Vec<Id> = rt.difference(&known_tombs).copied().collect();
    if let Some(only) = flag(a, "--only") {
        let keep: BTreeSet<String> = only.split(',').map(String::from).collect();
        new_groups.retain(|mid| keep.contains(&mid.hex()) || current.positions.iter()
            .any(|((g, m), _)| m == mid && keep.contains(&g.hex())));
        new_tombs.retain(|t| keep.contains(&t.hex()));
    }
    let new: Vec<(bool, Id)> = new_groups.iter().map(|g| (true, *g)).chain(new_tombs.iter().map(|t| (false, *t))).collect();
    let batches: BTreeMap<Id, Vec<Id>> = current.batches.iter()
        .map(|(b, r)| (*b, r.entries.iter().map(|e| e.object).collect())).collect();
    let filed: BTreeSet<Id> = batches.keys().filter(|b| c.batch_rec("records", b).exists()).copied().collect();
    let response: BTreeSet<Id> = rm.union(&rt).copied().collect();
    let keep: Option<BTreeSet<String>> = flag(a, "--only").map(|o| o.split(',').map(String::from).collect());
    let kept = |id: &Id| keep.as_ref().is_none_or(|k| k.contains(&id.hex()) || current.positions.iter()
        .any(|((g, m), _)| m == id && k.contains(&g.hex())));
    let seed = flag(a, "--seed").map(|s| s.parse::<u64>()).transpose().map_err(es)?;
    let max = flag(a, "--max").map(|s| s.parse::<usize>()).transpose().map_err(es)?;
    let units = delivery_units(&new, &batches, &filed, &response, &kept, seed, max);
    let mut bytes = 0;
    let mut delivered = Vec::new();
    'units: for u in units {
        // never deliver an uncertified record, nor a batch with one
        for (is_marker, id) in &u.records {
            let certified = if *is_marker {
                let ((group, mid), _) = current.positions.iter().find(|((_, mid), _)| mid == id).ok_or("marker vanished")?;
                st.certs(group).await.map_err(es)?.iter().any(|c| c.body.marker == *mid)
            } else {
                !st.tcerts(id).await.map_err(es)?.is_empty()
            };
            if !certified {
                continue 'units;
            }
        }
        for (is_marker, id) in &u.records {
            if *is_marker {
                let ((group, mid), p) = current.positions.iter().find(|((_, mid), _)| mid == id).ok_or("marker vanished")?;
                let (n, bound) = deliver_marker(&st, &c, mid, &p.marker, "records").await?;
                if bound != u.batch {
                    return Err(format!("marker {mid}: its job's batch differs from the batch record's"));
                }
                bytes += n;
                delivered.push(json!(["marker", group.hex()]));
            } else {
                let tb = st.tombstone(id).await.map_err(es)?.ok_or("tombstone vanished")?;
                if tb.batch != u.batch {
                    return Err(format!("tombstone {id}: its batch differs from the batch record's"));
                }
                let tv = checked_tomb_json(id, &tb)?.to_string();
                bytes += tv.len();
                c.write_new(&c.tomb_rec(id), tv.as_bytes()).map_err(es)?;
                delivered.push(json!(["tombstone", id.hex()]));
            }
        }
        if let Some(b) = u.batch {
            let first = batches[&b][0];
            bytes += deliver_batch_file(&st, &c, "records", &b, &first).await?;
            delivered.push(json!(["batch", b.hex()]));
        }
    }
    let el = ms(t);
    if !delivered.is_empty() {
        c.log_transfer("pull", &Id::default(), bytes, el);
    }
    Ok(json!({"stale": false, "delivered": delivered.len(), "records": delivered, "bytes": bytes, "ms": el,
        "available": rm.len() + rt.len()}))
}

/// IDs of known records: `group` = marker groups; `id-t` = tombstone IDs.
fn known_ids(c: &Cache, what: &str) -> R<BTreeSet<Id>> {
    let mut out = BTreeSet::new();
    let dir = c.p3().join("records");
    let Ok(rd) = std::fs::read_dir(&dir) else { return Ok(out) };
    for e in rd {
        let p = e.map_err(es)?.path();
        let n = p.file_name().and_then(|x| x.to_str()).unwrap_or_default().to_string();
        if !n.ends_with(".json") {
            continue;
        }
        let v: Value = serde_json::from_str(&std::fs::read_to_string(&p).map_err(es)?).map_err(es)?;
        match what {
            "group" if n.starts_with("m-") => {
                out.insert(id_of(&v["group"])?);
            }
            "id-m" if n.starts_with("m-") => { out.insert(id_of(&v["id"])?); }
            "id-t" if n.starts_with("t-") => {
                out.insert(id_of(&v["id"])?);
            }
            _ => {}
        }
    }
    Ok(out)
}

async fn fetch_group(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let g = Id::from_hex(a.last().ok_or(USAGE)?).ok_or("bad group")?;
    if c.object(&g).exists() {
        return Ok(json!({"group": g.hex(), "cached": true}));
    }
    let (st, _) = open()?;
    let t = Instant::now();
    let pre = st.s3.get(Kind::Group, &g).await.map_err(es)?.ok_or(format!("group {g} absent or corrupt"))?;
    let b = Kind::Group.domain().strip(&pre).map_err(es)?.to_vec();
    c.write_new(&c.object(&g), &b).map_err(es)?;
    let el = ms(t);
    c.log_transfer("fetch-group", &g, b.len(), el);
    Ok(json!({"group": g.hex(), "bytes": b.len(), "ms": el}))
}

async fn fetch_pkg_cmd(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    c.init().map_err(es)?;
    let g = Id::from_hex(a.last().ok_or(USAGE)?).ok_or("bad group")?;
    let (st, _) = open()?;
    let t = Instant::now();
    let (mid, m) = st.marker(&g).await.map_err(es)?.ok_or(format!("{g} is not published"))?;
    if st.certs(&g).await.map_err(es)?.is_empty() {
        return Err(format!("{g} has no publication certificate"));
    }
    let (mut bytes, batch) = deliver_marker(&st, &c, &mid, &m, "fetched").await?;
    if let Some(b) = batch {
        bytes += deliver_batch_file(&st, &c, "fetched", &b, &mid).await?;
    }
    let el = ms(t);
    c.log_transfer("fetch-pkg", &g, bytes, el);
    Ok(json!({"group": g.hex(), "marker": mid.hex(), "bytes": bytes, "ms": el}))
}

// ---------------------------------------------------------------- checkpoints and snapshots

async fn checkpoint(a: &[&str]) -> R<Value> {
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let w = Writer::new(st.clone(), wid, signer);
    let ctl = Controller::new(st.clone(), kf.authority_signer().ok_or("no authority seed")?);
    let mut contents: Vec<Id> = need(a, "--revisions")?.split(',').filter(|s| !s.is_empty()).map(|s| Id::from_hex(s).ok_or("bad revision")).collect::<std::result::Result<_, _>>()?;
    contents.sort();
    contents.dedup();
    let predecessor = flag(a, "--predecessor").and_then(Id::from_hex);
    let files: Vec<(String, Vec<Id>)> = match flag(a, "--files") {
        Some(f) => {
            let v: Value = serde_json::from_str(&std::fs::read_to_string(f).map_err(es)?).map_err(es)?;
            v.as_array().ok_or("files")?.iter().map(|e| Ok((e[0].as_str().ok_or("path")?.to_string(), e[1].as_array().ok_or("ids")?.iter().map(id_of).collect::<R<_>>()?))).collect::<R<_>>()?
        }
        None => vec![],
    };
    let ok = flag(a, "--build-ok") != Some("0");
    let source_root = Manifest::SourceRoot { files };
    let build_receipt = Manifest::BuildReceipt {
        exporter_bin: b"paralean-p1-export".to_vec(),
        lean_commit: flag(a, "--lean-commit").unwrap_or("").into(),
        mathlib_commit: flag(a, "--mathlib-commit").unwrap_or("").into(),
        layout: source_root.id(),
        build_log_hash: flag(a, "--build-log-hash").map(|h| hex::decode(h).unwrap_or_default()).unwrap_or_default(),
        target_checks: vec![],
        verdict: if ok { BuildVerdict::Ok } else { BuildVerdict::Failed("build failed".into()) },
    };
    let token = ctl.rotate(wid, &rand::random::<[u8; 16]>()).await.map_err(es)?;
    let snapshot = Snapshot {
        workspace: wid,
        base: receipt::base()?,
        contents,
        predecessors: vec![],
        targets: vec![],
        source_root: source_root.id(),
        build_receipt: build_receipt.id(),
    };
    let sid = snapshot.id();
    let cp = Checkpoint { snapshot, source_root, build_receipt, predecessor, token };
    let cat = w.commit_checkpoint(&cp).await.map_err(es)?;
    Ok(json!({"catalog": cat.hex(), "snapshot": sid.hex(), "rank": token.rank}))
}

async fn snapshot_get(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    c.init().map_err(es)?;
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, _) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let t = Instant::now();
    let r = recover_catalog(&st, wid).await.map_err(es)?;
    let cat = match flag(a, "--catalog") {
        Some(h) => Id::from_hex(h).ok_or("bad catalog")?,
        None => r.selected.ok_or("no unique committed head")?,
    };
    let rs = r.records.get(&cat).ok_or("catalog record not found")?;
    if !rs.admissible {
        return Err(format!("catalog record {cat} is not admissible: {:?}", rs.reasons));
    }
    let snap: Snapshot = st.s3.get_object(Kind::Snapshot, &rs.record.snapshot).await.map_err(es)?.ok_or("snapshot absent")?;
    let mut bytes = 0;
    let mut groups = BTreeSet::new();
    for rid in &snap.contents {
        let rev = st.revision(rid).await.map_err(es)?.ok_or(format!("revision {rid} missing"))?;
        if groups.insert(rev.group) {
            let (mid, m) = st.marker(&rev.group).await.map_err(es)?.ok_or("marker missing")?;
            let (n, batch) = deliver_marker(&st, &c, &mid, &m, "records").await?;
            bytes += n;
            if let Some(b) = batch {
                bytes += deliver_batch_file(&st, &c, "records", &b, &mid).await?;
            }
            let pre = st.s3.get(Kind::Group, &rev.group).await.map_err(es)?.ok_or("payload absent")?;
            let b = Kind::Group.domain().strip(&pre).map_err(es)?.to_vec();
            bytes += b.len();
            c.write_new(&c.object(&rev.group), &b).map_err(es)?;
        }
    }
    Ok(json!({"catalog": cat.hex(), "snapshot": rs.record.snapshot.hex(), "groups": groups.len(),
        "revisions": snap.contents.len(), "bytes": bytes, "ms": ms(t),
        "heads": r.heads.iter().map(|h| h.hex()).collect::<Vec<_>>()}))
}

async fn check_receipt(a: &[&str]) -> R<Value> {
    let (st, _) = open()?;
    let g = Id::from_hex(a.last().ok_or(USAGE)?).ok_or("bad group")?;
    if let Some(s) = flag(a, "--staged") {
        return Ok(match check_staged(&st, &Cache::new(need(a, "--cache")?), &g, s, need(a, "--receipt")?).await {
            Ok((rc, job)) => json!({"admits": true, "receipt": rc.id().hex(), "job": job.id().hex(), "staged": true}),
            Err(e) => json!({"admits": false, "reason": e}),
        });
    }
    match paralean_validator_api::published_receipt(&st, &g).await {
        Ok((rc, job)) => Ok(json!({"admits": true, "receipt": rc.id().hex(), "job": job.id().hex()})),
        Err(e) => Ok(json!({"admits": false, "reason": format!("{e:?}")})),
    }
}

/// The consumer check of a staged batch member (`batch-share`), which is not published:
/// its receipt answers a job bound to the staging ID (so no transaction publishes it),
/// and is checked as T1 would check it against this store's key ring (the strict
/// verifier), revocations and cancellations.
async fn check_staged(st: &Store, c: &Cache, g: &Id, staging: &str, rid: &str) -> R<(Receipt, SignedJob)> {
    let staging = Id::from_hex(staging).ok_or("bad staging ID")?;
    let rid = Id::from_hex(rid).ok_or("bad receipt ID")?;
    let rc = Receipt::from_bytes(&std::fs::read(c.receipt(&rid)).map_err(es)?).map_err(es)?;
    let jid = rc.body.request.as_ref().and_then(|q| <[u8; 32]>::try_from(&q[..]).ok()).map(Id).ok_or("receipt without a request")?;
    let job = SignedJob::from_bytes(&std::fs::read(c.job(&jid)).map_err(es)?).map_err(es)?;
    if rc.id() != rid || job.id() != jid {
        return Err("the cached receipt or job is not the one named".into());
    }
    if job.body.batch != Some(staging) {
        return Err("the staged member's job is not bound to its staging ID".into());
    }
    paralean_store::receipt::check(&rc, &job, g, &paralean_store::receipt::prepared_of(&job), &st.ring)
        .map_err(|e| format!("{e:?}"))?;
    if st.meta.is_revoked(&rc.body.validator_key).await.map_err(es)? {
        return Err("the validator key is revoked".into());
    }
    if st.meta.is_cancelled(&job.body.worker, &job.body.request).await.map_err(es)? {
        return Err("the job is cancelled".into());
    }
    Ok((rc, job))
}

// ---------------------------------------------------------------- atomic batches

/// A workspace named in the key file (public entries suffice).
fn workspace_id(kf: &KeyFile, name: &str) -> R<WorkspaceId> {
    kf.workspaces.get(name).and_then(|e| WorkspaceId::from_hex(&e.id)).ok_or(format!("no workspace {name}"))
}

fn hex_field<T>(v: &Value, k: &str, f: impl Fn(&[u8]) -> std::result::Result<T, paralean_store::pce::DecodeError>) -> R<T> {
    f(&hex::decode(v[k].as_str().ok_or(format!("{k} missing"))?).map_err(es)?).map_err(es)
}

/// A batch description (`batch-intent`): the signed intent and, per member in commit order,
/// what each step adds (receipts and jobs, plan entries, certificates).
fn read_batch(path: &str) -> R<(Value, SignedBatch)> {
    let d: Value = serde_json::from_slice(&read_private(std::path::Path::new(path)).map_err(|e| format!("{path}: {e}"))?).map_err(es)?;
    let intent = hex_field(&d, "intent", SignedBatch::from_bytes)?;
    let members = d["members"].as_array().ok_or("members")?;
    if members.len() != intent.body.members.len() {
        return Err("the description's members differ from its intent's".into());
    }
    Ok((d, intent))
}

fn write_batch(path: &str, d: &Value) -> R<()> {
    replace_private(std::path::Path::new(path), serde_json::to_string_pretty(d).map_err(es)?.as_bytes()).map_err(|e| format!("{path}: {e}"))
}

/// A group's payload or capsule: this cache's copy, else the staged object in the store.
async fn object_bytes(st: &Store, local: std::path::PathBuf, kind: Kind, id: &Id) -> R<Vec<u8>> {
    if let Ok(b) = std::fs::read(&local) {
        return Ok(b);
    }
    let pre = st.s3.get(kind, id).await.map_err(es)?.ok_or(format!("{kind:?} {id} is neither cached nor staged"))?;
    Ok(kind.domain().strip(&pre).map_err(es)?.to_vec())
}

/// Share a validated, unpublished member with a participant's cache (`C2/p3/staged/S`):
/// its record, receipt, job and the capsules of its closure. The participant loads it only
/// while capturing for staging ID `S` (Lean `PARALEAN_BATCH`), on demand, never rendered,
/// and checks the receipt itself. The record has no placement: a staged member is never
/// rendered.
async fn batch_share(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let to = Cache::new(need(a, "--to")?);
    to.init().map_err(es)?;
    let (st, _) = open()?;
    let staging = Id::from_hex(need(a, "--staging")?).ok_or("bad --staging")?;
    let (g, cap) = pkg_arg(need(a, "--pkg")?)?;
    let rid = Id::from_hex(need(a, "--receipt")?).ok_or("bad --receipt")?;
    let rbytes = std::fs::read(c.receipt(&rid)).map_err(|e| format!("receipt {rid}: {e}"))?;
    let rc = Receipt::from_bytes(&rbytes).map_err(es)?;
    let jid = rc.body.request.as_ref().and_then(|q| <[u8; 32]>::try_from(&q[..]).ok()).map(Id).ok_or("receipt without a request")?;
    let jbytes = std::fs::read(c.job(&jid)).map_err(|e| format!("job {jid}: {e}"))?;
    let job = SignedJob::from_bytes(&jbytes).map_err(es)?;
    if job.body.batch != Some(staging) || job.body.capsule != cap {
        return Err("the receipt's job is not this capsule's, bound to the staging ID".into());
    }
    paralean_store::receipt::check(&rc, &job, &g, &[], &st.ring).map_err(|e| format!("{e:?}"))?;
    to.write_new(&to.receipt(&rid), &rbytes).map_err(es)?;
    to.write_new(&to.job(&jid), &jbytes).map_err(es)?;
    let mut pid = String::new();
    for cid in job.body.deps.iter().chain(std::iter::once(&cap)) {
        pid = to.put_capsule(cid, &object_bytes(&st, c.capsule(cid), Kind::Capsule, cid).await?)?;
    }
    let author = AgentId(job.body.worker.0);
    let m = Marker {
        group: g, revisions: vec![], receipt: rid, file_path: "Staged.lean".into(), anchor: Anchor::FileStart,
        lamport: 0, author, root_path: vec![], lineage_keys: vec![],
    };
    let v = checked_marker_json(&m.id(), &m, &cap, &pid, None)?.to_string();
    to.write_new(&to.staged(&staging).join(format!("m-{}.json", m.id().hex())), v.as_bytes()).map_err(es)?;
    Ok(json!({"group": g.hex(), "pid": pid, "staged": to.staged(&staging).display().to_string()}))
}

/// Sign a target-free batch intent with this copy's job-issuer key and start its private
/// description. Members are in commit order: `publish:GROUP:CAPSULE:WRITER:DEP,..` or
/// `tombstone:TARGET:POSITION:LAMPORT:WRITER:FILE` (a W3 deletion of that position, by its
/// author).
async fn batch_intent(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let issuer = kf.job_issuer_signer(ws).ok_or(format!("no job issuer key for {ws}"))?;
    let staging = Id::from_hex(need(a, "--staging")?).ok_or("bad --staging")?;
    let mut named = Vec::new();
    let mut members = Vec::new();
    for spec in flags(a, "--member") {
        let parts: Vec<&str> = spec.splitn(6, ':').collect();
        let id = |i: usize| -> R<Id> { parts.get(i).and_then(|h| Id::from_hex(h)).ok_or(format!("bad member {spec}")) };
        match parts[0] {
            "publish" if parts.len() == 5 => {
                let writer = workspace_id(&kf, parts[3])?;
                let deps: Vec<Id> = parts[4].split(',').filter(|s| !s.is_empty())
                    .map(|h| Id::from_hex(h).ok_or(format!("bad dependency {h}"))).collect::<R<_>>()?;
                named.push(BatchMember::Publish { group: id(1)?, writer });
                members.push(json!({"kind": "publish", "writer": parts[3], "group": id(1)?.hex(), "capsule": id(2)?.hex(),
                    "deps": deps.iter().map(Id::hex).collect::<Vec<_>>()}));
            }
            "tombstone" if parts.len() == 6 => {
                let (target, position) = (id(1)?, id(2)?);
                let writer = workspace_id(&kf, parts[4])?;
                let m = st.marker_variant(&target, &position).await.map_err(es)?.ok_or("unknown tombstone target")?;
                named.push(BatchMember::Tombstone { target, position: Some(position), writer });
                members.push(json!({"kind": "tombstone", "writer": parts[4], "target": target.hex(), "position": position.hex(),
                    "lamport": parts[3].parse::<u64>().map_err(es)?, "author": m.author.hex(), "file": parts[5]}));
            }
            _ => return Err(format!("bad member {spec}")),
        }
    }
    let request = format!("working-copy/{ws}/{}", staging.hex()).into_bytes();
    let intent = SignedBatch::sign(BatchIntent { request, members: named }, &issuer);
    let path = c.p3().join("batches").join(format!("{}.json", staging.hex()));
    let d = json!({"staging": staging.hex(), "coordinator": ws, "intent": hex::encode(intent.to_bytes()), "members": members});
    write_private(&path, serde_json::to_string_pretty(&d).map_err(es)?.as_bytes()).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(json!({"batch": intent.id().hex(), "description": path.display().to_string(), "members": members.len()}))
}

/// Issue each publication member's job bound to the intent (this copy's job-issuer key, the
/// member's writer as worker) and validate them in commit order as one validator batch, so
/// an earlier member's receipt serves a later member's dependency.
async fn batch_validate(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let path = need(a, "--batch")?;
    let addr = need(a, "--validator")?;
    let (mut d, intent) = read_batch(path)?;
    let issuer = kf.job_issuer_signer(ws).ok_or(format!("no job issuer key for {ws}"))?;
    let t = Instant::now();
    let mut jobs = Vec::new();
    let mut slots = Vec::new();
    for (i, m) in d["members"].as_array().ok_or("members")?.iter().enumerate() {
        if m["kind"] != "publish" {
            continue;
        }
        let deps: Vec<Id> = m["deps"].as_array().ok_or("deps")?.iter().map(id_of).collect::<R<_>>()?;
        let job = receipt::issue(&kf, ws, workspace_id(&kf, m["writer"].as_str().ok_or("writer")?)?,
            id_of(&m["group"])?, id_of(&m["capsule"])?, deps, Some(intent.id()))?;
        jobs.push(st.meta.issue_job(&job).await.map_err(es)?);
        slots.push(i);
    }
    let receipts = receipt::validate_batch(addr, &jobs, &issuer, &st.ring.validators).await?;
    let mut out = Vec::new();
    for ((i, job), rc) in slots.into_iter().zip(&jobs).zip(receipts) {
        let m = &mut d["members"][i];
        c.write_new(&c.job(&job.id()), &job.to_bytes()).map_err(es)?;
        m["job"] = json!(hex::encode(job.to_bytes()));
        let (accepted, reason, rid) = match rc {
            Ok(rc) => {
                c.write_new(&c.receipt(&rc.id()), &rc.to_bytes()).map_err(es)?;
                m["receipt"] = json!(hex::encode(rc.to_bytes()));
                let reason = match &rc.body.verdict { Verdict::Rejected(r) => r.clone(), _ => String::new() };
                (rc.body.verdict == Verdict::Accepted, reason, Some(rc.id().hex()))
            }
            Err(e) => (false, e, None),
        };
        out.push(json!({"group": m["group"], "capsule": m["capsule"], "writer": m["writer"], "accepted": accepted,
            "reason": reason, "receipt": rid, "job": job.id().hex()}));
    }
    write_batch(path, &d)?;
    Ok(json!({"batch": intent.id().hex(), "members": out, "ms": ms(t)}))
}

/// This workspace's certificates for its own members of the batch, after checking them: the
/// intent is genuine and names each member; a publication's receipt is accepted and answers
/// a job bound to this intent for exactly that group and capsule, and its record (from this
/// copy's plan, `ws-plan`) is authored here; a deletion names a published position of this
/// workspace's file. Nobody else's key is needed or used.
async fn batch_sign(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, kf) = open()?;
    let ws = need(a, "--ws")?;
    let (wid, signer) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let w = Writer::new(st.clone(), wid, signer);
    let path = need(a, "--batch")?;
    let (mut d, intent) = read_batch(path)?;
    if !intent.issued_by(&st.ring) {
        return Err("the batch intent is not signed by the controller or a job issuer".into());
    }
    let id = intent.id();
    let plan: Vec<Value> = match flag(a, "--plan") {
        Some(p) => serde_json::from_slice::<Value>(&read_private(std::path::Path::new(p)).map_err(es)?).map_err(es)?
            .as_array().ok_or("plan: expected an array")?.clone(),
        None => vec![],
    };
    let mut signed = Vec::new();
    for (i, named) in intent.body.members.iter().enumerate() {
        let m = &mut d["members"][i];
        match named {
            BatchMember::Publish { group, writer } if *writer == wid => {
                if m["group"] != json!(group.hex()) {
                    return Err(format!("member {i} differs from the intent"));
                }
                let cap = id_of(&m["capsule"])?;
                let rc = hex_field(m, "receipt", Receipt::from_bytes)?;
                let job = hex_field(m, "job", SignedJob::from_bytes)?;
                if job.body.batch != Some(id) || job.body.capsule != cap {
                    return Err(format!("member {i}: its job is not this capsule's, bound to this batch"));
                }
                paralean_store::receipt::check(&rc, &job, group, &[], &st.ring).map_err(|e| format!("member {i}: {e:?}"))?;
                let entry = plan.iter().find(|e| e["group"] == m["group"]).ok_or(format!("member {i} is not in the plan"))?;
                let (revisions, marker) = planned(entry, *group, cap, wid, rc.id())?;
                let p = Package {
                    group: Opaque::new(Kind::Group, object_bytes(&st, c.object(group), Kind::Group, group).await?),
                    chunks: vec![],
                    capsule: Opaque::new(Kind::Capsule, object_bytes(&st, c.capsule(&cap), Kind::Capsule, &cap).await?),
                    receipt: rc, job, revisions, marker, targets: vec![],
                };
                if p.group.id() != *group || p.capsule.id() != cap {
                    return Err(format!("member {i}: payload or capsule bytes differ from their IDs"));
                }
                m["entry"] = entry.clone();
                m["cert"] = json!(hex::encode(w.sign_batch_publication(&p).to_bytes()));
                signed.push(json!(["publish", group.hex()]));
            }
            BatchMember::Tombstone { target, position, writer } if *writer == wid => {
                let t = Tombstone {
                    file_path: m["file"].as_str().ok_or("file")?.to_string(),
                    target: *target,
                    lamport: m["lamport"].as_u64().ok_or("lamport")?,
                    author: AgentId::from_hex(m["author"].as_str().ok_or("author")?).ok_or("bad author")?,
                    receipt: None,
                    position: *position,
                    batch: Some(id),
                };
                t.check().map_err(|e| format!("member {i}: {e}"))?;
                let pos = position.ok_or("a batch deletes an exact position")?;
                let old = st.marker_variant(target, &pos).await.map_err(es)?.ok_or(format!("member {i}: unknown position"))?;
                if old.file_path != t.file_path || old.author.0 != wid.0 || t.lamport <= old.lamport
                    || m["target"] != json!(target.hex()) {
                    return Err(format!("member {i}: not a newer deletion of this workspace's position"));
                }
                m["cert"] = json!(hex::encode(w.sign_batch_tombstone(&t).to_bytes()));
                signed.push(json!(["tombstone", target.hex()]));
            }
            _ => {}
        }
    }
    write_batch(path, &d)?;
    Ok(json!({"batch": id.hex(), "signed": signed}))
}

/// T12: publish every member of the batch or none. The coordinator assembles what the
/// description holds and needs no member's key; the store checks the intent, the binding of
/// every member and each member's own T1 or T8 guards in one transaction.
async fn publish_batch(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    let (st, kf) = open()?;
    let (d, intent) = read_batch(need(a, "--batch")?)?;
    let t = Instant::now();
    let mut items = Vec::new();
    for (i, m) in d["members"].as_array().ok_or("members")?.iter().enumerate() {
        let writer = workspace_id(&kf, m["writer"].as_str().ok_or("writer")?)?;
        if m["cert"].is_null() {
            return Err(format!("member {i} is not signed by its writer"));
        }
        if m["kind"] == "publish" {
            let (g, cap) = (id_of(&m["group"])?, id_of(&m["capsule"])?);
            let receipt = hex_field(m, "receipt", Receipt::from_bytes)?;
            let (revisions, marker) = planned(&m["entry"], g, cap, writer, receipt.id())?;
            let package = Package {
                group: Opaque::new(Kind::Group, object_bytes(&st, c.object(&g), Kind::Group, &g).await?),
                chunks: vec![],
                capsule: Opaque::new(Kind::Capsule, object_bytes(&st, c.capsule(&cap), Kind::Capsule, &cap).await?),
                receipt,
                job: hex_field(m, "job", SignedJob::from_bytes)?,
                revisions,
                marker,
                targets: vec![],
            };
            items.push(BatchItem::Publish { package, writer, cert: hex_field(m, "cert", Cert::from_bytes)? });
        } else {
            let tombstone = Tombstone {
                file_path: m["file"].as_str().ok_or("file")?.to_string(),
                target: id_of(&m["target"])?,
                lamport: m["lamport"].as_u64().ok_or("lamport")?,
                author: AgentId::from_hex(m["author"].as_str().ok_or("author")?).ok_or("bad author")?,
                receipt: None,
                position: Some(id_of(&m["position"])?),
                batch: Some(intent.id()),
            };
            items.push(BatchItem::Tombstone { tombstone, writer, cert: hex_field(m, "cert", TombstoneCert::from_bytes)?, grant: None });
        }
    }
    let o = st.publish_batch(&BatchPackage { intent, items }).await.map_err(es)?;
    Ok(json!({"batch": o.batch.hex(), "fresh": o.fresh, "ms": ms(t),
        "members": o.record.entries.iter().map(|e| e.object.hex()).collect::<Vec<_>>()}))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(n: u8) -> Id {
        Id([n; 32])
    }

    /// Records 1..=5; batch 9 = {2, 3, 4}.
    fn setup() -> (Vec<(bool, Id)>, BTreeMap<Id, Vec<Id>>, BTreeSet<Id>) {
        let new = (1..=5).map(|n| (n != 4, id(n))).collect();
        let batches = BTreeMap::from([(id(9), vec![id(2), id(3), id(4)])]);
        (new, batches, (1..=5).map(id).collect())
    }

    fn delivered(units: &[Unit]) -> Vec<Id> {
        units.iter().flat_map(|u| u.records.iter().map(|r| r.1)).collect()
    }

    #[test]
    fn a_batch_is_one_unit() {
        let (new, batches, response) = setup();
        let units = delivery_units(&new, &batches, &BTreeSet::new(), &response, &|_| true, None, None);
        assert_eq!(units.len(), 3);
        assert_eq!(units[1], Unit { batch: Some(id(9)), records: vec![(true, id(2)), (true, id(3)), (false, id(4))], size: 3 });
    }

    #[test]
    fn max_seed_and_only_never_split_a_batch() {
        let (new, batches, response) = setup();
        for seed in 0..20 {
            for max in 0..=5 {
                let units = delivery_units(&new, &batches, &BTreeSet::new(), &response, &|_| true, Some(seed), Some(max));
                let got = delivered(&units);
                let members = [id(2), id(3), id(4)].iter().filter(|m| got.contains(m)).count();
                assert!(members == 0 || members == 3, "seed {seed} max {max}: {got:?}");
                assert!(got.len() <= max);
            }
        }
        // `--max` smaller than the batch: none of it, though it comes first
        let only_batch = |i: &Id| *i == id(3);
        assert!(delivery_units(&new, &batches, &BTreeSet::new(), &response, &only_batch, None, Some(2)).is_empty());
        // `--only` naming one member delivers the whole batch
        let units = delivery_units(&new, &batches, &BTreeSet::new(), &response, &only_batch, None, None);
        assert_eq!(delivered(&units), vec![id(2), id(3), id(4)]);
    }

    #[test]
    fn a_response_without_every_member_delivers_none_of_the_batch() {
        let (new, batches, mut response) = setup();
        response.remove(&id(4));
        let new: Vec<_> = new.into_iter().filter(|r| r.1 != id(4)).collect();
        let units = delivery_units(&new, &batches, &BTreeSet::new(), &response, &|_| true, None, None);
        assert_eq!(delivered(&units), vec![id(1), id(5)]);
    }

    #[test]
    fn an_unfiled_batch_is_delivered_again() {
        let (_, batches, response) = setup();
        // every member written by an interrupted pull, its file not
        let new = vec![(true, id(1))];
        let units = delivery_units(&new, &batches, &BTreeSet::new(), &response, &|_| true, None, None);
        assert_eq!(units[1], Unit { batch: Some(id(9)), records: vec![], size: 3 });
        let filed = BTreeSet::from([id(9)]);
        assert_eq!(delivery_units(&new, &batches, &filed, &response, &|_| true, None, None).len(), 1);
    }
}
