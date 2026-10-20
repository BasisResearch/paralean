//! P5 target-aware publication through P3's signed validator jobs and P2 T1/T4.
//! This stays in P5 while the P3 remote CLI is independently developed.

#[path = "../../../p3-remote/src/cache.rs"]
mod cache;

use std::env;
use std::fs;
use std::time::{Duration, Instant};

use cache::{id_of, name_of_json, Cache};
use paralean_control::checker::{base_id, CheckerConfig};
use paralean_store::receipt::{self, Policy, TargetBinding};
use paralean_store::{
    AgentId, Anchor, Controller, Faults, Id, JobEnvelope, KeyFile, Kind, Marker, Name, Object,
    Opaque, Package, Receipt, Revision, Signed, SignedJob, Store, StoreConfig, Verdict, Writer,
};
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
        Some("assign-target") => assign(args).await,
        Some("validate-target") => validate_target(args).await,
        Some("publish-target") => publish_target(args).await,
        Some("verify-target") => verify_target(args).await,
        _ => Err("unknown target bridge command".into()),
    }
}

async fn assign(args: &[String]) -> R<Value> {
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, _) = workspace(&kf, args)?;
    let signer = kf
        .authority_signer()
        .ok_or("authority seed is required for target assignment")?;
    let ctl = Controller::new(store, signer);
    let request = need(args, "--request")?.as_bytes();
    if request.is_empty() {
        return Err("empty assignment request".into());
    }
    let epoch = ctl
        .reassign(&n, wid, request)
        .await
        .map_err(|e| e.to_string())?;
    Ok(json!({"name": n.to_string(), "owner": wid.hex(), "epoch": epoch}))
}

async fn validate_target(args: &[String]) -> R<Value> {
    let t = Instant::now();
    let c = cache(args)?;
    let (store, kf) = open()?;
    let n = name(args)?;
    let (wid, signer) = workspace(&kf, args)?;
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
    let response = validate(addr, &job, Duration::from_secs(1800))
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
    let binding = job
        .body
        .targets
        .iter()
        .find(|t| t.name == n && t.statement == statement)
        .ok_or("published job does not bind frozen target contract")?;
    let record = store
        .target(&n)
        .await
        .map_err(|e| e.to_string())?
        .ok_or("target record absent")?;
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
        "epoch": binding.epoch, "statement_hash": hex::encode(statement),
        "head": head.hex()}),
    )
}
