//! paralean-p3: the P3 control plane's processes and operator commands.
//!
//! Configuration comes from the environment (`impl/p3/scripts/env.sh` sets the store and
//! checker parts): `PARALEAN_FDB_CLUSTER`, `PARALEAN_S3_*`, `PARALEAN_DEPLOYMENT` (default
//! `default`), `PARALEAN_KEYS` (a key file; the validator, controller and worker each need
//! their own role file from `keys export`) and `PARALEAN_BIN` (impl/p1's `paralean`).

use std::collections::BTreeMap;
use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;
use std::time::Duration;

use paralean_control::checker::{base_id, CheckerConfig};
use paralean_control::controller::{call_controller, replay_generation_hint, ControlCall, ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::replay::ReplayConfig;
use paralean_control::gc::GcConfig;
use paralean_control::validator::{Validator, ValidatorConfig};
use paralean_control::worker::WorkerNode;
use paralean_control::keys::{self, Role};
use paralean_store::receipt::{Policy, Revocation, SignedRevocation};
use paralean_store::*;

const USAGE: &str = "usage: paralean-p3 <command> [args]
  keys init <path> [--validators N] [--workspaces N] [--demo]
                                   write a key file pinning policy v1 and this machine's checker
  keys add-validator <path> <name> rotation: add a validator key (the old ones stay trusted)
  keys add-issuer <path> <name>    add a job-envelope issuer key (target-free envelopes only)
  keys retire-validator <path> <name>
                                   rotation: remove a validator key from the configured set
  keys export <path> <out> --role validator|controller|worker [--name NAME]
                                   write the key file of one process: its own seed only
                                   (validator, controller and worker refuse any other seed)
  keys revoke-validator <name|public-hex> <reason>
                                   R1: revoke a validator key in the store (needs the authority seed)
  checker-version                  this machine's checker version and its ID
  validator --listen ADDR --key NAME [--max-running N] [--max-queued N] [--workdir DIR]
  controller --listen ADDR --validators A,B [--shard N --shards K] [--lease-ms N] [--max-work-queue N]
             [--no-gc] [--gc-grace-ticks N --gc-scan-limit N]
             [--replay-horizon-ticks H [--replay-grace-ticks N] [--require-replay-generation]]
             [--max-validations N] [--deadline-ms N] [--memory-mb N] [--attempts N]
  worker --name W --controller ADDR --p1-store DIR [--capacity-mb N] [--hold-ms N]
  submit --controller ADDR --request R --target NAME [--memory-mb N] [--generation G]
  assign --controller ADDR --target NAME --worker W [--generation G]
  assign-group --controller ADDR --targets NAME,NAME --worker W [--request R] [--generation G]
  cancel --controller ADDR --request R [--worker W] [--generation G]
                                   J3 for W's request R, or for every workspace's R
  status --controller ADDR";

type R<T> = std::result::Result<T, String>;

fn flags(args: &[String]) -> BTreeMap<String, String> {
    let mut m = BTreeMap::new();
    let mut i = 0;
    while i < args.len() {
        if let Some(k) = args[i].strip_prefix("--") {
            if i + 1 < args.len() && !args[i + 1].starts_with("--") {
                m.insert(k.to_string(), args[i + 1].clone());
                i += 2;
                continue;
            }
            m.insert(k.to_string(), "1".into());
        }
        i += 1;
    }
    m
}

fn num(f: &BTreeMap<String, String>, k: &str, d: u64) -> R<u64> {
    f.get(k).map(|s| s.parse().map_err(|e| format!("--{k}: {e}"))).unwrap_or(Ok(d))
}

/// The controller's snapshot and history GC. On unless `--no-gc` (`--gc` is accepted):
/// every state change retires the previous snapshot, and without the collector those
/// chunks and the snapshot's settled history are never reclaimed (W2-41).
fn controller_gc(f: &BTreeMap<String, String>) -> R<GcConfig> {
    let enabled = if cfg!(feature = "mutate-gc-off-by-default") { f.contains_key("gc") } else { !f.contains_key("no-gc") };
    Ok(GcConfig { enabled, grace_ticks: num(f, "gc-grace-ticks", 8)?, scan_limit: num(f, "gc-scan-limit", 128)? as usize })
}

/// Replay horizons (docs/w4-rest-log.md design 3): off unless `--replay-horizon-ticks`.
fn controller_replay(f: &BTreeMap<String, String>) -> R<ReplayConfig> {
    let horizon_ticks = f.get("replay-horizon-ticks").map(|_| num(f, "replay-horizon-ticks", 0)).transpose()?;
    if horizon_ticks == Some(0) { return Err("--replay-horizon-ticks must be positive".into()) }
    let require_generation = f.contains_key("require-replay-generation");
    if require_generation && horizon_ticks.is_none() {
        return Err("--require-replay-generation needs --replay-horizon-ticks".into());
    }
    let grace_ticks = num(f, "replay-grace-ticks", 8)?;
    if grace_ticks == 0 { return Err("--replay-grace-ticks must be positive".into()) }
    Ok(ReplayConfig { horizon_ticks, grace_ticks, require_generation })
}

fn keyfile() -> R<KeyFile> {
    let p = std::env::var("PARALEAN_KEYS").map_err(|_| "PARALEAN_KEYS not set (paralean-p3 keys init)")?;
    serde_json::from_str(&std::fs::read_to_string(&p).map_err(|e| format!("{p}: {e}"))?).map_err(|e| e.to_string())
}

fn open_store(kf: &KeyFile) -> R<Store> {
    let dep = std::env::var("PARALEAN_DEPLOYMENT").unwrap_or_else(|_| "default".into());
    let cfg = StoreConfig::from_env(&dep).map_err(|e| e.to_string())?;
    Store::open(&cfg, kf.ring(), Faults::none()).map_err(|e| e.to_string())
}

fn write_keys(path: &str, kf: &KeyFile) -> R<()> {
    kf.write_private(path).map_err(|e| format!("{path}: {e}"))
}

async fn ctl_call(f: &BTreeMap<String, String>, req: ControlRequest) -> R<ControlResponse> {
    let addr = f.get("controller").ok_or("--controller ADDR")?;
    let kf = keyfile()?;
    let signer = kf.authority_signer().ok_or("the key file holds no authority seed")?;
    call_controller(addr, &req, &signer, &kf.ring().authority, Duration::from_secs(900)).await.map_err(|e| e.to_string())
}

/// A request under a client-chosen ID, in replay generation `--generation G` or else the
/// owning shard's current one: a probe in a generation no shard has reached is refused
/// before anything is written, with the shard's generation, and the request is resent.
async fn ctl_call_scoped(f: &BTreeMap<String, String>, req: ControlRequest) -> R<ControlResponse> {
    let addr = f.get("controller").ok_or("--controller ADDR")?;
    let kf = keyfile()?;
    let signer = kf.authority_signer().ok_or("the key file holds no authority seed")?;
    let call = |generation: u64| {
        let call = ControlCall::scoped(generation, req.clone());
        let (signer, ring) = (signer.clone(), kf.ring());
        async move { call_controller(addr, &call, &signer, &ring.authority, Duration::from_secs(900)).await.map_err(|e| e.to_string()) }
    };
    if let Some(generation) = f.get("generation") {
        return call(generation.parse().map_err(|e| format!("--generation: {e}"))?).await;
    }
    let probe = call(u64::MAX).await?;
    match replay_generation_hint(&probe) {
        Some(generation) => call(generation).await,
        None => Ok(probe),
    }
}

async fn run(args: Vec<String>) -> R<()> {
    let a: Vec<&str> = args.iter().map(String::as_str).collect();
    let f = flags(&args);
    match a.as_slice() {
        ["keys", "init", path, ..] => {
            let nv = num(&f, "validators", 2)? as usize;
            let nw = num(&f, "workspaces", 4)? as usize;
            let mut kf = KeyFile::demo(nw);
            if !f.contains_key("demo") {
                kf = KeyFile::default();
                let auth = Signer::generate();
                kf.authority = Some(hex::encode(auth.seed()));
                kf.authority_public = hex::encode(auth.public());
                for i in 0..nw {
                    let s = Signer::generate();
                    kf.workspaces.insert(
                        format!("w{i}"),
                        paralean_store::sign::KeyEntry {
                            id: WorkspaceId::random().hex(),
                            public: hex::encode(s.public()),
                            seed: Some(hex::encode(s.seed())),
                        },
                    );
                }
            }
            kf.validators.clear();
            for i in 0..nv {
                kf.add_validator(&format!("v{i}"), &Signer::generate());
            }
            kf.policies = vec![Policy::v1().id().hex()];
            kf.checkers = vec![CheckerConfig::from_env()?.version()?.id().hex()];
            write_keys(path, &kf)?;
            println!("wrote {path}: {nv} validators, {nw} workspaces, checker {}", kf.checkers[0]);
        }
        ["keys", "add-validator", path, name] => {
            let mut kf: KeyFile = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
            let s = Signer::generate();
            kf.add_validator(name, &s);
            write_keys(path, &kf)?;
            println!("added validator {name}: {}", hex::encode(s.public()));
        }
        ["keys", "add-issuer", path, name] => {
            let mut kf: KeyFile = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
            let s = Signer::generate();
            kf.add_job_issuer(name, &s);
            write_keys(path, &kf)?;
            println!("added job issuer {name}: {}", hex::encode(s.public()));
        }
        ["keys", "export", path, out, ..] => {
            let kf: KeyFile = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?).map_err(|e| e.to_string())?;
            let role = Role::parse(f.get("role").ok_or("--role validator|controller|worker")?)?;
            let name = f.get("name").map(String::as_str);
            let exported = keys::export(&kf, role, name)?;
            write_keys(out, &exported)?;
            println!("wrote {out}: {role:?} {}", name.unwrap_or(""));
        }
        ["keys", "retire-validator", path, name] => {
            let mut kf: KeyFile = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
            kf.retire_validator(name).ok_or(format!("no validator {name}"))?;
            write_keys(path, &kf)?;
            println!("retired validator {name}");
        }
        ["keys", "revoke-validator", who, reason] => {
            let kf = keyfile()?;
            let key = match kf.validators.get(*who) {
                Some(e) => e.public.clone(),
                None => who.to_string(),
            };
            let key: [u8; 32] = hex::decode(&key).ok().and_then(|v| v.try_into().ok()).ok_or("not a validator name or key")?;
            let auth = kf.authority_signer().ok_or("the key file holds no authority seed")?;
            let store = open_store(&kf)?;
            let r = SignedRevocation::sign(Revocation { key, reason: reason.to_string() }, &auth);
            let fresh = store.meta.revoke_validator(&r).await.map_err(|e| e.to_string())?;
            println!("revoked {} ({})", hex::encode(key), if fresh { "new" } else { "already revoked" });
        }
        ["checker-version"] => {
            let v = CheckerConfig::from_env()?.version()?;
            println!("{} {} {} {}", v.id().hex(), v.lean_githash, hex::encode(&v.checker_sha256), v.mode);
        }
        ["validator", ..] => {
            let kf = keyfile()?;
            let name = f.get("key").ok_or("--key NAME")?;
            keys::check(&kf, Role::Validator, Some(name))?;
            let signer = kf.validator_signer(name).ok_or(format!("no seed for validator {name}"))?;
            let checker = CheckerConfig::from_env()?;
            let base = base_id(&checker.lean_githash);
            let v = Validator::new(ValidatorConfig {
                store: open_store(&kf)?,
                signer,
                checker,
                base,
                policies: vec![Policy::v1()],
                max_running: num(&f, "max-running", 2)? as usize,
                max_queued: num(&f, "max-queued", 16)? as usize,
                workdir: PathBuf::from(f.get("workdir").cloned().unwrap_or_else(|| {
                    // Per user; `prepare_workdir` refuses one that is not ours or not private.
                    format!("{}/paralean-validator-{}", std::env::var("TMPDIR").unwrap_or("/tmp".into()), unsafe { libc::geteuid() })
                })),
            })?;
            let l = tokio::net::TcpListener::bind(f.get("listen").ok_or("--listen ADDR")?).await.map_err(|e| e.to_string())?;
            println!("validator {name} on {} (checker {})", l.local_addr().unwrap(), v.checker_id().hex());
            v.serve(l).await.map_err(|e| e.to_string())?;
        }
        ["controller", ..] => {
            let kf = keyfile()?;
            keys::check(&kf, Role::Controller, None)?;
            let checker = CheckerConfig::from_env()?;
            let shard = u32::try_from(num(&f, "shard", 0)?).map_err(|_| "--shard exceeds u32")?;
            let shards = u32::try_from(num(&f, "shards", 1)?).map_err(|_| "--shards exceeds u32")?;
            if shards == 0 || shard >= shards { return Err("--shard must be less than positive --shards".into()) }
            let cp = ControlPlane::new_shard_with_replay(ControllerConfig {
                store: open_store(&kf)?,
                authority: kf.authority_signer().ok_or("the key file holds no authority seed")?,
                validators: f.get("validators").ok_or("--validators A,B")?.split(',').map(String::from).collect(),
                base: base_id(&checker.lean_githash),
                policy: Policy::v1().id(),
                checker: checker.version()?.id(),
                lease: Duration::from_millis(num(&f, "lease-ms", 3000)?),
                max_work_queue: num(&f, "max-work-queue", 64)? as usize,
                max_validations: num(&f, "max-validations", 16)? as usize,
                validation_deadline: Duration::from_millis(num(&f, "deadline-ms", 600_000)?),
                validation_memory_mb: num(&f, "memory-mb", 4096)?,
                validator_attempts: num(&f, "attempts", 4)? as usize,
            }, shard, shards, controller_gc(&f)?, controller_replay(&f)?);
            cp.verify_topology().await?;
            let l = tokio::net::TcpListener::bind(f.get("listen").ok_or("--listen ADDR")?).await.map_err(|e| e.to_string())?;
            println!("controller shard {shard}/{shards} on {}", l.local_addr().unwrap());
            cp.serve(l).await.map_err(|e| e.to_string())?;
        }
        ["worker", ..] => {
            let kf = keyfile()?;
            let name = f.get("name").ok_or("--name W")?;
            keys::check(&kf, Role::Worker, Some(name))?;
            let (id, s) = kf.workspace(name).ok_or(format!("no workspace {name}"))?;
            let w = WorkerNode::new(
                Writer::new(open_store(&kf)?, id, s),
                f.get("controller").ok_or("--controller ADDR")?,
                num(&f, "capacity-mb", 8192)?,
                &PathBuf::from(f.get("p1-store").ok_or("--p1-store DIR")?),
            )?;
            let lease = match w.register().await.map_err(|e| format!("{e:?}"))? {
                ControlResponse::Registered { lease_ms, .. } => lease_ms,
                other => return Err(format!("register: {other:?}")),
            };
            println!("worker {name} ({}) registered, lease {lease} ms", id.hex());
            let _hb = w.spawn_heartbeats(Duration::from_millis(lease / 3));
            Arc::clone(&w).run(Duration::from_millis(200), Duration::from_millis(num(&f, "hold-ms", 0)?)).await;
        }
        ["submit", ..] => {
            let r = ctl_call_scoped(
                &f,
                ControlRequest::SubmitWork {
                    request: f.get("request").ok_or("--request R")?.clone(),
                    target: f.get("target").ok_or("--target NAME")?.clone(),
                    memory_mb: num(&f, "memory-mb", 1024)?,
                },
            )
            .await?;
            println!("{}", serde_json::to_string(&r).unwrap());
        }
        ["assign", ..] => {
            let kf = keyfile()?;
            let w = f.get("worker").ok_or("--worker W")?;
            let id = kf.workspace(w).map(|(id, _)| id.hex()).unwrap_or(w.clone());
            let request = f.get("request").cloned().unwrap_or_else(|| format!("assign/{}", rand::random::<u64>()));
            let statements = f.get("statement").map(|s| vec![s.clone()]).unwrap_or_default();
            let r = ctl_call_scoped(&f, ControlRequest::AssignGroup {
                targets: vec![f.get("target").ok_or("--target NAME")?.clone()], worker: id, request, statements,
            }).await?;
            let r = match r { ControlResponse::AssignedGroup { epochs } => ControlResponse::Assigned { epoch: epochs[0] }, other => other };
            println!("{}", serde_json::to_string(&r).unwrap());
        }
        ["assign-group", ..] => {
            let kf = keyfile()?;
            let w = f.get("worker").ok_or("--worker W")?;
            let id = kf.workspace(w).map(|(id, _)| id.hex()).unwrap_or(w.clone());
            let targets: Vec<String> = f.get("targets").ok_or("--targets NAME,NAME")?.split(',').map(str::to_owned).collect();
            let request = f.get("request").cloned().unwrap_or_else(|| format!("assign-group/{}", rand::random::<u64>()));
            let statements = f.get("statements").map(|s| s.split(',').map(str::to_owned).collect()).unwrap_or_default();
            let r = ctl_call_scoped(&f, ControlRequest::AssignGroup { targets, worker: id, request, statements }).await?;
            println!("{}", serde_json::to_string(&r).unwrap());
        }
        ["cancel", ..] => {
            let kf = keyfile()?;
            let worker = f.get("worker").map(|w| kf.workspace(w).map(|(id, _)| id.hex()).unwrap_or(w.clone())).unwrap_or_default();
            let req = ControlRequest::Cancel { request: f.get("request").ok_or("--request R")?.clone(), worker };
            // `--generation G` names the request ID's generation (cancel is never refused for it).
            let r = if f.contains_key("generation") { ctl_call_scoped(&f, req).await? } else { ctl_call(&f, req).await? };
            println!("{}", serde_json::to_string(&r).unwrap());
        }
        ["status", ..] => {
            let r = ctl_call(&f, ControlRequest::Status).await?;
            println!("{}", serde_json::to_string_pretty(&r).unwrap());
        }
        _ => return Err(USAGE.into()),
    }
    Ok(())
}

fn main() -> ExitCode {
    match paralean_store::meta::run_main(run(std::env::args().skip(1).collect())) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("paralean-p3: {e}");
            ExitCode::FAILURE
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn controller_collects_unless_told_not_to() {
        let parse = |args: &[&str]| controller_gc(&flags(&args.iter().map(|a| a.to_string()).collect::<Vec<_>>())).unwrap();
        let default = parse(&["controller"]);
        assert!(default.enabled, "a default controller never reclaims retired snapshots");
        assert_eq!((default.grace_ticks, default.scan_limit), (8, 128));
        assert!(parse(&["controller", "--gc"]).enabled);
        assert!(!parse(&["controller", "--no-gc"]).enabled);
    }
}
