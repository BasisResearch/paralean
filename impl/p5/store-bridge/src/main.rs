//! P5 task journal. FDB holds a CAS head and immutable history; Garage holds the
//! content-addressed task/spec/state blob. Both live under the selected deployment.
use foundationdb::tuple::Subspace;
mod targets;
use paralean_store::{Faults, Id, Kind, Name, Opaque, Store, StoreConfig, TargetRecord};
use paralean_store::pce::Pce;
use serde_json::{json, Value};
use std::{env, fs, process::ExitCode};

type R<T> = Result<T, String>;

fn keyspace(deployment: &str) -> Subspace {
    Subspace::from(("paralean", deployment, "p5"))
}
fn head_key(space: &Subspace, task: &str) -> Vec<u8> {
    space.pack(&("head", task))
}
fn event_key(space: &Subspace, task: &str, sequence: u64) -> Vec<u8> {
    space.pack(&("event", task, sequence))
}
fn decode_head(bytes: &[u8]) -> R<(u64, Id)> {
    if bytes.len() != 40 { return Err("corrupt P5 head".into()); }
    let seq = u64::from_be_bytes(bytes[..8].try_into().unwrap());
    let id = Id(bytes[8..].try_into().unwrap());
    Ok((seq, id))
}
fn encode_head(seq: u64, id: Id) -> Vec<u8> {
    let mut b = seq.to_be_bytes().to_vec();
    b.extend_from_slice(&id.0);
    b
}
fn need<'a>(args: &'a [String], flag: &str) -> R<&'a str> {
    args.iter().position(|a| a == flag).and_then(|i| args.get(i+1)).map(String::as_str)
        .ok_or_else(|| format!("missing {flag}"))
}
fn task_id(s: &str) -> R<&str> {
    if s.is_empty() || s.len() > 128 || !s.bytes().all(|b| b.is_ascii_alphanumeric() || b"-_.".contains(&b)) {
        return Err("task ID must be 1..128 ASCII letters, digits, hyphen, underscore or dot".into());
    }
    Ok(s)
}
async fn run(args: Vec<String>) -> R<Value> {
    let dep = env::var("PARALEAN_DEPLOYMENT").map_err(|_| "PARALEAN_DEPLOYMENT is required")?;
    let cfg = StoreConfig::from_env(&dep).map_err(|e| e.to_string())?;
    let store = Store::open(&cfg, Default::default(), Faults::none()).map_err(|e| e.to_string())?;
    let space = keyspace(&dep);
    let cmd = args.first().map(String::as_str).ok_or("missing command")?;
    match cmd {
        "assign-target" | "validate-target" | "publish-target" | "verify-target" | "checkpoint-targets" => targets::run(&args).await,
        "put" => {
            let task = task_id(need(&args, "--task")?)?;
            let file = need(&args, "--file")?;
            let expected: u64 = need(&args, "--expected")?.parse().map_err(|_| "bad --expected")?;
            let bytes = fs::read(file).map_err(|e| e.to_string())?;
            let value: Value = serde_json::from_slice(&bytes).map_err(|e| format!("invalid JSON: {e}"))?;
            if value.get("task").and_then(Value::as_str) != Some(task) { return Err("payload names another task".into()); }
            let completion = if value.pointer("/state/phase").and_then(Value::as_str) == Some("complete") {
                let frozen = value.pointer("/spec/targets").and_then(Value::as_array).ok_or("complete task lacks frozen targets")?;
                let names = frozen.iter().map(|v| v.get("name").and_then(Value::as_str)
                    .ok_or_else(|| "frozen target name missing".to_owned()).map(str::to_owned))
                    .collect::<R<std::collections::BTreeSet<_>>>()?;
                let rows = value.get("completion_targets").and_then(Value::as_array).ok_or("complete task lacks completion_targets")?;
                if names.is_empty() || names.len() != frozen.len() || rows.len() != names.len() { return Err("completion target count differs from frozen task".into()); }
                let hashes = value.get("contract_hashes").and_then(Value::as_object).ok_or("complete task lacks frozen hashes")?;
                let mut seen = std::collections::BTreeSet::new();
                let mut checks = Vec::new();
                for row in rows {
                    let name = row.get("name").and_then(Value::as_str).ok_or("completion target name missing")?;
                    if !names.contains(name) || !seen.insert(name.to_owned()) { return Err("completion target names differ from frozen task".into()); }
                    let hash = row.get("statement_hash").and_then(Value::as_str).ok_or("completion hash missing")?;
                    if hashes.get(name).and_then(Value::as_str) != Some(hash) { return Err("completion statement differs from frozen contract".into()); }
                    let owner = row.get("owner").and_then(Value::as_str).and_then(paralean_store::WorkspaceId::from_hex).ok_or("completion owner invalid")?;
                    let epoch = row.get("epoch").and_then(Value::as_u64).ok_or("completion epoch invalid")?;
                    let head = row.get("head").and_then(Value::as_str).and_then(Id::from_hex).ok_or("completion head invalid")?;
                    let group = row.get("group").and_then(Value::as_str).and_then(Id::from_hex).ok_or("completion group invalid")?;
                    let n = Name::parse(name);
                    let rev = store.revision(&head).await.map_err(|e| e.to_string())?.ok_or("completion head revision absent")?;
                    if rev.name != n || rev.group != group { return Err("completion head does not identify target group".into()); }
                    checks.push((n, owner, epoch, head));
                }
                Some(checks)
            } else { None };
            let object = Opaque::new(Kind::Blob, bytes);
            let ack = store.s3.put_opaque(&object).await.map_err(|e| e.to_string())?;
            if ack.id() != object.id() { return Err("S3 acknowledgement ID mismatch".into()); }
            let next = expected.checked_add(1).ok_or("sequence overflow")?;
            let hk = head_key(&space, task);
            let ek = event_key(&space, task, next);
            let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
            for _ in 0..60 {
                let found = trx.get(&hk, false).await.map_err(|e| e.to_string())?;
                let current = match found.as_ref() { Some(v) => decode_head(v)?, None => (0, Id::default()) };
                if let Some(ref checks) = completion {
                    for (name, owner, epoch, head) in checks {
                        let raw = trx.get(&store.meta.keys.target(name), false).await.map_err(|e| e.to_string())?.ok_or("completion target record absent")?;
                        let record = TargetRecord::from_pce(&raw).map_err(|e| e.to_string())?;
                        if record.owner != *owner || record.epoch != *epoch || record.head != Some(*head) {
                            return Err(format!("target {name} changed before durable completion"));
                        }
                    }
                }
                if current.0 == next && current.1 == object.id() {
                    return Ok(json!({"sequence": next, "blob": object.id().hex(), "already": true}));
                }
                if current.0 != expected { return Err(format!("stale P5 state: expected {expected}, found {}", current.0)); }
                let packed = encode_head(next, object.id());
                trx.set(&hk, &packed);
                trx.set(&ek, &packed);
                match trx.commit().await {
                    Ok(_) => return Ok(json!({"sequence": next, "blob": object.id().hex(), "already": false})),
                    Err(e) => { trx = e.on_error().await.map_err(|e| e.to_string())?; }
                }
            }
            Err("P5 commit outcome unresolved after 60 retries".into())
        }
        "get" => {
            let task = task_id(need(&args, "--task")?)?;
            let out = need(&args, "--out")?;
            let hk = head_key(&space, task);
            let Some(raw) = store.meta.get(hk).await.map_err(|e| e.to_string())? else {
                return Ok(json!({"found": false}));
            };
            let (sequence, id) = decode_head(&raw)?;
            let pre = store.s3.get(Kind::Blob, &id).await.map_err(|e| e.to_string())?.ok_or("task blob absent or corrupt")?;
            let bytes = Kind::Blob.domain().strip(&pre).map_err(|e| e.to_string())?;
            let value: Value = serde_json::from_slice(bytes).map_err(|e| format!("task blob JSON invalid: {e}"))?;
            if value.get("task").and_then(Value::as_str) != Some(task) { return Err("task blob ID mismatch".into()); }
            let tmp = format!("{out}.tmp-{}", std::process::id());
            fs::write(&tmp, bytes).map_err(|e| e.to_string())?;
            fs::rename(&tmp, out).map_err(|e| e.to_string())?;
            Ok(json!({"found": true, "sequence": sequence, "blob": id.hex()}))
        }
        "list" => {
            let sub = space.subspace(&("head",));
            let rows = store.meta.scan(&sub, store.page, |_| None).await.map_err(|e| e.to_string())?;
            let mut tasks = Vec::new();
            for (key, value) in rows {
                let (_, task): (String, String) = space.unpack(&key).map_err(|e| e.to_string())?;
                let (sequence, id) = decode_head(&value)?;
                tasks.push(json!({"task": task, "sequence": sequence, "blob": id.hex()}));
            }
            Ok(json!({"tasks": tasks}))
        }
        _ => Err("usage: paralean-p5-store put --task ID --file JSON --expected N | get --task ID --out FILE | list".into()),
    }
}
#[tokio::main]
async fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    let result = run(args).await;
    // Join the native FDB network thread before process teardown, as P2's CLI
    // does. The upstream lifecycle API arrived with the P2 robustness changes.
    paralean_store::meta::shutdown();
    match result {
        Ok(value) => { println!("{value}"); ExitCode::SUCCESS }
        Err(error) => { eprintln!("paralean-p5-store: {error}"); ExitCode::from(2) }
    }
}
