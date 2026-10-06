//! plr: the P3 bridge between a working copy's local cache and the P2 store.
//!
//! Configuration comes from the environment, as for `paralean-p2`: `PARALEAN_FDB_CLUSTER`,
//! `PARALEAN_S3_*`, `PARALEAN_DEPLOYMENT` and `PARALEAN_KEYS` (a key file from `keys-init`).
//! Each command prints one JSON value on stdout.

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
use receipt::*;
use serde_json::{json, Value};

const USAGE: &str = "usage: plr <command> [args]
  keys-init KEYFILE TRUST --agents a,b,.. --lean-commit C --mathlib-commit M
  stage --cache C --pkg GROUP:CAPSULE ...          upload payloads and capsules (staged, unpublished)
  validate --cache VC --validator V --paralean BIN --pkg GROUP:CAPSULE ...
                                                   validator process: fetch from the store, replay, sign receipts
  publish --cache C --ws W --plan FILE            T1 for each planned record, in order
  tombstone --cache C --ws W --file F --target G --lamport L
  pull --cache C [--only G,..] [--seed S --max N] [--save FILE] [--replay FILE]
  fetch-group --cache C GROUP                      payload on demand (remote%)
  fetch-pkg --cache C GROUP                        a published group's records on demand
  checkpoint --cache C --ws W --revisions R,.. [--predecessor CAT] [--build-ok 0|1] [--files JSON]
  snapshot-get --cache C --ws W [--catalog CAT]   recover a committed snapshot into an empty cache
  check-receipt --trust TRUST --receipt FILE --group G --capsule C";

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

fn trust_of(path: &str) -> R<Trust> {
    let v: Value = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?).map_err(es)?;
    let h32 = |s: &Value| -> R<[u8; 32]> {
        hex::decode(s.as_str().ok_or("hex")?).map_err(es)?.try_into().map_err(|_| "32 bytes".to_string())
    };
    Ok(Trust {
        base: Id(h32(&v["base"])?),
        policy: Id(h32(&v["policy"])?),
        validators: v["validators"].as_array().ok_or("validators")?.iter().map(h32).collect::<R<_>>()?,
        allowed_axioms: v["allowedAxioms"].as_array().ok_or("allowedAxioms")?.iter().filter_map(|x| x.as_str().map(String::from)).collect(),
    })
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

fn pkg_arg(s: &str) -> R<CheckRequest> {
    let (g, c) = s.split_once(':').ok_or(format!("bad --pkg {s}"))?;
    Ok(CheckRequest { group: Id::from_hex(g).ok_or("bad group")?, capsule: Id::from_hex(c).ok_or("bad capsule")? })
}

fn ms(t: Instant) -> f64 {
    t.elapsed().as_secs_f64() * 1000.0
}

#[tokio::main]
async fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    match run(&a).await {
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
        Some("tombstone") => tombstone(&a[1..]).await,
        Some("pull") => pull(&a[1..]).await,
        Some("fetch-group") => fetch_group(&a[1..]).await,
        Some("fetch-pkg") => fetch_pkg_cmd(&a[1..]).await,
        Some("checkpoint") => checkpoint(&a[1..]).await,
        Some("snapshot-get") => snapshot_get(&a[1..]).await,
        Some("check-receipt") => check_receipt(&a[1..]),
        _ => Err(USAGE.into()),
    }
}

// ---------------------------------------------------------------- keys and trust

fn keys_init(a: &[&str]) -> R<Value> {
    let (kpath, tpath) = (a.first().ok_or(USAGE)?, a.get(1).ok_or(USAGE)?);
    let agents: Vec<&str> = need(a, "--agents")?.split(',').filter(|s| !s.is_empty()).collect();
    let mut kf = KeyFile::default();
    let auth = Signer::generate();
    kf.authority = Some(hex::encode(auth.seed()));
    kf.authority_public = hex::encode(auth.public());
    let val = Signer::generate();
    kf.validators.insert("v0".into(), sign::KeyEntry { id: String::new(), public: hex::encode(val.public()), seed: Some(hex::encode(val.seed())) });
    // An untrusted key, for the forgery tests: it signs receipts nobody accepts.
    let rogue = Signer::generate();
    kf.validators.insert("rogue".into(), sign::KeyEntry { id: String::new(), public: hex::encode(rogue.public()), seed: Some(hex::encode(rogue.seed())) });
    for n in &agents {
        let s = Signer::generate();
        kf.workspaces.insert(n.to_string(), sign::KeyEntry { id: WorkspaceId::random().hex(), public: hex::encode(s.public()), seed: Some(hex::encode(s.seed())) });
    }
    std::fs::write(kpath, serde_json::to_string_pretty(&kf).unwrap()).map_err(es)?;
    let trust = Trust::new(need(a, "--lean-commit")?, need(a, "--mathlib-commit")?, vec![val.public()]);
    let tv = json!({
        "validators": [hex::encode(val.public())],
        "base": trust.base.hex(),
        "policy": trust.policy.hex(),
        "allowedAxioms": trust.allowed_axioms,
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
        let req = pkg_arg(p)?;
        let t = Instant::now();
        let g = std::fs::read(c.object(&req.group)).map_err(|e| format!("payload {}: {e}", req.group))?;
        let cb = std::fs::read(c.capsule(&req.capsule)).map_err(|e| format!("capsule {}: {e}", req.capsule))?;
        let ga = st.s3.put_opaque(&Opaque::new(Kind::Group, g.clone())).await.map_err(es)?;
        let ca = st.s3.put_opaque(&Opaque::new(Kind::Capsule, cb.clone())).await.map_err(es)?;
        if ga.id() != req.group || ca.id() != req.capsule {
            return Err(format!("staged IDs differ from the local ones for {p}"));
        }
        c.log_transfer("put-group", &req.group, g.len(), 0.0);
        c.log_transfer("put-capsule", &req.capsule, cb.len(), ms(t));
        out.push(json!({"group": req.group.hex(), "capsule": req.capsule.hex(), "groupBytes": g.len(), "capsuleBytes": cb.len(), "ms": ms(t)}));
    }
    Ok(json!(out))
}

/// Fetch a package and its dependency closure from the store into `c` (validator side, or
/// a snapshot restore). Dependencies must be published (marker with a valid certificate)
/// or listed in `batch`.
async fn fetch_closure(st: &Store, c: &Cache, roots: &[CheckRequest], batch: &BTreeSet<Id>, require_published: bool) -> R<(Vec<String>, usize)> {
    let mut todo: Vec<(Id, Id)> = roots.iter().map(|r| (r.group, r.capsule)).collect();
    let mut seen = BTreeSet::new();
    let mut pids = Vec::new();
    let mut bytes = 0;
    while let Some((g, cap)) = todo.pop() {
        if !seen.insert((g, cap)) {
            continue;
        }
        let cb = match std::fs::read(c.capsule(&cap)) {
            Ok(b) => b,
            Err(_) => {
                let pre = st.s3.get(Kind::Capsule, &cap).await.map_err(es)?.ok_or(format!("capsule {cap} absent"))?;
                let b = Kind::Capsule.domain().strip(&pre).map_err(es)?.to_vec();
                bytes += b.len();
                b
            }
        };
        let (pid, deps) = c.put_capsule(&cap, &cb)?;
        if !c.object(&g).exists() {
            let pre = st.s3.get(Kind::Group, &g).await.map_err(es)?.ok_or(format!("group {g} absent"))?;
            let b = Kind::Group.domain().strip(&pre).map_err(es)?.to_vec();
            bytes += b.len();
            c.write_new(&c.object(&g), &b).map_err(es)?;
        }
        pids.push(pid);
        for (_, dg, dc) in deps {
            if require_published && !batch.contains(&dg) {
                let published = st.marker(&dg).await.map_err(es)?.is_some() && !st.certs(&dg).await.map_err(es)?.is_empty();
                if !published {
                    return Err(format!("dependency {dg} of {g} is neither published nor in the batch"));
                }
            }
            todo.push((dg, dc));
        }
    }
    Ok((pids, bytes))
}

async fn validate(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    c.init().map_err(es)?;
    let vname = need(a, "--validator")?;
    let bin = need(a, "--paralean")?;
    let trust = trust_of(&std::env::var("PARALEAN_TRUST").map_err(|_| "PARALEAN_TRUST is not set")?)?;
    let (st, kf) = open()?;
    let signer = kf.validator_signer(vname).ok_or(format!("no seed for validator {vname}"))?;
    let reqs: Vec<CheckRequest> = flags(a, "--pkg").into_iter().map(pkg_arg).collect::<R<_>>()?;
    let batch: BTreeSet<Id> = reqs.iter().map(|r| r.group).collect();
    let t = Instant::now();
    let (_, fetched) = fetch_closure(&st, &c, &reqs, &batch, true).await?;
    let t_fetch = ms(t);
    // The roots' package IDs, in request order.
    let mut roots = Vec::new();
    for r in &reqs {
        let cb = std::fs::read(c.capsule(&r.capsule)).map_err(es)?;
        let v: Value = serde_json::from_slice(&cb).map_err(es)?;
        roots.push(v["rec"]["gid"].as_str().ok_or("gid")?.to_string());
    }
    let out_path = c.p3().join(format!("verdicts-{}.json", std::process::id()));
    let t2 = Instant::now();
    let o = std::process::Command::new(bin)
        .arg("validate-pkgs")
        .args(["--store", c.root.to_str().unwrap(), "--out", out_path.to_str().unwrap()])
        .args(&roots)
        .env("PARALEAN_STORE", &c.root)
        .output()
        .map_err(|e| format!("{bin}: {e}"))?;
    let t_check = ms(t2);
    let verdicts: Value = serde_json::from_str(&std::fs::read_to_string(&out_path).map_err(|e| {
        format!("validator produced no verdicts ({e}): {}", String::from_utf8_lossy(&o.stderr))
    })?)
    .map_err(es)?;
    let bin_hash = sha2::Digest::finalize(<sha2::Sha256 as sha2::Digest>::new_with_prefix(std::fs::read(bin).map_err(es)?)).to_vec();
    let v = Validator { signer, bin_hash, trust };
    let mut out = Vec::new();
    for (r, pid) in reqs.iter().zip(&roots) {
        let vd = &verdicts[pid.as_str()];
        let res = CheckResult {
            accepted: vd["ok"].as_bool().unwrap_or(false),
            reason: vd["reason"].as_str().unwrap_or("no verdict").to_string(),
            axioms: vd["axioms"].as_array().map(|xs| xs.iter().filter_map(|x| name_of_json(x).ok()).collect()).unwrap_or_default(),
        };
        let rc = v.issue(r, &res);
        let blob = st.s3.put(Kind::Blob, &Domain::Blob.preimage(&rc.to_bytes())).await.map_err(es)?;
        out.push(json!({"group": r.group.hex(), "capsule": r.capsule.hex(), "pid": pid, "accepted": res.accepted,
            "reason": res.reason, "receipt": rc.id().hex(), "blob": blob.id().hex()}));
    }
    Ok(json!({"receipts": out, "fetchedBytes": fetched, "fetchMs": t_fetch, "checkMs": t_check}))
}

// ---------------------------------------------------------------- publication

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
        let blob = id_of(&e["receiptBlob"])?;
        let pre = st.s3.get(Kind::Blob, &blob).await.map_err(es)?.ok_or("receipt blob absent")?;
        let receipt = Receipt::from_bytes(Domain::Blob.strip(&pre).map_err(es)?).map_err(es)?;
        let gbytes = std::fs::read(c.object(&g)).map_err(|e| format!("payload {g}: {e}"))?;
        let cbytes = std::fs::read(c.capsule(&cap)).map_err(|e| format!("capsule {cap}: {e}"))?;
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
            revisions: rids.clone(),
            receipt: receipt.id(),
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
        // Receipts are checked by the writer too (§6 staging rule); this adds the request
        // binding to the capsule.
        let trust = trust_of(&std::env::var("PARALEAN_TRUST").map_err(|_| "PARALEAN_TRUST is not set")?)?;
        trust.admits(&receipt, &CheckRequest { group: g, capsule: cap }).map_err(|e| format!("receipt for {g}: {e}"))?;
        let p = Package {
            group: Opaque::new(Kind::Group, gbytes),
            chunks: vec![],
            capsule: Opaque::new(Kind::Capsule, cbytes),
            receipt,
            revisions,
            marker: marker.clone(),
            targets: vec![],
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
    let (_, m) = st.marker(&target).await.map_err(es)?.ok_or("target is not published")?;
    if st.certs(&target).await.map_err(es)?.is_empty() {
        return Err("target has no certificate".into());
    }
    // OPEN-19 default: only the element's author deletes it.
    if m.author.0 != wid.0 {
        return Err("only the author of an element may delete it".into());
    }
    let t = Tombstone {
        file_path: need(a, "--file")?.to_string(),
        target,
        lamport: need(a, "--lamport")?.parse().map_err(es)?,
        author: AgentId(wid.0),
        receipt: None,
    };
    if t.file_path != m.file_path || t.lamport <= m.lamport {
        return Err("a tombstone names its target's file and is newer than it".into());
    }
    let s = Signed::sign(t, &signer);
    st.meta.raw_set(st.meta.keys.tombstone(&s.id()), s.to_bytes()).await.map_err(es)?;
    Ok(json!({"tombstone": s.id().hex()}))
}

// ---------------------------------------------------------------- anti-entropy

struct Discovered {
    markers: BTreeMap<Id, (Id, Marker)>, // group -> (marker id, marker)
    tombs: BTreeMap<Id, Tombstone>,
}

async fn discover_all(st: &Store) -> R<Discovered> {
    let d = discover(st).await.map_err(es)?;
    let mut markers = BTreeMap::new();
    for (g, p) in d.groups {
        markers.insert(g, (p.marker_id, p.marker));
    }
    let mut tombs = BTreeMap::new();
    for (_, v) in st.meta.scan(&st.meta.keys.sub("tombstone"), st.page, |_| None).await.map_err(es)? {
        let Ok(s) = Signed::<Tombstone>::from_bytes(&v) else { continue };
        if st.ring.verify_writer(&WorkspaceId(s.body.author.0), &s.id(), &s.sig) {
            tombs.insert(s.id(), s.body);
        }
    }
    Ok(Discovered { markers, tombs })
}

/// Write one published group's records into the cache (marker, revisions, receipt, capsule).
async fn deliver_marker(st: &Store, c: &Cache, mid: &Id, m: &Marker, sub: &str) -> R<usize> {
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
    if !c.receipt(&m.receipt).exists() {
        let rc = st.receipt(&m.receipt).await.map_err(es)?.ok_or("receipt missing")?;
        let b = rc.to_bytes();
        bytes += b.len();
        c.write_new(&c.receipt(&m.receipt), &b).map_err(es)?;
    }
    let cb = match std::fs::read(c.capsule(&cap)) {
        Ok(b) => b,
        Err(_) => {
            let pre = st.s3.get(Kind::Capsule, &cap).await.map_err(es)?.ok_or(format!("capsule {cap} absent"))?;
            let b = Kind::Capsule.domain().strip(&pre).map_err(es)?.to_vec();
            bytes += b.len();
            b
        }
    };
    let (pid, _) = c.put_capsule(&cap, &cb)?;
    let v = marker_json(mid, m, &cap, &pid).to_string();
    bytes += v.len();
    c.write_new(&c.p3().join(sub).join(format!("m-{}.json", mid.hex())), v.as_bytes()).map_err(es)?;
    Ok(bytes)
}

async fn pull(a: &[&str]) -> R<Value> {
    let c = Cache::new(need(a, "--cache")?);
    c.init().map_err(es)?;
    let (st, _) = open()?;
    let t = Instant::now();
    // A response: the records some replica returned. `--replay` serves an earlier saved
    // response (a lagging replica); `--save` records this one.
    let (resp_markers, resp_tombs): (Vec<Id>, Vec<Id>) = if let Some(f) = flag(a, "--replay") {
        let v: Value = serde_json::from_str(&std::fs::read_to_string(f).map_err(es)?).map_err(es)?;
        let ids = |k: &str| -> R<Vec<Id>> { v[k].as_array().ok_or(k.to_string())?.iter().map(id_of).collect() };
        (ids("groups")?, ids("tombstones")?)
    } else {
        let d = discover_all(&st).await?;
        (d.markers.keys().copied().collect(), d.tombs.keys().copied().collect())
    };
    if let Some(f) = flag(a, "--save") {
        let v = json!({"groups": resp_markers.iter().map(|g| g.hex()).collect::<Vec<_>>(), "tombstones": resp_tombs.iter().map(|t| t.hex()).collect::<Vec<_>>()});
        std::fs::write(f, v.to_string()).map_err(es)?;
    }
    // Stale-response check: a response must cover every record this copy already knows.
    let known_groups = known_ids(&c, "group")?;
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
        new_groups.retain(|g| keep.contains(&g.hex()));
        new_tombs.retain(|t| keep.contains(&t.hex()));
    }
    let mut order: Vec<(bool, Id)> = new_groups.iter().map(|g| (true, *g)).chain(new_tombs.iter().map(|t| (false, *t))).collect();
    if let Some(s) = flag(a, "--seed") {
        let mut rng = rand::rngs::StdRng::seed_from_u64(s.parse().map_err(es)?);
        order.shuffle(&mut rng);
    }
    if let Some(n) = flag(a, "--max") {
        order.truncate(n.parse().map_err(es)?);
    }
    let mut bytes = 0;
    let mut delivered = Vec::new();
    for (is_marker, id) in order {
        if is_marker {
            let (mid, m) = st.marker(&id).await.map_err(es)?.ok_or("marker vanished")?;
            if st.certs(&id).await.map_err(es)?.is_empty() {
                continue; // never deliver an uncertified marker
            }
            bytes += deliver_marker(&st, &c, &mid, &m, "records").await?;
            delivered.push(json!(["marker", id.hex()]));
        } else {
            let v = st.meta.get(st.meta.keys.tombstone(&id)).await.map_err(es)?.ok_or("tombstone vanished")?;
            let s = Signed::<Tombstone>::from_bytes(&v).map_err(es)?;
            let tv = tomb_json(&id, &s.body).to_string();
            bytes += tv.len();
            c.write_new(&c.tomb_rec(&id), tv.as_bytes()).map_err(es)?;
            delivered.push(json!(["tombstone", id.hex()]));
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
    let bytes = deliver_marker(&st, &c, &mid, &m, "fetched").await?;
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
    let trust = trust_of(&std::env::var("PARALEAN_TRUST").map_err(|_| "PARALEAN_TRUST is not set")?)?;
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
        base: trust.base,
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
            bytes += deliver_marker(&st, &c, &mid, &m, "records").await?;
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

fn check_receipt(a: &[&str]) -> R<Value> {
    let trust = trust_of(need(a, "--trust")?)?;
    let b = std::fs::read(need(a, "--receipt")?).map_err(es)?;
    let r = Receipt::from_bytes(&b).map_err(es)?;
    let req = CheckRequest { group: Id::from_hex(need(a, "--group")?).ok_or("group")?, capsule: Id::from_hex(need(a, "--capsule")?).ok_or("capsule")? };
    match trust.admits(&r, &req) {
        Ok(()) => Ok(json!({"admits": true, "request": req.id().hex()})),
        Err(e) => Ok(json!({"admits": false, "reason": e, "request": req.id().hex()})),
    }
}
