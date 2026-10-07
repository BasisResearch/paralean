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
use paralean_store::receipt::SignedJob;
use serde_json::{json, Value};

const USAGE: &str = "usage: plr <command> [args]
  keys-init KEYFILE TRUST ROGUEKEYS --agents a,b,..   keys, pins (policy v1, this checker), trust file for Lean
  stage --cache C --pkg GROUP:CAPSULE ...          upload payload and capsule (staged, unpublished)
  validate --cache C --ws W --validator ADDR --pkg GROUP:CAPSULE --deps C1,C2,..
                                                   issue a job envelope, get the validator's receipt
  publish --cache C --ws W --plan FILE            T1 for each planned record, in order
  tombstone --cache C --ws W --file F --target G --lamport L
  pull --cache C [--only G,..] [--seed S --max N] [--save FILE] [--replay FILE]
  fetch-group --cache C GROUP                      payload on demand (remote%)
  fetch-pkg --cache C GROUP                        a published group's records on demand
  checkpoint --cache C --ws W --revisions R,.. [--predecessor CAT] [--build-ok 0|1] [--files JSON]
  snapshot-get --cache C --ws W [--catalog CAT]   recover a committed snapshot into an empty cache
  forge --cache C --keys KEYFILE --ws W --pkg G:C [--deps ..]
                                                   test only: a job and an accepted receipt signed with KEYFILE's keys
  check-receipt GROUP                              P3 control's consumer check of a published group";

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
    let checker = receipt::checker()?;
    kf.policies = vec![paralean_store::receipt::Policy::v1().id().hex()];
    kf.checkers = vec![checker.id().hex()];
    std::fs::write(kpath, serde_json::to_string_pretty(&kf).unwrap()).map_err(es)?;
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
        std::fs::write(dir.join(format!("keys-{n}.json")), serde_json::to_string_pretty(&own).unwrap()).map_err(es)?;
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
    let (wid, _) = kf.workspace(ws).ok_or(format!("no workspace {ws}"))?;
    let addr = need(a, "--validator")?;
    let (g, cap) = pkg_arg(need(a, "--pkg")?)?;
    let deps: Vec<Id> = flag(a, "--deps").unwrap_or("").split(',').filter(|s| !s.is_empty())
        .map(|h| Id::from_hex(h).ok_or(format!("bad capsule {h}"))).collect::<R<_>>()?;
    let t = Instant::now();
    let job = receipt::issue(&kf, ws, wid, g, cap, deps)?;
    let job = st.meta.issue_job(&job).await.map_err(es)?;
    let rc = receipt::validate(addr, &job).await?;
    let el = ms(t);
    let accepted = rc.body.verdict == Verdict::Accepted;
    let reason = match &rc.body.verdict { Verdict::Rejected(r) => r.clone(), _ => String::new() };
    c.write_new(&c.receipt(&rc.id()), &rc.to_bytes()).map_err(es)?;
    c.write_new(&c.job(&job.id()), &job.to_bytes()).map_err(es)?;
    c.log_transfer("validate", &g, 0, el);
    Ok(json!({"group": g.hex(), "capsule": cap.hex(), "accepted": accepted, "reason": reason,
        "receipt": rc.id().hex(), "job": job.id().hex(), "ms": el}))
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
    let job = receipt::issue(&kf, "", wid, g, cap, deps)?;
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

async fn check_receipt(a: &[&str]) -> R<Value> {
    let (st, _) = open()?;
    let g = Id::from_hex(a.last().ok_or(USAGE)?).ok_or("bad group")?;
    match paralean_validator_api::published_receipt(&st, &g).await {
        Ok((rc, job)) => Ok(json!({"admits": true, "receipt": rc.id().hex(), "job": job.id().hex()})),
        Err(e) => Ok(json!({"admits": false, "reason": format!("{e:?}")})),
    }
}
