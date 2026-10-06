//! paralean-p2: a small CLI over the P2 store.
//!
//! Configuration comes from the environment (`scripts/env.sh` sets it):
//! `PARALEAN_FDB_CLUSTER`, `PARALEAN_S3_ENDPOINT`, `PARALEAN_S3_BUCKET`,
//! `PARALEAN_S3_ACCESS_KEY`, `PARALEAN_S3_SECRET_KEY`, `PARALEAN_DEPLOYMENT` (default
//! `default`) and `PARALEAN_KEYS` (a key file from `keys init`). `sync` also reads the peer
//! deployment's `PARALEAN_PEER_FDB_CLUSTER`, `PARALEAN_PEER_S3_*`, `PARALEAN_PEER_DEPLOYMENT`
//! and `PARALEAN_PEER_KEYS`.

use std::collections::BTreeMap;
use std::process::ExitCode;

use paralean_store::pce::Pce;
use paralean_store::recovery::{discover, recover_catalog};
use paralean_store::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

const USAGE: &str = "usage: paralean-p2 <command> [args]
  keys init <path> [--workspaces N] [--demo]   write a key file (random seeds unless --demo)
  status                                        fence and key counts
  assign <target> <workspace>                   T4: assign/reassign a target name
  rotate <holder-workspace>                     T3: issue the next fence rank
  put <kind> <file>                             put a file as an opaque object (group|chunk|capsule)
  get <kind> <hex-id>                           verified read; writes the PCE payload to stdout
  publish-demo <workspace> <name> <tag>         publish a synthetic group (a target if <name> has a record)
  checkpoint-demo <workspace> <tag>             rotate to <workspace>, publish a group, commit a checkpoint
  discover                                      groups by certificates, heads and conflicts
  recover <workspace>                           enumerate the catalogue and select by certificates
  audit                                         whole-store invariant audit (exit 1 on violations)
  check-p1 <p1-store-root>                      offline: P2's group ID of every objects/*.grp equals P1's declId
  import-p1 <p1-store-root>                     check-p1, then upload them as group payloads (acked ID = declId)
  tombstone-demo <workspace> <group-hex>        T8: delete a group published by <workspace>
  sync <workspace> <peer-workspace>             anti-entropy with the peer deployment (PARALEAN_PEER_*) until converged
  stress --worker I --ops N --seed S [--crash-p P] [--fault-p P] [--ack-log FILE]
                                                random operations (multi-process tests); FILE gets one
                                                line per acknowledged effect
  verify-acks FILE...                           every acknowledged effect in the logs is in the store";

type R<T> = std::result::Result<T, String>;

fn keyfile() -> R<KeyFile> {
    match std::env::var("PARALEAN_KEYS") {
        Ok(p) => serde_json::from_str(&std::fs::read_to_string(&p).map_err(|e| format!("{p}: {e}"))?).map_err(|e| e.to_string()),
        Err(_) => {
            eprintln!("paralean-p2: PARALEAN_KEYS not set; using the deterministic demo key set");
            Ok(KeyFile::demo(8))
        }
    }
}

fn open(faults: std::sync::Arc<Faults>) -> R<(Store, KeyFile)> {
    let dep = std::env::var("PARALEAN_DEPLOYMENT").unwrap_or_else(|_| "default".into());
    let cfg = StoreConfig::from_env(&dep).map_err(|e| e.to_string())?;
    let kf = keyfile()?;
    let store = Store::open(&cfg, kf.ring(), faults).map_err(|e| e.to_string())?;
    Ok((store, kf))
}

fn read_keys(path: &str) -> R<KeyFile> {
    serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?).map_err(|e| e.to_string())
}

fn writer(store: &Store, kf: &KeyFile, name: &str) -> R<Writer> {
    let (id, s) = kf.workspace(name).ok_or(format!("no workspace {name} in the key file"))?;
    Ok(Writer::new(store.clone(), id, s))
}

fn controller(store: &Store, kf: &KeyFile) -> R<Controller> {
    Ok(Controller::new(store.clone(), kf.authority_signer().ok_or("key file holds no authority seed")?))
}

fn request_id() -> Vec<u8> {
    rand::random::<[u8; 16]>().to_vec()
}

/// P1 group objects of a P1 store (`objects/<declId>.grp`), each with P1's `declId` (the file
/// name), P2's group ID `H("v0/group", bytes)` of the same bytes, and the bytes.
fn p1_groups(root: &str) -> R<Vec<(String, Id, Vec<u8>)>> {
    let dir = std::path::Path::new(root).join("objects");
    let mut out = Vec::new();
    for e in std::fs::read_dir(&dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let p = e.map_err(|e| e.to_string())?.path();
        if p.extension().and_then(|x| x.to_str()) != Some("grp") {
            continue;
        }
        let p1_id = p.file_stem().and_then(|x| x.to_str()).unwrap_or_default().to_string();
        let bytes = std::fs::read(&p).map_err(|e| e.to_string())?;
        out.push((p1_id, Domain::Group.hash(&bytes), bytes));
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(out)
}

/// Print one line per P1 group and return the number whose IDs differ.
fn check_p1(groups: &[(String, Id, Vec<u8>)]) -> usize {
    let mut bad = 0;
    for (p1, p2, _) in groups {
        if *p1 == p2.hex() {
            println!("p1 {p1} = group:{}", p2.hex());
        } else {
            println!("MISMATCH p1 {p1} != group:{}", p2.hex());
            bad += 1;
        }
    }
    bad
}

fn kind(s: &str) -> R<Kind> {
    Kind::from_name(s).ok_or(format!("unknown kind {s}"))
}

#[tokio::main]
async fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(args).await {
        Ok(code) => code,
        Err(e) => {
            eprintln!("paralean-p2: {e}");
            ExitCode::from(2)
        }
    }
}

async fn run(args: Vec<String>) -> R<ExitCode> {
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    let es = |e: StoreError| e.to_string();
    match a.as_slice() {
        ["keys", "init", path, rest @ ..] => {
            let n = rest.iter().position(|x| *x == "--workspaces").and_then(|i| rest.get(i + 1)).and_then(|s| s.parse().ok()).unwrap_or(4);
            let kf = if rest.contains(&"--demo") { KeyFile::demo(n) } else { random_keys(n) };
            std::fs::write(path, serde_json::to_string_pretty(&kf).unwrap()).map_err(|e| e.to_string())?;
            println!("wrote {path} ({n} workspaces)");
        }
        ["status"] => {
            let (st, _) = open(Faults::none())?;
            println!("fence {}", st.fence().await.map_err(es)?);
            for kind in ["marker", "cert", "revision", "receipt", "target", "catalog", "rcert", "ocert", "token", "tombstone", "tcert", "xcert"] {
                let n = st.meta.scan(&st.meta.keys.sub(kind), 10_000, |_| None).await.map_err(es)?.len();
                println!("{kind:9} {n}");
            }
        }
        ["assign", target, ws] => {
            let (st, kf) = open(Faults::none())?;
            let (id, _) = kf.workspace(ws).ok_or("unknown workspace")?;
            let ep = controller(&st, &kf)?.reassign(&Name::parse(target), id, &request_id()).await.map_err(es)?;
            println!("{target}: owner {ws}, epoch {ep}");
        }
        ["rotate", ws] => {
            let (st, kf) = open(Faults::none())?;
            let (id, _) = kf.workspace(ws).ok_or("unknown workspace")?;
            let t = controller(&st, &kf)?.rotate(id, &request_id()).await.map_err(es)?;
            println!("rank {} issued to {ws}", t.rank);
        }
        ["put", k, file] => {
            let (st, _) = open(Faults::none())?;
            let bytes = std::fs::read(file).map_err(|e| e.to_string())?;
            let o = Opaque::new(kind(k)?, bytes);
            let ack = st.s3.put_opaque(&o).await.map_err(es)?;
            println!("{}:{}", k, ack.id().hex());
        }
        ["get", k, id] => {
            let (st, _) = open(Faults::none())?;
            let kd = kind(k)?;
            let id = Id::from_hex(id).ok_or("bad id")?;
            match st.s3.get(kd, &id).await.map_err(es)? {
                None => return Err("absent or failed verification".into()),
                Some(b) => {
                    use std::io::Write;
                    std::io::stdout().write_all(kd.domain().strip(&b).map_err(|e| e.to_string())?).unwrap();
                }
            }
        }
        ["publish-demo", ws, name, tag] => {
            let (st, kf) = open(Faults::none())?;
            let w = writer(&st, &kf, ws)?;
            let name = Name::parse(name);
            let v = kf.validator_signer("v0").ok_or("no validator seed")?;
            let pt = match st.target(&name).await.map_err(es)? {
                Some(_) => Some(w.prepare_target(&name).await.map_err(es)?),
                None => None,
            };
            let parents = pt.as_ref().and_then(|t| t.head).into_iter().collect();
            let p = fixture::package(tag, w.id, &v, &name, parents, pt, 1);
            let o = w.publish(&p).await.map_err(es)?;
            println!("published group {} marker {} (fresh: {})", p.group.id(), o.marker, o.fresh);
        }
        ["checkpoint-demo", ws, tag] => {
            let (st, kf) = open(Faults::none())?;
            let w = writer(&st, &kf, ws)?;
            let v = kf.validator_signer("v0").ok_or("no validator seed")?;
            let tok = controller(&st, &kf)?.rotate(w.id, &request_id()).await.map_err(es)?;
            let p = fixture::package(tag, w.id, &v, &Name::parse(&format!("Demo.{tag}")), vec![], None, 1);
            w.publish(&p).await.map_err(es)?;
            let pred = recover_catalog(&st, w.id).await.map_err(es)?.selected;
            let cp = fixture::checkpoint(w.id, vec![p.revisions[0].id()], pred, tok, tag);
            let c = w.commit_checkpoint(&cp).await.map_err(es)?;
            println!("committed record {c} (rank {}, predecessor {pred:?})", tok.rank);
        }
        ["discover"] => {
            let (st, _) = open(Faults::none())?;
            let d = discover(&st).await.map_err(es)?;
            println!("{} published groups, {} ignored markers, {} dangling certificates", d.groups.len(), d.ignored_markers.len(), d.dangling_certs);
            println!("{} tombstones, {} ignored tombstones", d.tombstones.len(), d.ignored_tombstones.len());
            for (n, h) in &d.heads {
                println!("  {n}: {} head(s) {:?}", h.len(), h);
            }
            for (f, seq) in &d.files {
                println!("  file {f}: {seq:?}");
            }
            if !d.conflicts.is_empty() {
                println!("conflicts: {:?}", d.conflicts);
            }
        }
        ["recover", ws] => {
            let (st, kf) = open(Faults::none())?;
            let (id, _) = kf.workspace(ws).ok_or("unknown workspace")?;
            let r = recover_catalog(&st, id).await.map_err(es)?;
            for (c, s) in &r.records {
                if s.record.workspace == id {
                    println!("  {c:?} rank {} admissible {} {:?}", s.record.token.rank, s.admissible, s.reasons);
                }
            }
            println!("heads {:?}; selected {:?}", r.heads, r.selected);
        }
        ["audit"] => {
            let (st, _) = open(Faults::none())?;
            let r = audit::audit(&st).await.map_err(es)?;
            for (k, v) in &r.counts {
                println!("{k:18} {v}");
            }
            println!("uncertified markers {}", r.uncertified_markers.len());
            if !r.ok() {
                for v in &r.violations {
                    println!("VIOLATION {v}");
                }
                return Ok(ExitCode::from(1));
            }
            println!("audit ok");
        }
        ["check-p1", root] => {
            let groups = p1_groups(root)?;
            let bad = check_p1(&groups);
            println!("{} groups, {} with P1 declId = P2 group ID, {bad} mismatches", groups.len(), groups.len() - bad);
            if bad > 0 || groups.is_empty() {
                return Ok(ExitCode::from(1));
            }
        }
        ["import-p1", root] => {
            let groups = p1_groups(root)?;
            let bad = check_p1(&groups);
            if bad > 0 {
                println!("{bad} mismatches; nothing imported");
                return Ok(ExitCode::from(1));
            }
            let (st, _) = open(Faults::none())?;
            for (p1, _, bytes) in groups.iter() {
                let ack = st.s3.put_opaque(&Opaque::new(Kind::Group, bytes.clone())).await.map_err(es)?;
                if ack.id().hex() != *p1 {
                    println!("MISMATCH acked group:{} for p1 {p1}", ack.id().hex());
                    return Ok(ExitCode::from(1));
                }
            }
            println!("imported {} groups; every acknowledged group ID equals P1's declId", groups.len());
        }
        ["tombstone-demo", ws, g] => {
            let (st, kf) = open(Faults::none())?;
            let w = writer(&st, &kf, ws)?;
            let g = Id::from_hex(g).ok_or("bad group id")?;
            let (_, m) = st.marker(&g).await.map_err(es)?.ok_or("group not published")?;
            let t = fixture::tombstone_of(&m, m.lamport + 1);
            let fresh = w.tombstone(&t).await.map_err(es)?;
            println!("tombstone {} of {g} (fresh: {fresh})", t.id());
        }
        ["sync", ws, peer_ws] => {
            let own = keyfile()?;
            let peer_keys = read_keys(&std::env::var("PARALEAN_PEER_KEYS").map_err(|_| "PARALEAN_PEER_KEYS not set")?)?;
            let dep = std::env::var("PARALEAN_DEPLOYMENT").unwrap_or_else(|_| "default".into());
            let peer_dep = std::env::var("PARALEAN_PEER_DEPLOYMENT").unwrap_or_else(|_| dep.clone());
            let (mut ra, mut rb) = (own.ring(), peer_keys.ring());
            ra.trust(&peer_keys.ring());
            rb.trust(&own.ring());
            let a = Store::open(&StoreConfig::from_env(&dep).map_err(es)?, ra, Faults::none()).map_err(es)?;
            let b = Store::open(&StoreConfig::from_env_with("PARALEAN_PEER_", &peer_dep).map_err(es)?, rb, Faults::none()).map_err(es)?;
            let wa = writer(&a, &own, ws)?;
            let wb = writer(&b, &peer_keys, peer_ws)?;
            let (rounds, ab, ba) = antientropy::sync((&a, &wa), (&b, &wb), 20).await.map_err(es)?;
            let (pa, pb) = (antientropy::published_set(&a).await.map_err(es)?, antientropy::published_set(&b).await.map_err(es)?);
            println!("{rounds} rounds; last round: to peer {ab:?}, from peer {ba:?}");
            println!("groups {} / {}, tombstones {} / {}; converged: {}", pa.groups.len(), pb.groups.len(), pa.tombstones.len(), pb.tombstones.len(), pa == pb);
            if pa != pb {
                return Ok(ExitCode::from(1));
            }
        }
        ["verify-acks", files @ ..] => return verify_acks(files).await,
        ["stress", rest @ ..] => return stress(rest).await,
        _ => {
            eprintln!("{USAGE}");
            return Ok(ExitCode::from(2));
        }
    }
    Ok(ExitCode::SUCCESS)
}

fn random_keys(n: usize) -> KeyFile {
    let auth = Signer::generate();
    let val = Signer::generate();
    let mut kf = KeyFile {
        authority: Some(hex::encode(auth.seed())),
        authority_public: hex::encode(auth.public()),
        ..Default::default()
    };
    kf.validators.insert(
        "v0".into(),
        sign::KeyEntry { id: String::new(), public: hex::encode(val.public()), seed: Some(hex::encode(val.seed())) },
    );
    for i in 0..n {
        let s = Signer::generate();
        kf.workspaces.insert(
            format!("w{i}"),
            sign::KeyEntry { id: WorkspaceId::random().hex(), public: hex::encode(s.public()), seed: Some(hex::encode(s.seed())) },
        );
    }
    kf
}

/// Random operations by one worker process. Guard failures are expected (the workers
/// race); any other error, or an unresolved outcome, exits with status 3. Injected crashes
/// abort the process (a real crash).
async fn stress(rest: &[&str]) -> R<ExitCode> {
    let flag = |k: &str| rest.iter().position(|x| *x == k).and_then(|i| rest.get(i + 1)).copied();
    let wi: usize = flag("--worker").ok_or("--worker")?.parse().map_err(|_| "--worker")?;
    let ops: usize = flag("--ops").unwrap_or("50").parse().map_err(|_| "--ops")?;
    let seed: u64 = flag("--seed").unwrap_or("1").parse().map_err(|_| "--seed")?;
    let crash_p: f64 = flag("--crash-p").unwrap_or("0").parse().map_err(|_| "--crash-p")?;
    let fault_p: f64 = flag("--fault-p").unwrap_or("0").parse().map_err(|_| "--fault-p")?;
    let mut ack_log = match flag("--ack-log") {
        Some(p) => Some(std::fs::OpenOptions::new().create(true).append(true).open(p).map_err(|e| format!("{p}: {e}"))?),
        None => None,
    };
    let mut cfg = RandomFaults::no_crash(fault_p);
    cfg.p_crash_point = crash_p;
    cfg.p_crash_commit = crash_p;
    let faults = Faults::random(seed, cfg, CrashMode::Abort);
    let (st, kf) = open(faults.clone())?;
    let nw = kf.workspaces.len();
    let me = writer(&st, &kf, &format!("w{wi}"))?;
    let ctl = controller(&st, &kf)?;
    let v = kf.validator_signer("v0").ok_or("no validator")?;
    let mut rng = StdRng::seed_from_u64(seed ^ 0x9e37_79b9);
    let targets: Vec<Name> = (0..3).map(|i| Name::parse(&format!("Stress.t{i}"))).collect();
    let mut mine: Vec<Id> = Vec::new();
    let mut free: Vec<Marker> = Vec::new();
    let mut last_commit: Option<Id> = None;
    let mut acks: Vec<String> = Vec::new();
    let mut outcomes: BTreeMap<String, u64> = BTreeMap::new();
    for op in 0..ops {
        let tag = format!("w{wi}-s{seed}-op{op}");
        let choice = rng.gen_range(0..11);
        let r: Result<String> = async {
            match choice {
                0..=2 => {
                    let p = fixture::package(&tag, me.id, &v, &Name::parse(&format!("Stress.free.{tag}")), vec![], None, op as u64);
                    let o = me.publish(&p).await?;
                    mine.push(p.revisions[0].id());
                    free.push(p.marker.clone());
                    acks.push(format!("group {} {}", p.group.id(), o.marker));
                    Ok("publish-free".into())
                }
                3..=5 => {
                    let t = &targets[rng.gen_range(0..targets.len())];
                    if st.target(t).await?.is_none() {
                        ctl.reassign(t, me.id, format!("init-{t}").as_bytes()).await?;
                    }
                    let pt = me.prepare_target(t).await?;
                    let parents = pt.head.into_iter().collect();
                    let p = fixture::package(&tag, me.id, &v, t, parents, Some(pt), op as u64);
                    let o = me.publish(&p).await?;
                    acks.push(format!("group {} {}", p.group.id(), o.marker));
                    Ok("publish-target".into())
                }
                6 => {
                    let t = &targets[rng.gen_range(0..targets.len())];
                    let to = rng.gen_range(0..nw);
                    let (id, _) = kf.workspace(&format!("w{to}")).unwrap();
                    let ep = ctl.reassign(t, id, &rand::random::<[u8; 16]>()).await?;
                    acks.push(format!("assign {} {ep} {}", hex::encode(t.to_pce()), id.hex()));
                    Ok("reassign".into())
                }
                10 => {
                    let Some(m) = free.pop() else { return Ok("skip".into()) };
                    let t = fixture::tombstone_of(&m, 10_000 + op as u64);
                    me.tombstone(&t).await?;
                    acks.push(format!("tombstone {}", t.id()));
                    Ok("tombstone".into())
                }
                _ => {
                    if mine.is_empty() {
                        return Ok("skip".into());
                    }
                    let tok = ctl.rotate(me.id, &rand::random::<[u8; 16]>()).await?;
                    acks.push(format!("rank {} {}", tok.rank, tok.holder.hex()));
                    let k = rng.gen_range(1..=mine.len().min(3));
                    let contents: Vec<Id> = mine.iter().rev().take(k).copied().collect();
                    let cp = fixture::checkpoint(me.id, contents, last_commit, tok, &tag);
                    let c = me.commit_checkpoint(&cp).await?;
                    acks.push(format!("record {c}"));
                    last_commit = Some(c);
                    Ok("checkpoint".into())
                }
            }
        }
        .await;
        // Every effect a call returned as done is logged before the next operation.
        if let Some(f) = ack_log.as_mut() {
            use std::io::Write;
            for a in acks.drain(..) {
                writeln!(f, "{a}").map_err(|e| e.to_string())?;
            }
            f.flush().map_err(|e| e.to_string())?;
        }
        acks.clear();
        match r {
            Ok(s) => *outcomes.entry(s).or_default() += 1,
            Err(StoreError::Guard(g)) => {
                let s = format!("{g:?}");
                *outcomes.entry(format!("guard:{}", s.split(['(', ' ', '{']).next().unwrap_or(""))).or_default() += 1;
            }
            Err(e) => {
                eprintln!("worker {wi}: unexpected error at op {op}: {e}");
                return Ok(ExitCode::from(3));
            }
        }
    }
    println!("worker {wi}: {outcomes:?} faults {:?}", faults.stats());
    Ok(ExitCode::SUCCESS)
}

/// Check that every effect a stress worker saw acknowledged is in the store: published and
/// certified groups (with the acknowledged marker, payload in S3), committed records with a
/// valid commit certificate, certified tombstones, issued ranks and assignments.
async fn verify_acks(files: &[&str]) -> R<ExitCode> {
    let (st, _) = open(Faults::none())?;
    let es = |e: StoreError| e.to_string();
    let (mut ok, mut lost) = (BTreeMap::<String, u64>::new(), Vec::new());
    for f in files {
        for line in std::fs::read_to_string(f).map_err(|e| format!("{f}: {e}"))?.lines() {
            let w: Vec<&str> = line.split_whitespace().collect();
            let id = |i: usize| w.get(i).and_then(|s| Id::from_hex(s)).ok_or(format!("bad line {line}"));
            let present = match w.first().copied() {
                Some("group") => {
                    let (g, m) = (id(1)?, id(2)?);
                    st.marker(&g).await.map_err(es)?.is_some_and(|(mid, _)| mid == m)
                        && st.certs(&g).await.map_err(es)?.iter().any(|c| c.body.marker == m)
                        && st.s3.get(Kind::Group, &g).await.map_err(es)?.is_some()
                }
                Some("record") => {
                    let c = id(1)?;
                    match st.record(&c).await.map_err(es)? {
                        Some(r) => st.valid_rcert(&c, &r.body).await.map_err(es)?.is_some(),
                        None => false,
                    }
                }
                Some("tombstone") => {
                    let t = id(1)?;
                    st.tombstone(&t).await.map_err(es)?.is_some() && !st.tcerts(&t).await.map_err(es)?.is_empty()
                }
                Some("rank") => {
                    let rank: u64 = w.get(1).and_then(|s| s.parse().ok()).ok_or(format!("bad line {line}"))?;
                    st.token(rank).await.map_err(es)?.is_some_and(|e| Some(e.token.body.token.holder.hex()) == w.get(2).map(|s| s.to_string()))
                }
                Some("assign") => {
                    let name = Name::from_pce(&hex::decode(w.get(1).ok_or("bad line")?).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
                    let epoch: u64 = w.get(2).and_then(|s| s.parse().ok()).ok_or(format!("bad line {line}"))?;
                    let v = st.meta.get(st.meta.keys.assign(&name, epoch)).await.map_err(es)?;
                    v.and_then(|v| AssignEntry::from_pce(&v).ok()).is_some_and(|e| Some(e.owner.hex()) == w.get(3).map(|s| s.to_string()))
                }
                _ => return Err(format!("bad line {line}")),
            };
            if present {
                *ok.entry(w[0].to_string()).or_default() += 1;
            } else {
                lost.push(line.to_string());
            }
        }
    }
    println!("acknowledged effects present: {ok:?}; lost: {}", lost.len());
    for l in &lost {
        println!("LOST {l}");
    }
    Ok(if lost.is_empty() { ExitCode::SUCCESS } else { ExitCode::from(1) })
}
