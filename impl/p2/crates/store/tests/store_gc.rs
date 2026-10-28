//! Store GC (docs/w4-rest-log.md, Design 1) against the live private cluster. Every test
//! runs its own deployment behind its own s3-guard process started with
//! `--gc-fdb-cluster` and `--gc-deployment` for that deployment only, with a GC principal
//! imported into Garage for this test process (deleted again at exit).
//!
//! Build the gateway first (`cargo build -p s3-guard`); run with `--test-threads=1` on a
//! private `w4r-*` instance (`source impl/p3/scripts/w4r-env.sh`).
#![deny(dead_code)]

mod common;

use std::collections::BTreeMap;
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, OnceLock};
use std::time::{Duration, Instant};

use common::*;
use paralean_store::ae::{AeEvent, AeKind, AePart, AePending, PendingState};
use paralean_store::antientropy::Outcome;
use paralean_store::faults::{CommitFault, Txn};
use paralean_store::gc::{self, GcConfig, GcState};
use paralean_store::recovery::{discover, recover_catalog};
use paralean_store::*;

// ------------------------------------------------------------------ harness

struct GcKey {
    access: String,
    secret: String,
}

static GC_KEY: OnceLock<GcKey> = OnceLock::new();

fn env(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("{name} not set: source impl/p3/scripts/w4r-env.sh"))
}

fn garage(args: &[&str]) {
    let bin = format!("{}/bin/garage", env("PARALEAN_P2_PREFIX"));
    let config = format!("{}/garage/n0/garage.toml", env("PARALEAN_HOME"));
    let out = Command::new(bin).arg("-c").arg(config).args(args).output().expect("run garage");
    assert!(out.status.success(), "garage {args:?}: {}", String::from_utf8_lossy(&out.stderr));
}

fn hex_random(n: usize) -> String {
    use std::io::Read;
    let mut b = vec![0u8; n];
    std::fs::File::open("/dev/urandom").unwrap().read_exact(&mut b).unwrap();
    b.iter().map(|x| format!("{:x}", x & 0xf)).collect()
}

/// The GC principal of this test process: a fresh Garage key with read/write on the bucket.
fn gc_key() -> &'static GcKey {
    GC_KEY.get_or_init(|| {
        assert!(env("PARALEAN_INSTANCE").starts_with("w4r-"), "store GC tests run only on a private w4r-* instance");
        let key = GcKey { access: format!("GK{}", hex_random(24)), secret: hex_random(64) };
        garage(&["key", "import", "--yes", "-n", "w4r-store-gc-test", &key.access, &key.secret]);
        garage(&["bucket", "allow", "--read", "--write", &env("PARALEAN_S3_BUCKET"), "--key", &key.access]);
        key
    })
}

/// A private s3-guard process with store-GC content deletes for the given deployments.
struct Guard {
    child: Child,
    endpoint: String,
}

impl Drop for Guard {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

fn guard_for(deployments: &[&str]) -> Guard {
    let bin = concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/debug/s3-guard");
    assert!(std::path::Path::new(bin).exists(), "build the gateway first: cargo build -p s3-guard");
    let port = std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port();
    let mut cmd = Command::new(bin);
    cmd.args(["--listen", &format!("127.0.0.1:{port}"), "--upstream", &format!("unix:{}", env("PARALEAN_GARAGE_S3_SOCKET"))])
        .args(["--gc-access-key", &gc_key().access, "--gc-fdb-cluster", &env("PARALEAN_FDB_CLUSTER")]);
    for d in deployments {
        cmd.args(["--gc-deployment", &format!("{d}={}/{d}/", env("PARALEAN_S3_BUCKET"))]);
    }
    let log = std::fs::OpenOptions::new().create(true).append(true)
        .open(concat!(env!("CARGO_MANIFEST_DIR"), "/../../target/store-gc-guard.log")).unwrap();
    let child = cmd.stdout(Stdio::null()).stderr(log).spawn().expect("start s3-guard");
    let deadline = Instant::now() + Duration::from_secs(10);
    while std::net::TcpStream::connect(("127.0.0.1", port)).is_err() {
        assert!(Instant::now() < deadline, "s3-guard did not start");
        std::thread::sleep(Duration::from_millis(20));
    }
    Guard { child, endpoint: format!("http://127.0.0.1:{port}") }
}

/// A deployment whose writers and collector use their own FDB-aware gateway.
struct Gc {
    e: Env,
    gc_s3: s3::Payloads,
    guard: Guard,
}

fn s3_with(cfg: &StoreConfig, endpoint: &str, access: &str, secret: &str) -> s3::Payloads {
    let mut c = cfg.s3.clone();
    c.endpoint = endpoint.to_string();
    c.access_key = access.to_string();
    c.secret_key = secret.to_string();
    s3::Payloads::new(&c, Faults::none())
}

fn gc_env_with(name: &str, n: usize, faults: Arc<Faults>, kf: KeyFile, peer: Option<&KeyRing>) -> Gc {
    let mut cfg = StoreConfig::from_env(&deployment(name)).expect("PARALEAN_* not set");
    let guard = guard_for(&[&cfg.deployment]);
    cfg.s3.endpoint = guard.endpoint.clone();
    let e = Env::open_keys(cfg, kf, n, faults, peer);
    let gc_s3 = s3_with(&e.cfg, &guard.endpoint, &gc_key().access, &gc_key().secret);
    Gc { e, gc_s3, guard }
}

fn gc_env(name: &str, n: usize) -> Gc {
    gc_env_with(name, n, Faults::none(), KeyFile::demo(n.max(1)), None)
}

async fn enable(st: &Store) -> GcReport {
    let r = gc::backfill(st).await.unwrap();
    gc::enable(st).await.unwrap();
    r
}

async fn sweep(st: &Store, grace: u64) -> GcReport {
    gc::sweep(st, &GcConfig { grace }).await.unwrap()
}

async fn sweeps(st: &Store, grace: u64, n: usize) -> u64 {
    let mut doomed = 0;
    for _ in 0..n {
        doomed += sweep(st, grace).await.doomed;
    }
    doomed
}

async fn present(st: &Store, kind: Kind, id: &Id) -> bool {
    st.s3.get(kind, id).await.unwrap().is_some()
}

async fn state(st: &Store, kind: Kind, id: &Id) -> Option<GcState> {
    st.gc_state(kind, id).await.unwrap()
}

fn is_doomed(s: Option<GcState>) -> bool {
    matches!(s, Some(GcState::Doomed { .. } | GcState::Deleting { .. }))
}

/// Every payload object a published package names (not its fixture chunk, which no
/// metadata names unless the group is a chunked P1 group).
fn package_objects(p: &Package) -> Vec<(Kind, Id)> {
    vec![(Kind::Group, p.group.id()), (Kind::Capsule, p.capsule.id()), (Kind::StagedMarker, p.marker.id())]
}

async fn put_package_payloads(st: &Store, p: &Package) {
    for c in &p.chunks {
        st.s3.put_opaque(c).await.unwrap();
    }
    st.s3.put_opaque(&p.group).await.unwrap();
    st.s3.put_opaque(&p.capsule).await.unwrap();
    st.s3.put(Kind::StagedMarker, &p.marker.preimage()).await.unwrap();
}

async fn assert_all_present(st: &Store, objects: &[(Kind, Id)], what: &str) {
    for (kind, id) in objects {
        assert!(present(st, *kind, id).await, "{what}: {} {id} was collected", kind.name());
        assert!(!state(st, *kind, id).await.is_some_and(|s| s.retired()), "{what}: {} {id} is being collected", kind.name());
    }
}

async fn put_orphan(st: &Store, tag: &str) -> Id {
    st.s3.put_opaque(&Opaque::new(Kind::Group, fixture::group_bytes(tag))).await.unwrap().id()
}

async fn ref_count(st: &Store, kind: Kind, id: &Id) -> usize {
    st.meta.scan(&st.meta.keys.gcrefs_of(kind, id), 100, |_| None).await.unwrap().len()
}

async fn raw_clear(st: &Store, key: Vec<u8>) {
    let mut trx = st.meta.db.create_trx().unwrap();
    loop {
        trx.clear(&key);
        match trx.commit().await {
            Ok(_) => return,
            Err(e) => trx = e.on_error().await.unwrap(),
        }
    }
}

// ------------------------------------------------------------------ disabled by default

/// References are maintained from the start, but nothing is collected without `enable`:
/// sweeps refuse to run and the gateway refuses the GC principal's content deletes.
#[tokio::main(flavor = "current_thread")]
async fn gc_disabled_by_default_collects_nothing() {
    let g = gc_env("gcoff", 1);
    let e = &g.e;
    let p = e.plain_package(0, "Gc.Off", "gcoff");
    e.w[0].publish(&p).await.unwrap();
    let orphan = put_orphan(&e.store, "gcoff-orphan").await;
    let err = gc::sweep(&e.store, &GcConfig::default()).await.unwrap_err();
    assert!(err.to_string().contains("not enabled"), "{err}");
    assert!(gc::delete_doomed(&e.store, &g.gc_s3).await.is_err());
    assert!(gc::enable(&e.store).await.is_err(), "enable needs a completed backfill");
    // The index is complete without any backfill: the published marker names its objects.
    for (kind, id) in package_objects(&p) {
        assert_eq!(ref_count(&e.store, kind, &id).await, 1, "{} has one reference from its marker", kind.name());
    }
    // No GC state anywhere, and the gateway refuses to delete an unmarked object.
    assert!(gc::status(&e.store).await.unwrap().states.is_empty());
    assert!(g.gc_s3.try_delete(Kind::Group, &orphan).await.is_err());
    assert!(present(&e.store, Kind::Group, &orphan).await);
    // The cluster's own gateway (no store-GC flags) refuses every content delete too.
    let plain = StoreConfig::from_env(&e.store.deployment).unwrap();
    let via_default = s3_with(&plain, &plain.s3.endpoint, &gc_key().access, &gc_key().secret);
    assert!(via_default.try_delete(Kind::Group, &orphan).await.is_err());
    assert!(present(&e.store, Kind::Group, &orphan).await);
    e.audit_ok().await;
}

// ------------------------------------------------------------------ staging garbage

/// Backfill + sweeps collect exactly the staging garbage (an abandoned T1's payloads, an
/// aborted checkpoint's snapshot and manifests, orphan blobs), and only after the grace
/// period; the published group stays. Listing pages of two exercise S3 pagination.
#[tokio::main(flavor = "current_thread")]
async fn gc_collects_staged_orphans_only_after_grace() {
    let g = gc_env("orphans", 1);
    let e = &g.e;
    let mut st = e.store.clone();
    st.s3.list_page = 2;
    let p = e.plain_package(0, "Gc.Kept", "kept");
    e.w[0].publish(&p).await.unwrap();
    // An abandoned publication: payloads and staged marker, never T1.
    let abandoned = e.plain_package(0, "Gc.Abandoned", "abandoned");
    put_package_payloads(&st, &abandoned).await;
    // An aborted checkpoint: manifests and snapshot (certified), never T5.
    let token = e.ctl.rotate(e.w[0].id, b"rank-1").await.unwrap();
    let cp = fixture::checkpoint(e.w[0].id, vec![rev_id(&p)], None, token, "aborted");
    let snap = prepare_snapshot(e, 0, &cp).await;
    let mut orphans = package_objects(&abandoned);
    for i in 0..3 {
        let blob = st.s3.put_opaque(&Opaque::new(Kind::Blob, format!("orphan blob {i}").into_bytes())).await.unwrap().id();
        orphans.push((Kind::Blob, blob));
    }
    orphans.extend(abandoned.chunks.iter().chain(&p.chunks).map(|c| (Kind::Chunk, c.id())));
    orphans.extend([(Kind::Snapshot, snap), (Kind::Manifest, cp.source_root.id()), (Kind::Manifest, cp.build_receipt.id())]);
    let mut orphan_bytes = 0;
    for (kind, id) in &orphans {
        orphan_bytes += st.s3.get(*kind, id).await.unwrap().unwrap().len() as u64;
    }
    let backfill = enable(&st).await;
    assert!(backfill.referrers >= 1 && backfill.anomalies.is_empty(), "{backfill:?}");
    let r1 = sweep(&st, 2).await;
    assert_eq!((r1.sighted, r1.doomed), (orphans.len() as u64, 0), "first pass only sights: {r1:?}");
    assert!(r1.listing_pages > Kind::S3_KINDS.len() as u64, "paginated listing: {r1:?}");
    let r2 = sweep(&st, 2).await;
    assert_eq!(r2.doomed, 0, "one tick is inside the grace period: {r2:?}");
    for (kind, id) in &orphans {
        assert!(matches!(state(&st, *kind, id).await, Some(GcState::Sighted { .. })), "{} {id}", kind.name());
    }
    let r3 = sweep(&st, 2).await;
    assert_eq!(r3.doomed, orphans.len() as u64, "{r3:?}");
    assert!(st.valid_ocert(Kind::Snapshot, &snap).await.unwrap().is_none(), "a doom clears the object certificate");
    let d = gc::delete_doomed(&st, &g.gc_s3).await.unwrap();
    assert_eq!((d.deleted, d.reclaimed_bytes, d.delete_failures), (orphans.len() as u64, orphan_bytes, 0), "{d:?}");
    for (kind, id) in &orphans {
        assert!(!present(&st, *kind, id).await, "{} {id} survived", kind.name());
        assert!(matches!(state(&st, *kind, id).await, Some(GcState::Gone { .. })));
    }
    assert_all_present(&st, &package_objects(&p), "published group").await;
    let r4 = sweep(&st, 2).await;
    assert_eq!((r4.doomed, r4.sighted, r4.pending_delete), (0, 0, 0), "{r4:?}");
    e.audit_ok().await;
}

// ------------------------------------------------------------------ roots

/// Published groups, revised ancestors, tombstoned and moved positions and committed
/// checkpoints are roots: never collected, whatever the grace.
#[tokio::main(flavor = "current_thread")]
async fn gc_never_collects_published_tombstoned_moved_or_revised() {
    let g = gc_env("roots", 1);
    let e = &g.e;
    let x = Name::parse("Gc.Target");
    e.ctl.reassign(&x, e.w[0].id, b"assign-gc").await.unwrap();
    let (p1, _) = e.publish_target(0, &x, "rev-1").await.unwrap();
    let p2 = e.prepare(0, &x, "rev-2", 2).await.unwrap();
    e.w[0].publish(&p2).await.unwrap();
    assert_eq!(e.store.target(&x).await.unwrap().unwrap().head, Some(rev_id(&p2)), "p1 is a revised ancestor");
    let q = e.plain_package(0, "Gc.Moved", "moved");
    e.w[0].publish(&q).await.unwrap();
    let t = fixture::tombstone_of(&q.marker, 2);
    e.w[0].tombstone(&t).await.unwrap();
    let mut moved = q.marker.clone();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, 3, moved.author)];
    e.w[0].move_position(&moved, &t).await.unwrap();
    let token = e.ctl.rotate(e.w[0].id, b"rank-1").await.unwrap();
    let cp = one_snapshot(e, 0, "root-cp", token, None).await;
    let c = e.w[0].commit_checkpoint(&cp).await.unwrap();
    let orphan = put_orphan(&e.store, "roots-orphan").await;
    enable(&e.store).await;
    sweeps(&e.store, 1, 3).await;
    let d = gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert!(d.deleted >= 1 && !present(&e.store, Kind::Group, &orphan).await, "{d:?}");
    let mut roots = Vec::new();
    for p in [&p1, &p2, &q] {
        roots.extend(package_objects(p));
    }
    roots.extend([(Kind::StagedMarker, moved.id()), (Kind::StagedTombstone, t.id()), (Kind::Snapshot, cp.snapshot.id()),
        (Kind::Manifest, cp.source_root.id()), (Kind::Manifest, cp.build_receipt.id())]);
    assert_all_present(&e.store, &roots, "root").await;
    assert!(e.store.valid_ocert(Kind::Snapshot, &cp.snapshot.id()).await.unwrap().is_some());
    let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
    assert_eq!(r.selected, Some(c));
    let found = discover(&e.store).await.unwrap();
    assert!(found.positions.keys().any(|(g, _)| *g == q.group.id()));
    e.audit_ok().await;
}

// ------------------------------------------------------------------ T1 against a doom

fn doom_hook(st: &Store, gc_s3: &s3::Payloads, delete_now: bool, done: Arc<tokio::sync::Notify>) -> faults::Hook {
    let (st, gc_s3) = (st.clone(), gc_s3.clone());
    Arc::new(move || {
        let (st, gc_s3, done) = (st.clone(), gc_s3.clone(), done.clone());
        Box::pin(async move {
            // T1 has read its object states and written its references, uncommitted: the
            // doom sees no reference and commits first (grace 0: sight, then doom).
            sweeps(&st, 0, 2).await;
            if delete_now {
                gc::delete_doomed(&st, &gc_s3).await.unwrap();
                done.notify_one();
            } else {
                tokio::spawn(async move {
                    tokio::time::sleep(Duration::from_millis(300)).await;
                    gc::delete_doomed(&st, &gc_s3).await.unwrap();
                    done.notify_one();
                });
            }
        })
    })
}

/// T1 and a doom race in both orders and neither leaves a dangling reference: a reference
/// committed first stops the doom; a doom committed first makes T1 refuse (`Collected`),
/// wait for `Gone`, re-PUT and retry (the revival path), both while the delete is in flight
/// and after it completed.
#[tokio::main(flavor = "current_thread")]
async fn gc_t1_doom_race_both_orders() {
    let faults = Faults::none();
    let g = gc_env_with("t1race", 1, faults.clone(), KeyFile::demo(1), None);
    let e = &g.e;
    enable(&e.store).await;
    // Reference first: the doom transaction sees the reference and leaves the objects.
    let a = e.plain_package(0, "Gc.RaceA", "race-a");
    e.w[0].publish(&a).await.unwrap();
    sweeps(&e.store, 0, 3).await;
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert_all_present(&e.store, &package_objects(&a), "reference first").await;
    // Doom first: the delete in flight when T1 retries, then completed before it.
    for (tag, delete_now) in [("race-doomed", false), ("race-gone", true)] {
        let p = e.plain_package(0, &format!("Gc.{tag}"), tag);
        let before = faults.stats().get("gc-revived").copied().unwrap_or(0);
        let done = Arc::new(tokio::sync::Notify::new());
        faults.on_commit(Some(Txn::T1Publish), 0, CommitFault::Interleave(doom_hook(&e.store, &g.gc_s3, delete_now, done.clone())));
        let out = e.w[0].publish(&p).await.unwrap();
        assert!(out.fresh, "{tag}");
        let _ = tokio::time::timeout(Duration::from_secs(30), done.notified()).await;
        // Whatever the delete did, the committed marker's objects are present.
        assert_all_present(&e.store, &package_objects(&p), tag).await;
        assert!(faults.stats().get("gc-revived").copied().unwrap_or(0) > before, "{tag}: the writer revived");
    }
    sweeps(&e.store, 0, 2).await;
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    e.audit_ok().await;
}

/// A collected orphan can be published later: the gateway refuses a PUT under the doomed
/// key; after `Gone` the writer's PUT lands, T1 refuses the gone object, the writer revives
/// it and T1 commits.
#[tokio::main(flavor = "current_thread")]
async fn gc_revival_after_gone() {
    let faults = Faults::none();
    let g = gc_env_with("revive", 1, faults.clone(), KeyFile::demo(1), None);
    let e = &g.e;
    let p = e.plain_package(0, "Gc.Revived", "revived");
    put_package_payloads(&e.store, &p).await;
    enable(&e.store).await;
    sweeps(&e.store, 1, 2).await;
    for (kind, id) in package_objects(&p) {
        assert!(is_doomed(state(&e.store, kind, &id).await), "{}", kind.name());
    }
    let err = e.store.s3.put(Kind::Group, &p.group.preimage()).await.unwrap_err();
    assert!(err.to_string().contains("AccessDenied"), "{err}");
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert!(!present(&e.store, Kind::Group, &p.group.id()).await);
    let before = faults.stats().get("gc-revived").copied().unwrap_or(0);
    e.w[0].publish(&p).await.unwrap();
    assert!(faults.stats().get("gc-revived").copied().unwrap_or(0) > before);
    assert_all_present(&e.store, &package_objects(&p), "revived").await;
    sweeps(&e.store, 1, 3).await;
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert_all_present(&e.store, &package_objects(&p), "revived and referenced").await;
    e.audit_ok().await;
}

// ------------------------------------------------------------------ T5 / T6

/// An aborted checkpoint's snapshot is collected: the doom clears its object certificate,
/// T6 refuses to certify it and T5 refuses a record over it. A full retry of the checkpoint
/// after the delete revives the snapshot and commits.
#[tokio::main(flavor = "current_thread")]
async fn gc_t5_t6_refuse_a_doomed_snapshot() {
    let g = gc_env("t5doom", 1);
    let e = &g.e;
    let token = e.ctl.rotate(e.w[0].id, b"rank-1").await.unwrap();
    let cp = one_snapshot(e, 0, "t5doom", token, None).await;
    let snap = prepare_snapshot(e, 0, &cp).await;
    assert!(e.store.valid_ocert(Kind::Snapshot, &snap).await.unwrap().is_some());
    enable(&e.store).await;
    sweeps(&e.store, 1, 2).await;
    assert!(is_doomed(state(&e.store, Kind::Snapshot, &snap).await));
    assert!(e.store.valid_ocert(Kind::Snapshot, &snap).await.unwrap().is_none(), "the doom cleared ocert/snapshot");
    let acked = e.store.s3.get_acked(Kind::Snapshot, &snap).await.unwrap().unwrap().0;
    assert_eq!(guard_of(e.w[0].certify_object(acked).await), GuardFailure::Collected { kind: Kind::Snapshot, id: snap });
    assert!(e.store.valid_ocert(Kind::Snapshot, &snap).await.unwrap().is_none(), "T6 wrote nothing");
    let rec = e.w[0].sign_record(snap, None, token);
    let g5 = guard_of(e.w[0].commit_record(&rec).await);
    assert!(matches!(g5, GuardFailure::ManifestUncertified(_) | GuardFailure::Collected { .. }), "{g5:?}");
    assert!(e.store.record(&rec.id()).await.unwrap().is_none());
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert!(!present(&e.store, Kind::Snapshot, &snap).await);
    let c = e.w[0].commit_checkpoint(&cp).await.unwrap();
    assert_eq!(c, rec.id());
    assert!(present(&e.store, Kind::Snapshot, &snap).await);
    assert_eq!(recover_catalog(&e.store, e.w[0].id).await.unwrap().selected, Some(c));
    sweeps(&e.store, 1, 3).await;
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert_all_present(&e.store, &[(Kind::Snapshot, snap), (Kind::Manifest, cp.source_root.id()),
        (Kind::Manifest, cp.build_receipt.id())], "committed").await;
    e.audit_ok().await;
}

// ------------------------------------------------------------------ dead catalogue records

/// A staged record whose rank fell below the fence is retired after the grace period (its
/// snapshot then collected); a staged record at the current fence is not, and still commits.
/// Desktop-loss recovery from a fresh store handle selects the committed head with every
/// object present.
#[tokio::main(flavor = "current_thread")]
async fn gc_dead_catalogue_record_retired_and_recovery() {
    let g = gc_env("deadrec", 1);
    let e = &g.e;
    let t1 = e.ctl.rotate(e.w[0].id, b"rank-1").await.unwrap();
    let cp1 = one_snapshot(e, 0, "head", t1, None).await;
    let c1 = e.w[0].commit_checkpoint(&cp1).await.unwrap();
    // c2: staged at rank 1, never committed; the fence then moves to 2.
    let cp2 = one_snapshot(e, 0, "dead", t1, Some(c1)).await;
    let snap2 = prepare_snapshot(e, 0, &cp2).await;
    let r2 = e.w[0].sign_record(snap2, Some(c1), t1);
    assert!(e.w[0].stage_record(&r2).await.unwrap());
    let t2 = e.ctl.rotate(e.w[0].id, b"rank-2").await.unwrap();
    // c3: staged at rank 2 = fence: still committable, never retired.
    let cp3 = one_snapshot(e, 0, "live", t2, Some(c1)).await;
    let snap3 = prepare_snapshot(e, 0, &cp3).await;
    let r3 = e.w[0].sign_record(snap3, Some(c1), t2);
    assert!(e.w[0].stage_record(&r3).await.unwrap());
    enable(&e.store).await;
    let s1 = sweep(&e.store, 2).await;
    assert_eq!((s1.catalogue_dead_seen, s1.catalogue_retired), (1, 0), "{s1:?}");
    sweep(&e.store, 2).await;
    let s3 = sweep(&e.store, 2).await;
    assert_eq!(s3.catalogue_retired, 1, "{s3:?}");
    assert!(e.store.record(&r2.id()).await.unwrap().is_none(), "dead record cleared");
    assert!(e.store.meta.get(e.store.meta.keys.gc_retired_catalog(&r2.id())).await.unwrap().is_some());
    assert!(e.store.record(&r3.id()).await.unwrap().is_some(), "a record at the fence is not dead");
    // The retired record's snapshot and manifests become staging garbage.
    sweeps(&e.store, 2, 3).await;
    let d = gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    assert!(d.deleted >= 3, "{d:?}");
    for (kind, id) in [(Kind::Snapshot, snap2), (Kind::Manifest, cp2.source_root.id()), (Kind::Manifest, cp2.build_receipt.id())] {
        assert!(!present(&e.store, kind, &id).await, "{} of the dead record", kind.name());
    }
    // The retired record never comes back.
    let again = e.w[0].commit_record(&r2).await;
    assert!(matches!(again, Err(StoreError::Guard(GuardFailure::StaleToken { .. } | GuardFailure::CatalogueRetired(_)))), "{again:?}");
    // The live staged record still commits; recovery from a fresh handle selects it.
    assert!(e.w[0].commit_record(&r3).await.unwrap());
    let fresh = Store::open(&e.cfg, e.kf.ring(), Faults::none()).unwrap();
    let rec = recover_catalog(&fresh, e.w[0].id).await.unwrap();
    assert_eq!(rec.selected, Some(r3.id()), "{:?}", rec.heads);
    assert!(!rec.records.contains_key(&r2.id()));
    assert!(rec.records[&c1].admissible);
    discover(&fresh).await.unwrap();
    for cp in [&cp1, &cp3] {
        assert_all_present(&fresh, &[(Kind::Snapshot, cp.snapshot.id()), (Kind::Manifest, cp.source_root.id()),
            (Kind::Manifest, cp.build_receipt.id())], "recovered head chain").await;
    }
    audit::audit(&fresh).await.unwrap().assert_ok();
}

// ------------------------------------------------------------------ jobs

/// A pending job (J1 without J2 or J3) protects its group and capsule; once a receipt (J2) or
/// a cancellation (J3) exists the sweep releases the job's references.
#[tokio::main(flavor = "current_thread")]
async fn gc_pending_jobs_protect_their_objects() {
    let g = gc_env("jobs", 1);
    let e = &g.e;
    let mut jobs = Vec::new();
    for tag in ["pending", "received", "cancelled"] {
        let group = Opaque::new(Kind::Group, fixture::group_bytes(&format!("job-{tag}")));
        let capsule = Opaque::new(Kind::Capsule, format!("job capsule {tag}").into_bytes());
        e.store.s3.put_opaque(&group).await.unwrap();
        e.store.s3.put_opaque(&capsule).await.unwrap();
        let job = fixture::job_by(&e.authority(), tag, group.id(), capsule.id(), e.w[0].id, &[]);
        e.store.meta.issue_job(&job).await.unwrap();
        jobs.push((job, group.id(), capsule.id()));
    }
    let receipt = fixture::receipt_for(&jobs[1].0, &e.validator, Verdict::Accepted);
    e.store.meta.record_receipt(&e.w[0].id, &jobs[1].0.body.request, &receipt).await.unwrap();
    e.store.meta.cancel_job(&e.w[0].id, &jobs[2].0.body.request).await.unwrap();
    enable(&e.store).await;
    let s = sweep(&e.store, 1).await;
    assert_eq!((s.jobs_examined, s.jobs_released), (3, 2), "{s:?}");
    sweeps(&e.store, 1, 2).await;
    gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    let (_, pg, pc) = &jobs[0];
    assert_all_present(&e.store, &[(Kind::Group, *pg), (Kind::Capsule, *pc)], "pending job").await;
    for (_, group, capsule) in &jobs[1..] {
        assert!(!present(&e.store, Kind::Group, group).await && !present(&e.store, Kind::Capsule, capsule).await,
            "a finished job's objects are no longer protected");
    }
    e.audit_ok().await;
}

// ------------------------------------------------------------------ anti-entropy

fn member(e: &Env, transport: u8) -> FederationMember {
    FederationMember { replica: e.store.replica, transport_public: [transport; 32], authority: e.kf.ring().authority,
        writers: e.kf.ring().writers, job_issuers: e.kf.ring().job_issuers }
}

/// Two federated deployments, each trusting the other's keys.
fn federated(name: &str) -> (Gc, Gc) {
    let (ka, kb) = (KeyFile::demo_prefixed(&format!("{name}-a/"), 1), KeyFile::demo_prefixed(&format!("{name}-b/"), 1));
    let a = gc_env_with(&format!("{name}-a"), 1, Faults::none(), ka.clone(), Some(&kb.ring()));
    let b = gc_env_with(&format!("{name}-b"), 1, Faults::none(), kb, Some(&ka.ring()));
    (a, b)
}

async fn pin(a: &Env, b: &Env) {
    let mut members = BTreeMap::new();
    members.insert(a.store.deployment.clone(), member(a, 1));
    members.insert(b.store.deployment.clone(), member(b, 2));
    for e in [a, b] {
        let cfg = FederationConfig { deployment: e.store.deployment.clone(), members: members.clone(), target_homes: BTreeMap::new() };
        e.store.ae_pin_config(&cfg).await.unwrap();
    }
}

async fn materialize_all(st: &Store, event: &AeEvent) -> Vec<(u64, AePart)> {
    let mut parts = Vec::new();
    let mut after = None;
    loop {
        let page = st.ae_materialize(event, after, 1 << 20).await.unwrap();
        parts.extend(page.parts.clone());
        after = page.next_part;
        if page.complete {
            return parts;
        }
    }
}

/// A receiver's pending event protects the objects it names (referrer `aepending`) while
/// they wait for import; dropping the imported event releases those references, and the
/// imported marker's own references keep the objects.
#[tokio::main(flavor = "current_thread")]
async fn gc_pending_ae_events_protect_their_objects() {
    let (ga, gb) = federated("aepend");
    let (a, b) = (&ga.e, &gb.e);
    pin(a, b).await;
    enable(&b.store).await;
    let p = a.plain_package(0, "Gc.Federated", "federated");
    a.w[0].publish(&p).await.unwrap();
    let page = a.store.ae_page(None, 16, 1 << 20).await.unwrap();
    let event = page.events.iter().find(|ev| matches!(ev.kind, AeKind::GroupVariant { .. })).unwrap().clone();
    let parts = materialize_all(&a.store, &event).await;
    let source = a.store.deployment.clone();
    let pending = AePending { source: source.clone(), generation: page.generation, event: event.clone(),
        next_part: parts.last().map(|(n, _)| *n), objects_after: None, missing_count: 0,
        state: PendingState::Deferred("metadata collected".into()), last_error: None };
    let rows: Vec<_> = parts.iter().map(|(n, part)| (event.key.clone(), *n, part.clone())).collect();
    b.store.ae_save_progress(&source, page.generation, page.next.clone(), &[pending], &[], &rows).await.unwrap();
    let mut objects = Vec::new();
    for (_, part) in &parts {
        if let AePart::ObjectRef { kind, id, .. } = part {
            let AeFetch::Object(bytes) = a.store.ae_fetch(*kind, id).await.unwrap() else { panic!("source serves {id}") };
            b.store.put_live(*kind, &bytes).await.unwrap();
            objects.push((*kind, *id));
        }
    }
    assert!(objects.len() >= 3, "{objects:?}");
    sweeps(&b.store, 1, 3).await;
    gc::delete_doomed(&b.store, &gb.gc_s3).await.unwrap();
    assert_all_present(&b.store, &objects, "pending event's objects").await;
    // Import, then drop the pending row: its references go, T9's stay.
    assert_eq!(b.w[0].ae_import_staged(&source, &event).await.unwrap(), Outcome::Applied);
    b.store.ae_save_progress(&source, page.generation, page.next.clone(), &[], &[event.key.clone()], &[]).await.unwrap();
    let referrer = b.store.meta.keys.ae_pending(&source, &event.key);
    for (kind, id) in &objects {
        assert!(b.store.meta.get(b.store.meta.keys.gcref(*kind, id, &referrer)).await.unwrap().is_none(), "released");
    }
    assert!(b.store.meta.scan(&b.store.meta.keys.gc_aerefs_of(&source, &event.key), 100, |_| None).await.unwrap().is_empty());
    sweeps(&b.store, 1, 3).await;
    gc::delete_doomed(&b.store, &gb.gc_s3).await.unwrap();
    assert_all_present(&b.store, &objects, "imported group").await;
    b.audit_ok().await;
}

/// A source never serves or advertises a doomed, deleting or gone object (`Retired`, a
/// dropped part), never exports a retired catalogue record, and a receiver refuses a
/// catalogue event naming an ID retired here.
#[tokio::main(flavor = "current_thread")]
async fn gc_ae_never_serves_collected_objects_or_retired_records() {
    let (ga, gb) = federated("aeserve");
    let (a, b) = (&ga.e, &gb.e);
    pin(a, b).await;
    let p = a.plain_package(0, "Gc.Served", "served");
    a.w[0].publish(&p).await.unwrap();
    let orphan = put_orphan(&a.store, "aeserve-orphan").await;
    enable(&a.store).await;
    sweeps(&a.store, 1, 2).await;
    assert!(is_doomed(state(&a.store, Kind::Group, &orphan).await));
    assert_eq!(a.store.ae_fetch(Kind::Group, &orphan).await.unwrap(), AeFetch::Retired, "doomed, bytes still present");
    gc::delete_doomed(&a.store, &ga.gc_s3).await.unwrap();
    assert_eq!(a.store.ae_fetch(Kind::Group, &orphan).await.unwrap(), AeFetch::Retired, "gone");
    assert!(matches!(a.store.ae_fetch(Kind::Group, &p.group.id()).await.unwrap(), AeFetch::Object(_)));
    // Materialization drops a part naming a collected object (a forced state: committed
    // metadata never names one).
    let page = a.store.ae_page(None, 16, 1 << 20).await.unwrap();
    let event = page.events.iter().find(|ev| matches!(ev.kind, AeKind::GroupVariant { .. })).unwrap().clone();
    let staged = a.store.meta.keys.gcobj(Kind::StagedMarker, &p.marker.id());
    a.store.meta.raw_set(staged.clone(), GcState::Doomed { clock: 0, size: 1 }.encode()).await.unwrap();
    let parts = materialize_all(&a.store, &event).await;
    assert!(!parts.iter().any(|(_, part)| matches!(part, AePart::ObjectRef { kind: Kind::StagedMarker, .. })), "retired part advertised");
    assert_eq!(a.store.ae_fetch(Kind::StagedMarker, &p.marker.id()).await.unwrap(), AeFetch::Retired);
    raw_clear(&a.store, staged).await;
    // A committed record forced retired is not exported.
    let token = a.ctl.rotate(a.w[0].id, b"rank-1").await.unwrap();
    let cp = one_snapshot(a, 0, "aeserve-cp", token, None).await;
    let c = a.w[0].commit_checkpoint(&cp).await.unwrap();
    let page = a.store.ae_page(None, 128, 1 << 20).await.unwrap();
    let cat = page.events.iter().find(|ev| matches!(&ev.kind, AeKind::Catalogue { id, .. } if *id == c)).unwrap().clone();
    let retired = a.store.meta.keys.gc_retired_catalog(&c);
    a.store.meta.raw_set(retired.clone(), 1u64.to_be_bytes().to_vec()).await.unwrap();
    let err = a.store.ae_materialize(&cat, None, 1 << 20).await.unwrap_err();
    assert!(err.to_string().contains("retired"), "{err}");
    raw_clear(&a.store, retired).await;
    // The receiver refuses a catalogue event naming an ID it retired.
    b.store.meta.raw_set(b.store.meta.keys.gc_retired_catalog(&c), 1u64.to_be_bytes().to_vec()).await.unwrap();
    let outcome = b.w[0].ae_import_staged(&a.store.deployment, &cat).await.unwrap();
    assert!(matches!(outcome, Outcome::Rejected(ref why) if why.contains("retired")), "{outcome:?}");
}

// ------------------------------------------------------------------ gateway

fn sdk(endpoint: &str, access: &str, secret: &str) -> aws_sdk_s3::Client {
    let creds = aws_credential_types::Credentials::from_keys(access, secret, None);
    let conf = aws_sdk_s3::config::Builder::new()
        .behavior_version(aws_sdk_s3::config::BehaviorVersion::latest())
        .endpoint_url(endpoint)
        .region(aws_sdk_s3::config::Region::new(env("PARALEAN_S3_REGION")))
        .credentials_provider(creds)
        .force_path_style(true)
        .build();
    aws_sdk_s3::Client::from_conf(conf)
}

/// The FDB-aware gateway admits a GC-principal content DELETE only for a doomed key and moves
/// it to `Gone`; the application principal, an unknown or forged access key, unmarked,
/// sighted and gone keys, bucket and bulk deletes are all refused; a PUT under a doomed key
/// is refused and allowed again once gone.
#[tokio::main(flavor = "current_thread")]
async fn gc_guard_deletes_only_doomed_keys() {
    let g = gc_env("guard", 1);
    let e = &g.e;
    let st = &e.store;
    let (unmarked, sighted, doomed) = (put_orphan(st, "guard-unmarked").await, put_orphan(st, "guard-sighted").await,
        put_orphan(st, "guard-doomed").await);
    st.meta.raw_set(st.meta.keys.gcobj(Kind::Group, &sighted), GcState::Sighted { clock: 1 }.encode()).await.unwrap();
    st.meta.raw_set(st.meta.keys.gcobj(Kind::Group, &doomed), GcState::Doomed { clock: 1, size: 7 }.encode()).await.unwrap();
    let endpoint = g.guard.endpoint.clone();
    let app = s3_with(&e.cfg, &endpoint, &e.cfg.s3.access_key, &e.cfg.s3.secret_key);
    let forged = s3_with(&e.cfg, &endpoint, &gc_key().access, &"0".repeat(64));
    let other = s3_with(&e.cfg, &endpoint, &format!("GK{}", hex_random(24)), &hex_random(64));
    assert!(app.try_delete(Kind::Group, &doomed).await.is_err(), "application principal");
    assert!(other.try_delete(Kind::Group, &doomed).await.is_err(), "unknown access key");
    assert!(g.gc_s3.try_delete(Kind::Group, &unmarked).await.is_err(), "unmarked key");
    assert!(g.gc_s3.try_delete(Kind::Group, &sighted).await.is_err(), "sighted key");
    // A PUT under a doomed key is refused.
    let bytes = Opaque::new(Kind::Group, fixture::group_bytes("guard-doomed")).preimage();
    assert!(app.put(Kind::Group, &bytes).await.is_err(), "PUT under Doomed");
    // A forged signature with the GC key ID passes the identity selector (the key moves to
    // Deleting); Garage refuses it and the object stays, never Gone.
    assert!(forged.try_delete(Kind::Group, &doomed).await.is_err(), "forged signature");
    assert!(present(st, Kind::Group, &doomed).await);
    assert!(matches!(state(st, Kind::Group, &doomed).await, Some(GcState::Deleting { .. })));
    assert!(app.put(Kind::Group, &bytes).await.is_err(), "PUT under Deleting");
    // Bucket, bulk and versioned deletes stay refused for the GC principal.
    let client = sdk(&endpoint, &gc_key().access, &gc_key().secret);
    let bucket = env("PARALEAN_S3_BUCKET");
    assert!(client.delete_bucket().bucket(&bucket).send().await.is_err(), "bucket delete");
    let key = g.gc_s3.key(Kind::Group, &doomed);
    let del = aws_sdk_s3::types::Delete::builder()
        .objects(aws_sdk_s3::types::ObjectIdentifier::builder().key(&key).build().unwrap()).build().unwrap();
    assert!(client.delete_objects().bucket(&bucket).delete(del).send().await.is_err(), "bulk delete");
    assert!(client.delete_object().bucket(&bucket).key(&key).version_id("x").send().await.is_err(), "delete with a query");
    assert!(present(st, Kind::Group, &doomed).await);
    // The GC principal deletes the marked key: Deleting{nonce}, forwarded, Gone.
    g.gc_s3.try_delete(Kind::Group, &doomed).await.unwrap();
    assert!(!present(st, Kind::Group, &doomed).await);
    assert!(matches!(state(st, Kind::Group, &doomed).await, Some(GcState::Gone { .. })));
    assert!(g.gc_s3.try_delete(Kind::Group, &doomed).await.is_err(), "gone key");
    assert!(present(st, Kind::Group, &unmarked).await && present(st, Kind::Group, &sighted).await);
    // After Gone a PUT is admitted again (the revival path).
    app.put(Kind::Group, &bytes).await.unwrap();
    assert!(present(st, Kind::Group, &doomed).await);
}

// ------------------------------------------------------------------ measurement

/// Measurement (ignored by default): `N` published groups, `M` staged orphans of known size
/// (abandoned uploads and aborted checkpoints), backfill and sweeps; reclaimed bytes, cost of
/// a pass and the reference index's per-T1 overhead. Writes `results/w4r/store-gc.json`.
#[tokio::main(flavor = "current_thread")]
async fn gc_measurement() {
    let n: usize = std::env::var("GC_MEASURE_GROUPS").ok().and_then(|s| s.parse().ok()).unwrap_or(200);
    let m: usize = std::env::var("GC_MEASURE_ORPHANS").ok().and_then(|s| s.parse().ok()).unwrap_or(100);
    let g = gc_env("measure", 1);
    let e = &g.e;
    // Publication latency (T1 with its reference index) and the index's own cost.
    let mut t1_ms = Vec::new();
    let mut published = Vec::new();
    for i in 0..n {
        let p = e.plain_package(0, &format!("Gc.M{i}"), &format!("measure-{i}"));
        let t = Instant::now();
        e.w[0].publish(&p).await.unwrap();
        t1_ms.push(t.elapsed().as_secs_f64() * 1e3);
        published.push(p);
    }
    // The point reads and writes T1 adds (one gcobj read and one gcref write per named
    // object), alone in one transaction under a scratch referrer that is cleared again.
    let mut ref_ms = Vec::new();
    let mut refs_per_t1 = 0;
    let scratch: &[u8] = b"measurement-scratch-referrer";
    for p in &published {
        let objects = package_objects(p);
        refs_per_t1 = objects.len();
        let k = e.store.meta.keys.clone();
        let t = Instant::now();
        let mut trx = e.store.meta.db.create_trx().unwrap();
        loop {
            gc::reference_in(&trx, &k, &objects, scratch).await.unwrap();
            for (kind, id) in &objects {
                trx.clear(&k.gcref(*kind, id, scratch));
            }
            match trx.commit().await {
                Ok(_) => break,
                Err(err) => trx = err.on_error().await.unwrap(),
            }
        }
        ref_ms.push(t.elapsed().as_secs_f64() * 1e3);
    }
    // Staging garbage of known size.
    let mut orphan_bytes = 0u64;
    let mut orphan_objects = 0u64;
    let token = e.ctl.rotate(e.w[0].id, b"rank-1").await.unwrap();
    for i in 0..m {
        if i % 4 == 3 {
            let cp = fixture::checkpoint(e.w[0].id, vec![rev_id(&published[i % n])], None, token, &format!("aborted-{i}"));
            for (kind, o) in [(Kind::Manifest, cp.source_root.preimage()), (Kind::Manifest, cp.build_receipt.preimage()),
                (Kind::Snapshot, cp.snapshot.preimage())] {
                e.store.s3.put(kind, &o).await.unwrap();
                orphan_bytes += o.len() as u64;
                orphan_objects += 1;
            }
        } else {
            let mut payload = fixture::group_bytes(&format!("abandoned-{i}"));
            payload.extend(vec![i as u8; 16 * 1024]);
            let o = Opaque::new(Kind::Group, payload);
            e.store.s3.put_opaque(&o).await.unwrap();
            orphan_bytes += o.preimage().len() as u64;
            orphan_objects += 1;
        }
    }
    // Fixture chunks are not named by any chunk index: they are staging garbage too.
    for p in &published {
        for c in &p.chunks {
            orphan_bytes += c.preimage().len() as u64;
            orphan_objects += 1;
        }
    }
    let backfill = gc::backfill(&e.store).await.unwrap();
    gc::enable(&e.store).await.unwrap();
    let grace = 1;
    let mut passes = Vec::new();
    for _ in 0..3 {
        passes.push(sweep(&e.store, grace).await);
    }
    let delete = gc::delete_doomed(&e.store, &g.gc_s3).await.unwrap();
    let after = sweep(&e.store, grace).await;
    assert_eq!(delete.deleted, orphan_objects, "{delete:?}");
    assert_eq!(delete.reclaimed_bytes, orphan_bytes);
    for p in &published {
        assert_all_present(&e.store, &package_objects(p), "published").await;
    }
    let mean = |v: &[f64]| v.iter().sum::<f64>() / v.len().max(1) as f64;
    let median = |v: &[f64]| {
        let mut s = v.to_vec();
        s.sort_by(|a, b| a.partial_cmp(b).unwrap());
        s[s.len() / 2]
    };
    let report = serde_json::json!({
        "instance": env("PARALEAN_INSTANCE"),
        "deployment": e.store.deployment,
        "published_groups": n,
        "staged_orphans": orphan_objects,
        "staged_orphan_bytes": orphan_bytes,
        "grace_ticks": grace,
        "backfill": backfill,
        "sweeps": passes,
        "delete": delete,
        "after_sweep": after,
        "reclaimed_bytes": delete.reclaimed_bytes,
        "objects_deleted": delete.deleted,
        "t1": {
            "samples": t1_ms.len(),
            "publish_ms_mean": mean(&t1_ms),
            "publish_ms_median": median(&t1_ms),
            "objects_referenced_per_t1": refs_per_t1,
            "added_point_reads_per_t1": refs_per_t1,
            "added_point_writes_per_t1": refs_per_t1,
            "reference_index_alone_ms_mean": mean(&ref_ms),
            "reference_index_alone_ms_median": median(&ref_ms),
            "note": "publish latency includes the S3 PUTs and T1; the reference-only transaction issues the gcobj reads (concurrently) and gcref writes T1 adds, plus scratch clears, in a transaction of its own",
        },
    });
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../../results/w4r/store-gc.json");
    std::fs::create_dir_all(std::path::Path::new(path).parent().unwrap()).unwrap();
    std::fs::write(path, serde_json::to_string_pretty(&report).unwrap()).unwrap();
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}

// ------------------------------------------------------------------ main

fn main() {
    struct StopNetwork;
    impl Drop for StopNetwork {
        fn drop(&mut self) {
            paralean_store::meta::shutdown();
        }
    }
    let stop = StopNetwork;
    let args = libtest_mimic::Arguments::from_args();
    let t = |name: &'static str, f: fn()| libtest_mimic::Trial::test(name, move || { f(); Ok(()) });
    let trials = vec![
        t("gc_disabled_by_default_collects_nothing", gc_disabled_by_default_collects_nothing),
        t("gc_collects_staged_orphans_only_after_grace", gc_collects_staged_orphans_only_after_grace),
        t("gc_never_collects_published_tombstoned_moved_or_revised", gc_never_collects_published_tombstoned_moved_or_revised),
        t("gc_t1_doom_race_both_orders", gc_t1_doom_race_both_orders),
        t("gc_revival_after_gone", gc_revival_after_gone),
        t("gc_t5_t6_refuse_a_doomed_snapshot", gc_t5_t6_refuse_a_doomed_snapshot),
        t("gc_dead_catalogue_record_retired_and_recovery", gc_dead_catalogue_record_retired_and_recovery),
        t("gc_pending_jobs_protect_their_objects", gc_pending_jobs_protect_their_objects),
        t("gc_pending_ae_events_protect_their_objects", gc_pending_ae_events_protect_their_objects),
        t("gc_ae_never_serves_collected_objects_or_retired_records", gc_ae_never_serves_collected_objects_or_retired_records),
        t("gc_guard_deletes_only_doomed_keys", gc_guard_deletes_only_doomed_keys),
        t("gc_measurement", gc_measurement).with_ignored_flag(true),
    ];
    let result = libtest_mimic::run(&args, trials);
    if let Some(key) = GC_KEY.get() {
        garage(&["key", "delete", "--yes", &key.access]);
    }
    drop(stop);
    result.exit();
}
