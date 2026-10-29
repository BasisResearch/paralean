//! W4-rest design 2: dynamic controller shard topology, on the live private cluster.
//! Moves (begin/export/import) under takeover, fences on every bucket-keyed write,
//! drained validations, cross-shard replay, add/remove shard, real processes, and an
//! ignored resharding benchmark.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use common::{deployment, scratch};
use paralean_control::controller::{call_controller, BatchMemberReq, ControlPlane, ControlRequest, ControlResponse, ControllerConfig, TargetReq};
use paralean_control::durable::Durable;
use paralean_control::gc::GcConfig;
use paralean_control::topology::{self, MoveState};
use paralean_store::receipt::SignedJob;
use paralean_store::*;
use paralean_validator_api::{rpc, ValidatorRequest, ValidatorResponse};

const LEASE: Duration = Duration::from_millis(500);

fn config(store: Store, keys: &KeyFile, validators: Vec<String>) -> ControllerConfig {
    ControllerConfig {
        store, authority: keys.authority_signer().unwrap(), validators,
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: LEASE,
        max_work_queue: 4096, max_validations: 8, validation_deadline: Duration::from_secs(30),
        validation_memory_mb: 128, validator_attempts: 1,
    }
}

struct Fixture { keys: KeyFile, store: Store, cfg: ControllerConfig }

async fn fixture(name: &str, shards: u32) -> Fixture {
    fixture_with(name, shards, vec![]).await
}

async fn fixture_with(name: &str, shards: u32, validators: Vec<String>) -> Fixture {
    let keys = KeyFile::demo(3);
    let store = Store::open(&StoreConfig::from_env(&deployment(name)).unwrap(), keys.ring(), Faults::none()).unwrap();
    topology::init_dynamic(&store, shards).await.unwrap();
    let cfg = config(store.clone(), &keys, validators);
    Fixture { keys, store, cfg }
}

impl Fixture {
    fn plane(&self, shard: u32) -> Arc<ControlPlane> { ControlPlane::new_dynamic(self.cfg.clone(), shard, GcConfig::default()) }
    fn plane_gc(&self, shard: u32) -> Arc<ControlPlane> {
        ControlPlane::new_dynamic(self.cfg.clone(), shard, GcConfig { enabled: true, grace_ticks: 1, scan_limit: 128 })
    }
    fn worker(&self, i: usize) -> WorkspaceId { self.keys.workspace(&format!("w{i}")).unwrap().0 }
    /// Advance `shard`'s logical clock past any lease taken so far.
    async fn expire(&self, shard: u32) {
        let clock = Durable::new_dynamic(self.store.clone(), LEASE, shard);
        for _ in 0..9 { clock.tick().await.unwrap(); }
    }
}

/// A target name whose hash bucket is `bucket`.
fn in_bucket(tag: &str, bucket: u16) -> Name {
    (0..100_000).map(|i| Name::parse(&format!("{tag}.t{i}"))).find(|n| topology::name_bucket(n) == bucket).unwrap()
}

async fn status(cp: &Arc<ControlPlane>) -> serde_json::Value {
    match cp.handle(ControlRequest::Status).await {
        ControlResponse::Status { status } => status,
        other => panic!("status: {other:?}"),
    }
}

/// request -> state of a leader's current work.
async fn work_of(cp: &Arc<ControlPlane>) -> BTreeMap<String, String> {
    let s = status(cp).await;
    assert_eq!(s["leader"], true, "not leader: {s}");
    s["work"].as_array().unwrap().iter()
        .map(|w| (w["request"].as_str().unwrap().to_string(), w["state"].as_str().unwrap().to_string())).collect()
}

async fn submit(cp: &Arc<ControlPlane>, request: &str, target: &Name) -> ControlResponse {
    cp.handle(ControlRequest::SubmitWork { request: request.into(), target: target.to_string(), memory_mb: 1 }).await
}

async fn register(cp: &Arc<ControlPlane>, w: WorkspaceId) {
    assert!(matches!(cp.handle(ControlRequest::Register { worker: w.hex(), capacity_mb: 1024 }).await, ControlResponse::Registered { .. }));
}

fn moving() -> ControlResponse { ControlResponse::Inconclusive { reason: "bucket moving".into() } }
fn not_shard() -> ControlResponse { ControlResponse::Inconclusive { reason: "not controller shard".into() } }

async fn move_state(store: &Store, id: u64) -> MoveState { topology::read_move(store, id).await.unwrap().unwrap().state }

async fn epochs(store: &Store, jobs: &[(String, Name, u64)]) -> Vec<u64> {
    let mut out = vec![];
    for (_, target, _) in jobs { out.push(store.target(target).await.unwrap().unwrap().epoch) }
    out
}

/// Every request is in exactly one shard's snapshot.
fn exactly_once(parts: &[&BTreeMap<String, String>], expected: &BTreeSet<String>) {
    let mut seen: BTreeMap<&str, usize> = BTreeMap::new();
    for part in parts { for r in part.keys() { *seen.entry(r).or_default() += 1; } }
    let dup: Vec<_> = seen.iter().filter(|(_, n)| **n > 1).collect();
    assert!(dup.is_empty(), "duplicated across shards: {dup:?}");
    let have: BTreeSet<String> = seen.keys().map(|s| s.to_string()).collect();
    let lost: Vec<_> = expected.difference(&have).collect();
    assert!(lost.is_empty(), "lost by the move: {lost:?}");
}

/// Queued, running (assigned with an epoch), failed-and-requeued, done and cancelled
/// work and a group move with no loss, no duplicate and unchanged epochs. Requests for
/// the moving buckets are refused retryably at the destination until it imports; a
/// moved running job finishes at the destination; the source refuses its buckets.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn move_preserves_every_job_exactly_once() {
    let f = fixture("w4r-move", 2).await;
    let (a, b) = (f.plane(0), f.plane(1));
    let w = f.worker(0);
    register(&a, w).await;
    let moved_buckets = [0u16, 1, 2, 3];
    let mut expected = BTreeSet::new();
    let mut bucket_of = BTreeMap::new();
    for bucket in moved_buckets.iter().copied().chain([40u16]) {
        for i in 0..3 {
            let request = format!("job/{bucket}/{i}");
            let target = in_bucket(&format!("Move.b{bucket}i{i}"), bucket);
            assert_eq!(submit(&a, &request, &target).await, ControlResponse::Queued);
            expected.insert(request.clone());
            bucket_of.insert(request, bucket);
        }
    }
    // Five assigned: one finishes, one fails (requeued), one is cancelled, two run on.
    let mut running = Vec::new();
    for _ in 0..5 {
        match a.handle(ControlRequest::Poll { worker: w.hex() }).await {
            ControlResponse::Work { request, target, epoch, .. } => running.push((request, Name::parse(&target), epoch)),
            other => panic!("poll: {other:?}"),
        }
    }
    assert_eq!(a.handle(ControlRequest::Finish { worker: w.hex(), request: running[0].0.clone(), ok: true }).await, ControlResponse::Ok);
    assert_eq!(a.handle(ControlRequest::Finish { worker: w.hex(), request: running[1].0.clone(), ok: false }).await, ControlResponse::Ok);
    assert_eq!(a.handle(ControlRequest::Cancel { request: running[2].0.clone(), worker: String::new() }).await, ControlResponse::Cancelled);
    let still_running: Vec<_> = running[3..].to_vec();
    // A jointly assigned group in bucket 0 (its first sorted name's).
    let g0 = in_bucket("GroupA", 0);
    let g1 = Name::parse("GroupZ.other");
    assert!(matches!(a.handle(ControlRequest::AssignGroup { targets: vec![g0.to_string(), g1.to_string()], worker: w.hex(),
        request: "group/1".into(), statements: vec![] }).await, ControlResponse::AssignedGroup { .. }));
    let before = work_of(&a).await;
    assert_eq!(before.keys().cloned().collect::<BTreeSet<_>>(), expected);
    let running_epochs = epochs(&f.store, &still_running).await;

    topology::begin_move(&f.store, 11, &moved_buckets, 0, 1).await.unwrap();
    b.pause_move_steps(true);
    a.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 11).await, MoveState::Exported);
    // The destination owns the buckets but refuses them until it imports.
    let late = in_bucket("Move.late", 0);
    let moved_running = still_running.iter().find(|(r, ..)| moved_buckets.contains(&bucket_of[r])).expect("a moved running job").clone();
    assert_eq!(submit(&b, "late/1", &late).await, moving());
    assert_eq!(b.handle(ControlRequest::Finish { worker: w.hex(), request: moved_running.0.clone(), ok: true }).await, moving());
    assert_eq!(submit(&a, "late/1", &late).await, not_shard());
    assert_eq!(a.handle(ControlRequest::Finish { worker: w.hex(), request: moved_running.0.clone(), ok: true }).await, not_shard());
    b.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 11).await, MoveState::Done);
    assert!(topology::active_moves(&f.store).await.unwrap().is_empty());
    assert!(b.durable().read_handoff(11).await.unwrap().is_none(), "handoff not consumed");

    let (after_a, after_b) = (work_of(&a).await, work_of(&b).await);
    exactly_once(&[&after_a, &after_b], &expected);
    for (request, state) in &before {
        let here = if moved_buckets.contains(&bucket_of[request]) { &after_b } else { &after_a };
        assert_eq!(here.get(request), Some(state), "{request} changed or is at the wrong shard");
    }
    assert_eq!(status(&b).await["groups"].as_array().unwrap().len(), 1);
    assert_eq!(status(&a).await["groups"].as_array().unwrap().len(), 0);
    // Assignments keep their epochs; the moved running job finishes at the destination.
    assert_eq!(epochs(&f.store, &still_running).await, running_epochs);
    assert_eq!(b.handle(ControlRequest::Finish { worker: w.hex(), request: moved_running.0.clone(), ok: true }).await, ControlResponse::Ok);
    assert_eq!(work_of(&b).await[&moved_running.0], "Done");
    // The destination assigns moved queued work (T4 in its bucket), takes new work and
    // reassigns the moved group.
    assert!(matches!(b.handle(ControlRequest::Poll { worker: w.hex() }).await, ControlResponse::Work { .. }));
    assert_eq!(submit(&b, "late/1", &late).await, ControlResponse::Queued);
    assert!(matches!(b.handle(ControlRequest::AssignGroup { targets: vec![g0.to_string(), g1.to_string()], worker: f.worker(1).hex(),
        request: "group/2".into(), statements: vec![] }).await, ControlResponse::AssignedGroup { .. }));
    assert_eq!(f.store.target(&g1).await.unwrap().unwrap().owner, f.worker(1));
}

/// The source leader dies before export, and the destination leader before import:
/// each step completes on takeover with a new term. A source leader that dies after
/// export leaves nothing for its successor.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn leaders_lost_around_export_and_import_complete_by_takeover() {
    let f = fixture("w4r-takeover", 2).await;
    let (a1, b1) = (f.plane(0), f.plane(1));
    a1.pause_move_steps(true);
    b1.pause_move_steps(true);
    let mut expected = BTreeSet::new();
    for i in 0..6u16 {
        let request = format!("tk/{i}");
        assert_eq!(submit(&a1, &request, &in_bucket(&format!("Takeover{i}"), i % 3)).await, ControlResponse::Queued);
        expected.insert(request);
    }
    let a_term = status(&a1).await["term"].as_u64().unwrap();
    let b_term = status(&b1).await["term"].as_u64().unwrap();
    topology::begin_move(&f.store, 21, &[0, 1, 2], 0, 1).await.unwrap();
    // The paused source refuses its moving buckets with the retryable answer.
    assert_eq!(submit(&a1, "tk/new", &in_bucket("Takeover.new", 0)).await, moving());
    drop(a1);
    f.expire(0).await;
    let a2 = f.plane(0);
    a2.pause_move_steps(true);
    let a2_term = a2.drive_moves_now().await.unwrap();
    assert!(a2_term > a_term);
    assert_eq!(move_state(&f.store, 21).await, MoveState::Exported);
    // Source lost after export: its successor finds nothing of the moved buckets.
    drop(a2);
    f.expire(0).await;
    let a3 = f.plane(0);
    assert!(a3.drive_moves_now().await.unwrap() > a2_term);
    assert!(work_of(&a3).await.is_empty());
    drop(b1);
    f.expire(1).await;
    let b2 = f.plane(1);
    assert!(b2.drive_moves_now().await.unwrap() > b_term);
    assert_eq!(move_state(&f.store, 21).await, MoveState::Done);
    let (wa, wb) = (work_of(&a3).await, work_of(&b2).await);
    exactly_once(&[&wa, &wb], &expected);
    assert_eq!(wb.len(), expected.len());
}

/// After Begin, the source writes nothing new for its moving buckets; after export, a
/// still-leading source can write none of them: no work route, T4 claim, J1, J2 or
/// recovery count. The destination cannot write them before it imports.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn stale_source_cannot_write_moved_buckets() {
    let f = fixture("w4r-fence", 2).await;
    let (a, b) = (f.plane(0), f.plane(1));
    let w = f.worker(0);
    let ta = a.drive_moves_now().await.unwrap();
    let tb = b.drive_moves_now().await.unwrap();
    let (da, db) = (a.durable(), b.durable());
    let owned = in_bucket("Fence.owned", 5);
    let fresh = in_bucket("Fence.fresh", 5);
    da.assign_group(&[owned.clone()], w, b"fence/assign", ta).await.unwrap();
    let validator = Signer::derive("validator");
    let bound = |tag: &str, name: &Name| {
        let mut body = fixture::package(tag, w, &validator, name, vec![], None, 1).job.body;
        body.targets = vec![receipt::TargetBinding { name: name.clone(), epoch: 0, statement: vec![] }];
        SignedJob::sign(body, &fixture::authority())
    };
    let job = bound("fence-job", &owned);
    let other_job = bound("fence-other", &fresh);
    da.issue_job(&job, ta).await.unwrap();
    let receipt = fixture::receipt_for(&job, &validator, Verdict::Accepted);

    topology::begin_move(&f.store, 31, &[5], 0, 1).await.unwrap();
    // Prepared: the source owns bucket 5 but writes nothing new for it.
    assert!(da.reserve_work_shard("fence/prepared", &fresh, ta).await.is_err(), "work route during move");
    assert!(da.assign_group(&[fresh.clone()], w, b"fence/prepared", ta).await.is_err(), "T4 claim during move");
    assert!(da.issue_job(&other_job, ta).await.is_err(), "J1 during move");
    assert!(db.reserve_work_shard("fence/prepared", &fresh, tb).await.is_err(), "destination wrote before export");
    a.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 31).await, MoveState::Exported);
    // The same leader and term after export: every bucket-keyed write is fenced.
    assert!(da.reserve_work_shard("fence/stale", &fresh, ta).await.is_err(), "stale work route");
    assert!(da.assign_group(&[fresh.clone()], w, b"fence/stale", ta).await.is_err(), "stale T4 claim");
    assert!(da.issue_job(&other_job, ta).await.is_err(), "stale J1");
    assert!(da.record_receipt(&w, &job.body.request, &receipt, ta).await.is_err(), "stale J2");
    assert!(da.count_recovery(&w, &job.body.request, 4, ta).await.is_err(), "stale recovery dispatch");
    assert!(f.store.meta.get(f.store.meta.keys.job_receipt(&w, &job.body.request)).await.unwrap().is_none());
    assert!(f.store.meta.get(f.store.meta.keys.job_request(&w, &other_job.body.request)).await.unwrap().is_none());
    assert_eq!(da.mapped_shard(&fresh).await.unwrap(), None);
    // The destination before import: still moving.
    assert!(db.record_receipt(&w, &job.body.request, &receipt, tb).await.is_err(), "J2 before import");
    assert!(db.reserve_work_shard("fence/early", &fresh, tb).await.is_err(), "work route before import");
    let tb = b.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 31).await, MoveState::Done);
    db.record_receipt(&w, &job.body.request, &receipt, tb).await.unwrap();
    db.reserve_work_shard("fence/after", &fresh, tb).await.unwrap();
    assert!(db.count_recovery(&w, &job.body.request, 4, tb).await.unwrap());
    assert_eq!(da.shard_for_target(&fresh).await.unwrap(), 1);
}

/// Snapshot saves compare the head generation they loaded (and so do export and
/// import commits): a snapshot computed from a superseded load never replaces a newer
/// one, even under the same lease and term.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn snapshot_saves_compare_the_loaded_generation() {
    let f = fixture("w4r-cas", 2).await;
    let d = Durable::new_dynamic(f.store.clone(), LEASE, 0);
    let term = d.acquire_or_renew().await.unwrap().unwrap().term;
    let g1 = d.save_generation(b"first", term, &[], &[], Some(None)).await.unwrap();
    let g2 = d.save_generation(b"second", term, &[], &[], Some(Some(g1))).await.unwrap();
    assert!(g2 > g1);
    assert!(d.save_generation(b"stale", term, &[], &[], Some(Some(g1))).await.is_err(), "stale generation replaced the head");
    assert_eq!(d.load().await.unwrap().unwrap(), b"second");
    topology::begin_move(&f.store, 41, &[7], 0, 1).await.unwrap();
    let outcome = d.export_commit(41, term, Some(g1), b"{}", b"{}", &[]).await;
    assert!(outcome.is_err(), "export from a superseded load: {outcome:?}");
    assert_eq!(move_state(&f.store, 41).await, MoveState::Prepared);
}

/// A source leader whose lease passed to a successor cannot export, even with the
/// current head generation.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn stale_leader_export_is_fenced_by_lease() {
    let f = fixture("w4r-export-lease", 2).await;
    let old = Durable::new_dynamic(f.store.clone(), LEASE, 0);
    let term = old.acquire_or_renew().await.unwrap().unwrap().term;
    let generation = old.save_generation(b"{}", term, &[], &[], Some(None)).await.unwrap();
    topology::begin_move(&f.store, 51, &[9], 0, 1).await.unwrap();
    f.expire(0).await;
    let next = Durable::new_dynamic(f.store.clone(), LEASE, 0);
    assert!(next.acquire_or_renew().await.unwrap().unwrap().term > term);
    let outcome = old.export_commit(51, term, Some(generation), b"{}", b"{}", &[]).await;
    assert!(outcome.is_err(), "stale leader exported: {outcome:?}");
    assert_eq!(move_state(&f.store, 51).await, MoveState::Prepared);
    assert_eq!(topology::read_bucket(&f.store, 9).await.unwrap().shard, 0);
}

/// A fake validator that answers after `delay` with an accepted receipt.
async fn slow_validator(delay: Duration, calls: Arc<AtomicUsize>) -> (String, tokio::task::JoinHandle<()>) {
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap().to_string();
    let signer = Signer::derive("validator");
    let authority = fixture::authority().public();
    let handle = paralean_control::server::serve_authenticated(listener, signer.clone(), authority,
        move |_: &ValidatorRequest, public: &[u8; 32]| *public == authority,
        move |req: ValidatorRequest| {
            let (calls, signer) = (calls.clone(), signer.clone());
            async move {
                match req {
                    ValidatorRequest::Validate { job } => {
                        calls.fetch_add(1, Ordering::SeqCst);
                        tokio::time::sleep(delay).await;
                        let job = SignedJob::from_bytes(&hex::decode(job).unwrap()).unwrap();
                        ValidatorResponse::Receipt { receipt: hex::encode(fixture::receipt_for(&job, &signer, Verdict::Accepted).to_bytes()) }
                    }
                    ValidatorRequest::ValidateBatch { jobs } => {
                        calls.fetch_add(1, Ordering::SeqCst);
                        tokio::time::sleep(delay).await;
                        let responses = jobs.iter().map(|j| {
                            let job = SignedJob::from_bytes(&hex::decode(j).unwrap()).unwrap();
                            ValidatorResponse::Receipt { receipt: hex::encode(fixture::receipt_for(&job, &signer, Verdict::Accepted).to_bytes()) }
                        }).collect();
                        ValidatorResponse::Batch { responses }
                    }
                    _ => ValidatorResponse::Busy,
                }
            }
        });
    (addr, handle)
}

fn validate_req(w: WorkspaceId, request: &str, target: &Name) -> ControlRequest {
    ControlRequest::Validate {
        worker: w.hex(), request: request.into(), group: Id(paralean_store::id::sha256(request.as_bytes())).hex(),
        capsule: Id(paralean_store::id::sha256(b"capsule")).hex(), deps: vec![],
        targets: vec![TargetReq { name: target.to_string(), statement: String::new() }], memory_mb: 0, deadline_ms: 0,
    }
}

/// A validation in flight when its bucket starts moving is drained: the export waits,
/// new validations of the bucket are refused retryably, the drained receipt is recorded
/// once at the source, and a retry at the destination returns that same receipt
/// without another validator call.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn inflight_validation_is_drained_before_export() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (vaddr, _validator) = slow_validator(Duration::from_millis(1500), calls.clone()).await;
    let f = fixture_with("w4r-drain", 2, vec![vaddr]).await;
    let (a, b) = (f.plane(0), f.plane(1));
    let w = f.worker(0);
    register(&a, w).await;
    let target = in_bucket("Drain.target", 12);
    let other = in_bucket("Drain.other", 12);
    for (t, r) in [(&target, "drain/assign"), (&other, "drain/assign2")] {
        assert!(matches!(a.handle(ControlRequest::AssignGroup { targets: vec![t.to_string()], worker: w.hex(), request: r.into(), statements: vec![] }).await,
            ControlResponse::AssignedGroup { .. }));
    }
    let a2 = a.clone();
    let req = validate_req(w, "drain/1", &target);
    let inflight = tokio::spawn(async move { a2.handle(req).await });
    let deadline = Instant::now() + Duration::from_secs(10);
    while calls.load(Ordering::SeqCst) == 0 {
        assert!(Instant::now() < deadline, "validation never dispatched");
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    topology::begin_move(&f.store, 61, &[12], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 61).await, MoveState::Prepared, "exported with a validation in flight");
    assert_eq!(a.handle(validate_req(w, "drain/2", &other)).await, moving());
    let answer = inflight.await.unwrap();
    let ControlResponse::Receipt { receipt, .. } = &answer else { panic!("drained validation: {answer:?}") };
    let stored = f.store.meta.get(f.store.meta.keys.job_receipt(&w, b"drain/1")).await.unwrap().expect("J2 recorded");
    assert_eq!(hex::encode(stored), *receipt);
    a.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 61).await, MoveState::Exported);
    b.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 61).await, MoveState::Done);
    register(&b, w).await;
    assert_eq!(b.handle(validate_req(w, "drain/1", &target)).await, answer, "retry at the destination");
    assert_eq!(a.handle(validate_req(w, "drain/1", &target)).await, not_shard());
    assert_eq!(calls.load(Ordering::SeqCst), 1, "the drained validation ran again");
    // The next validation of the moved bucket runs at the destination.
    assert!(matches!(b.handle(validate_req(w, "drain/2", &other)).await, ControlResponse::Receipt { .. }));
    assert_eq!(calls.load(Ordering::SeqCst), 2);
}

/// Work compacted to a replay row at the source is still a duplicate at the destination,
/// and a poll token whose job moved keeps its first answer at the destination while
/// the source answers NoWork rather than a new job.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn compacted_work_and_poll_tokens_resolve_across_shards() {
    let f = fixture("w4r-replay", 2).await;
    let (a, b) = (f.plane_gc(0), f.plane(1));
    let w = f.worker(0);
    register(&a, w).await;
    let (t1, t2, t3) = (in_bucket("Replay.one", 20), in_bucket("Replay.two", 20), in_bucket("Replay.three", 90));
    assert_eq!(submit(&a, "replay/1", &t1).await, ControlResponse::Queued);
    let ControlResponse::Work { request, .. } = a.handle(ControlRequest::Poll { worker: w.hex() }).await else { panic!("poll") };
    assert_eq!(request, "replay/1");
    assert_eq!(a.handle(ControlRequest::Finish { worker: w.hex(), request, ok: true }).await, ControlResponse::Ok);
    let clock = Durable::new_dynamic(f.store.clone(), LEASE, 0);
    for _ in 0..4 {
        clock.tick().await.unwrap();
        a.compact_history_once().await.unwrap();
        if !work_of(&a).await.contains_key("replay/1") { break }
    }
    assert!(!work_of(&a).await.contains_key("replay/1"), "not compacted");
    assert_eq!(submit(&a, "replay/2", &t2).await, ControlResponse::Queued);
    let token = ControlRequest::PollRequest { worker: w.hex(), request: "replay/token".into() };
    let first = a.handle(token.clone()).await;
    assert!(matches!(&first, ControlResponse::Work { request, .. } if request == "replay/2"), "{first:?}");
    topology::begin_move(&f.store, 71, &[20], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    b.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 71).await, MoveState::Done);
    assert_eq!(submit(&b, "replay/1", &t1).await, ControlResponse::Duplicate { state: "Done".into() });
    assert_eq!(b.handle(token.clone()).await, first, "moved job's poll token lost its first answer");
    assert_eq!(submit(&a, "replay/3", &t3).await, ControlResponse::Queued);
    assert_eq!(a.handle(token).await, ControlResponse::NoWork, "source gave an old token new work");
    assert!(work_of(&b).await.get("replay/1").is_none(), "compacted work recreated");
}

/// A shard added to the topology owns nothing until a move gives it buckets; a shard
/// that owns buckets or takes part in a move cannot be removed; a removed shard is
/// retired and its leader fenced.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn add_shard_takes_buckets_and_remove_shard_retires() {
    let f = fixture("w4r-membership", 2).await;
    let (a, b) = (f.plane(0), f.plane(1));
    assert_eq!(topology::add_shard(&f.store, None).await.unwrap(), 2);
    let c = f.plane(2);
    assert!(work_of(&c).await.is_empty());
    let early = in_bucket("Member.early", 3);
    assert_eq!(submit(&c, "member/early", &early).await, not_shard());
    assert_eq!(submit(&a, "member/a", &early).await, ControlResponse::Queued);
    topology::begin_move(&f.store, 81, &[3, 4], 0, 2).await.unwrap();
    a.drive_moves_now().await.unwrap();
    c.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 81).await, MoveState::Done);
    assert_eq!(work_of(&c).await.keys().cloned().collect::<Vec<_>>(), vec!["member/a".to_string()]);
    assert_eq!(submit(&c, "member/c", &in_bucket("Member.c", 4)).await, ControlResponse::Queued);
    assert!(topology::remove_shard(&f.store, 2).await.is_err(), "removed a shard owning buckets");
    assert!(topology::remove_shard(&f.store, 0).await.is_err(), "removed a shard owning buckets");
    // Hand all of shard 0's remaining buckets to shard 1, then retire it.
    let rest: Vec<u16> = topology::read_buckets(&f.store).await.unwrap().iter().enumerate()
        .filter(|(_, r)| r.shard == 0).map(|(b, _)| b as u16).collect();
    assert_eq!(rest.len(), 126);
    let old_term = a.drive_moves_now().await.unwrap();
    topology::begin_move(&f.store, 82, &rest, 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    assert!(topology::remove_shard(&f.store, 0).await.is_err(), "removed a shard in a move");
    b.drive_moves_now().await.unwrap();
    topology::remove_shard(&f.store, 0).await.unwrap();
    topology::remove_shard(&f.store, 0).await.unwrap();
    assert_eq!(topology::read_topology(&f.store).await.unwrap().members[&0], topology::MemberState::Retired);
    assert!(topology::add_shard(&f.store, Some(0)).await.is_err(), "a retired shard number was reused");
    assert_eq!(a.handle(ControlRequest::Status).await, not_shard());
    assert_eq!(a.handle(ControlRequest::Poll { worker: f.worker(0).hex() }).await, not_shard());
    assert!(a.durable().save(b"retired shard write", old_term).await.is_err(), "retired leader wrote its snapshot");
    let ts = topology::status(&f.store).await.unwrap();
    assert_eq!(ts["members"].as_array().unwrap().len(), 3);
    assert_eq!(ts["owned"]["1"].as_array().unwrap().len(), 254);
}

/// Re-running an import after the move is done merges nothing: work the destination
/// finished and compacted is not resurrected by a second import.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn second_import_does_not_resurrect_work() {
    let f = fixture("w4r-reimport", 2).await;
    let (a, b) = (f.plane(0), f.plane_gc(1));
    let w = f.worker(0);
    let target = in_bucket("Reimport.one", 30);
    assert_eq!(submit(&a, "reimport/1", &target).await, ControlResponse::Queued);
    topology::begin_move(&f.store, 91, &[30], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    b.drive_moves_now().await.unwrap();
    register(&b, w).await;
    let ControlResponse::Work { request, .. } = b.handle(ControlRequest::Poll { worker: w.hex() }).await else { panic!("poll at destination") };
    assert_eq!(b.handle(ControlRequest::Finish { worker: w.hex(), request, ok: true }).await, ControlResponse::Ok);
    let clock = Durable::new_dynamic(f.store.clone(), LEASE, 1);
    for _ in 0..4 {
        clock.tick().await.unwrap();
        b.compact_history_once().await.unwrap();
        if work_of(&b).await.is_empty() { break }
    }
    assert!(work_of(&b).await.is_empty(), "not compacted");
    let again = b.import_move_now(91).await;
    assert!(work_of(&b).await.is_empty(), "second import resurrected work");
    assert!(matches!(again, Ok(false)), "{again:?}");
    assert_eq!(submit(&b, "reimport/1", &target).await, ControlResponse::Duplicate { state: "Done".into() });
}

/// An export that would not fit one transaction aborts the move; the buckets stay.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn oversized_move_is_aborted_and_buckets_stay() {
    let f = fixture("w4r-oversize", 2).await;
    let a = f.plane(0);
    assert_eq!(submit(&a, "big/1", &in_bucket("Big.one", 50)).await, ControlResponse::Queued);
    a.durable().set_move_limit(64);
    topology::begin_move(&f.store, 101, &[50], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    let record = topology::read_move(&f.store, 101).await.unwrap().unwrap();
    assert_eq!(record.state, MoveState::Aborted);
    assert!(record.reason.contains("split the move"), "{}", record.reason);
    let bucket = topology::read_bucket(&f.store, 50).await.unwrap();
    assert_eq!((bucket.shard, bucket.moving), (0, None));
    assert!(work_of(&a).await.contains_key("big/1"));
    assert_eq!(submit(&a, "big/2", &in_bucket("Big.two", 50)).await, ControlResponse::Queued);
    // The operator aborts a prepared move the same way.
    a.durable().set_move_limit(topology::MOVE_LIMIT);
    a.pause_move_steps(true);
    topology::begin_move(&f.store, 102, &[50], 0, 1).await.unwrap();
    topology::abort_move(&f.store, 102, "operator").await.unwrap();
    assert_eq!(topology::read_bucket(&f.store, 50).await.unwrap().moving, None);
    assert_eq!(submit(&a, "big/3", &in_bucket("Big.three", 50)).await, ControlResponse::Queued);
}

/// Fixed and dynamic deployments refuse each other's controllers; topology init is
/// idempotent and refuses a fixed deployment.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn fixed_and_dynamic_topologies_refuse_each_other() {
    let keys = KeyFile::demo(1);
    let dynamic = Store::open(&StoreConfig::from_env(&deployment("w4r-modes-dyn")).unwrap(), keys.ring(), Faults::none()).unwrap();
    assert!(Durable::new_dynamic(dynamic.clone(), LEASE, 0).acquire_or_renew().await.is_err(), "dynamic before init");
    topology::init_dynamic(&dynamic, 2).await.unwrap();
    topology::init_dynamic(&dynamic, 2).await.unwrap();
    assert!(topology::init_dynamic(&dynamic, 3).await.is_err());
    assert!(Durable::new_shard(dynamic.clone(), LEASE, 0, 2).acquire_or_renew().await.is_err(), "fixed controller on dynamic topology");
    assert!(Durable::new_dynamic(dynamic.clone(), LEASE, 2).acquire_or_renew().await.is_err(), "non-member shard");
    Durable::new_dynamic(dynamic, LEASE, 1).acquire_or_renew().await.unwrap().unwrap();
    let fixed = Store::open(&StoreConfig::from_env(&deployment("w4r-modes-fixed")).unwrap(), keys.ring(), Faults::none()).unwrap();
    Durable::new_shard(fixed.clone(), LEASE, 0, 2).acquire_or_renew().await.unwrap().unwrap();
    assert!(Durable::new_dynamic(fixed.clone(), LEASE, 0).acquire_or_renew().await.is_err(), "dynamic controller on fixed topology");
    assert!(topology::init_dynamic(&fixed, 2).await.is_err());
}

fn rebind(package: &mut Package, validator: &Signer) {
    package.job = SignedJob::sign(package.job.body.clone(), &fixture::authority());
    package.receipt = fixture::receipt_for(&package.job, validator, Verdict::Accepted);
    package.marker.receipt = package.receipt.id();
    package.marker.revisions = package.revisions.iter().map(Revision::id).collect();
}

/// tests/w4_dependencies.rs after a move: the prerequisite's bucket moves to the
/// dependent's shard; publication still needs the prerequisite published first.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn cross_shard_dependency_publication_after_move() {
    let f = fixture("w4r-dependencies", 2).await;
    let (a, b) = (f.plane(0), f.plane(1));
    let (workspace, signer) = f.keys.workspace("w0").unwrap();
    let writer = Writer::new(f.store.clone(), workspace, signer);
    let validator = f.keys.validator_signer("v0").unwrap();
    let base_name = in_bucket("W4r.base", 60);
    let dependent_name = in_bucket("W4r.dependent", 200);
    for (cp, name, r) in [(&a, &base_name, "dep/base"), (&b, &dependent_name, "dep/dependent")] {
        assert!(matches!(cp.handle(ControlRequest::AssignGroup { targets: vec![name.to_string()], worker: workspace.hex(), request: r.into(), statements: vec![] }).await,
            ControlResponse::AssignedGroup { .. }));
    }
    assert_eq!(a.durable().shard_for_target(&base_name).await.unwrap(), 0);
    topology::begin_move(&f.store, 111, &[60], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    let tb = b.drive_moves_now().await.unwrap();
    assert_eq!(a.durable().shard_for_target(&base_name).await.unwrap(), 1);
    let mut base = fixture::package("w4r/base", workspace, &validator, &base_name, vec![],
        Some(writer.prepare_target(&base_name).await.unwrap()), 1);
    base.capsule = Opaque::new(Kind::Capsule, serde_json::to_vec(&serde_json::json!({"declId": base.group.id().hex()})).unwrap());
    base.revisions[0].capsule = base.capsule.id();
    base.job.body.capsule = base.capsule.id();
    rebind(&mut base, &validator);
    f.store.s3.put_opaque(&base.capsule).await.unwrap();
    let mut dependent = fixture::package("w4r/dependent", workspace, &validator, &dependent_name, vec![],
        Some(writer.prepare_target(&dependent_name).await.unwrap()), 2);
    dependent.job.body.deps = vec![base.capsule.id()];
    rebind(&mut dependent, &validator);
    let ta = a.drive_moves_now().await.unwrap();
    // The moved prerequisite's J1/J2 belong to its new shard only.
    assert!(a.durable().issue_job(&base.job, ta).await.is_err());
    for package in [&base, &dependent] {
        b.durable().issue_job(&package.job, tb).await.unwrap();
        b.durable().record_receipt(&workspace, &package.job.body.request, &package.receipt, tb).await.unwrap();
    }
    for bypass in [false, true] {
        let outcome = if bypass { writer.publish_skipping_staging_check(&dependent).await } else { writer.publish(&dependent).await };
        assert!(matches!(outcome, Err(StoreError::Guard(GuardFailure::NotPublished(_) | GuardFailure::Uncertified(_)))),
            "cross-shard prerequisite bypass: {outcome:?}");
    }
    writer.publish(&base).await.unwrap();
    writer.publish(&dependent).await.unwrap();
    assert!(f.store.target(&dependent_name).await.unwrap().unwrap().head.is_some());
    audit::audit(&f.store).await.unwrap().assert_ok();
}

struct Process(Child);
impl Drop for Process {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

async fn rpc_status(addr: &str, signer: &Signer) -> Option<serde_json::Value> {
    match rpc::call_authenticated(addr, &ControlRequest::Status, signer, &signer.public(), Duration::from_secs(1)).await {
        Ok(ControlResponse::Status { status }) => Some(status),
        _ => None,
    }
}

/// Real controller processes: `kill -9` the source leader while it is inside its
/// export and the destination leader while it is inside its import; standbys take
/// over with new terms and the move completes with every job exactly once.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn kill_nine_mid_move_completes_by_takeover() {
    let dir = scratch("w4r-processes");
    let dep = deployment("w4r-processes");
    let keys = KeyFile::demo(2);
    let keypath = dir.join("keys.json");
    paralean_control::keys::export(&keys, paralean_control::keys::Role::Controller, None).unwrap().write_private(&keypath).unwrap();
    let authority = keys.authority_signer().unwrap();
    let store = Store::open(&StoreConfig::from_env(&dep).unwrap(), keys.ring(), Faults::none()).unwrap();
    let cli = |args: &[&str]| {
        let out = Command::new(env!("CARGO_BIN_EXE_paralean-p3")).args(args)
            .env("PARALEAN_KEYS", &keypath).env("PARALEAN_DEPLOYMENT", &dep).output().unwrap();
        assert!(out.status.success(), "{args:?}: {}", String::from_utf8_lossy(&out.stderr));
        String::from_utf8(out.stdout).unwrap()
    };
    cli(&["topology", "init", "--shards", "2"]);
    let ports: Vec<_> = (0..4).map(|_| std::net::TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<String> = ports.iter().map(|p| p.local_addr().unwrap().to_string()).collect();
    drop(ports);
    let spawn = |index: usize, shard: &str, pause: Option<(&str, &str)>| {
        let log = std::fs::File::create(dir.join(format!("controller-{index}.log"))).unwrap();
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_paralean-p3"));
        cmd.args(["controller", "--listen", &addrs[index], "--validators", "127.0.0.1:1", "--lease-ms", "1200", "--shard", shard, "--dynamic"])
            .env("PARALEAN_KEYS", &keypath).env("PARALEAN_DEPLOYMENT", &dep)
            // No validation is requested; this file is only hashed for checker identity.
            .env("PARALEAN_BIN", "/bin/true")
            .env("ELAN_TOOLCHAIN", "leanprover/lean4-nightly:nightly-2026-10-03")
            .stdout(log.try_clone().unwrap()).stderr(log).stdin(Stdio::null());
        if let Some((k, v)) = pause { cmd.env(k, v); }
        Process(cmd.spawn().unwrap())
    };
    let wait_leader = |index: usize| {
        let addr = addrs[index].clone();
        let authority = authority.clone();
        let dir = dir.clone();
        async move {
            let deadline = Instant::now() + Duration::from_secs(30);
            loop {
                if let Some(s) = rpc_status(&addr, &authority).await { if s["leader"] == true { return s } }
                assert!(Instant::now() < deadline, "no leader at {addr}; logs: {}", dir.display());
                tokio::time::sleep(Duration::from_millis(50)).await;
            }
        }
    };
    let a = spawn(0, "0", Some(("PARALEAN_TEST_PAUSE_BEFORE_EXPORT_MS", "600000")));
    let b = spawn(1, "1", Some(("PARALEAN_TEST_PAUSE_BEFORE_IMPORT_MS", "600000")));
    let a_term = wait_leader(0).await["term"].as_u64().unwrap();
    let b_term = wait_leader(1).await["term"].as_u64().unwrap();
    let both = format!("{},{}", addrs[0], addrs[1]);
    let mut expected = BTreeSet::new();
    for i in 0..24 {
        let request = format!("proc/{i}");
        let req = ControlRequest::SubmitWork { request: request.clone(), target: format!("Proc.target{i}"), memory_mb: 1 };
        assert_eq!(call_controller(&both, &req, &authority, &authority.public(), Duration::from_secs(10)).await.unwrap(), ControlResponse::Queued);
        expected.insert(request);
    }
    cli(&["topology", "move", "--buckets", "0-63", "--from", "0", "--to", "1", "--id", "7"]);
    // The source leader's monitor enters the export and parks there (holding its
    // operation lock, renewing nothing). Start its standby, then kill it mid-step.
    tokio::time::sleep(Duration::from_millis(1000)).await;
    assert_eq!(move_state(&store, 7).await, MoveState::Prepared);
    let standby_a = spawn(2, "0", None);
    unsafe { assert_eq!(libc::kill(a.0.id() as i32, libc::SIGKILL), 0); }
    let killed = Instant::now();
    let deadline = Instant::now() + Duration::from_secs(30);
    while move_state(&store, 7).await == MoveState::Prepared {
        assert!(Instant::now() < deadline, "standby source never exported; logs: {}", dir.display());
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let exported_after = killed.elapsed();
    // The destination leader now parks inside its import; kill it too.
    tokio::time::sleep(Duration::from_millis(1000)).await;
    assert_eq!(move_state(&store, 7).await, MoveState::Exported);
    let standby_b = spawn(3, "1", None);
    unsafe { assert_eq!(libc::kill(b.0.id() as i32, libc::SIGKILL), 0); }
    let killed = Instant::now();
    let deadline = Instant::now() + Duration::from_secs(30);
    while move_state(&store, 7).await != MoveState::Done {
        assert!(Instant::now() < deadline, "standby destination never imported; logs: {}", dir.display());
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let imported_after = killed.elapsed();
    let sa = wait_leader(2).await;
    let sb = wait_leader(3).await;
    assert!(sa["term"].as_u64().unwrap() > a_term && sb["term"].as_u64().unwrap() > b_term);
    let work = |s: &serde_json::Value| s["work"].as_array().unwrap().iter()
        .map(|w| (w["request"].as_str().unwrap().to_string(), w["state"].as_str().unwrap().to_string())).collect::<BTreeMap<_, _>>();
    let (wa, wb) = (work(&sa), work(&sb));
    exactly_once(&[&wa, &wb], &expected);
    for r in wa.keys() {
        let target = Name::parse(&format!("Proc.target{}", r.trim_start_matches("proc/")));
        assert!(topology::name_bucket(&target) >= 64, "{r} stayed at the source");
    }
    let status = cli(&["topology", "status"]);
    assert!(status.contains("\"active_moves\": []"), "{status}");
    println!("kill -9 mid-export: standby exported after {:.3}s; kill -9 mid-import: standby imported after {:.3}s; {} jobs at source, {} at destination",
        exported_after.as_secs_f64(), imported_after.as_secs_f64(), wa.len(), wb.len());
    drop((standby_a, standby_b));
}

/// Ignored benchmark: steady submissions against 2 -> 3 -> 4 -> 3 shards while buckets
/// move (add shard, rebalance, remove shard). Reports submissions/s before, during and
/// after resharding, move durations (begin -> done) and checks every job exactly once.
#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn reshard_benchmark() {
    let f = fixture("w4r-reshard", 2).await;
    let planes: Arc<std::sync::Mutex<BTreeMap<u32, Arc<ControlPlane>>>> = Arc::new(std::sync::Mutex::new(BTreeMap::new()));
    let monitors = Arc::new(std::sync::Mutex::new(Vec::new()));
    let mut bench_cfg = f.cfg.clone();
    bench_cfg.max_work_queue = 1_000_000;
    let start_shard = |n: u32| {
        let cp = ControlPlane::new_dynamic(bench_cfg.clone(), n, GcConfig::default());
        planes.lock().unwrap().insert(n, cp.clone());
        let monitor = tokio::spawn(async move {
            loop {
                // The monitor's work without its store ticks: leases never expire here.
                cp.expire_leases().await;
                tokio::time::sleep(Duration::from_millis(25)).await;
            }
        });
        monitors.lock().unwrap().push(monitor);
    };
    start_shard(0);
    start_shard(1);
    let clients = std::env::var("W4R_RESHARD_CLIENTS").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    let submitted = Arc::new(std::sync::Mutex::new(Vec::<(Instant, String)>::new()));
    let retries = Arc::new(AtomicUsize::new(0));
    let stop = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let mut tasks = vec![];
    for c in 0..clients {
        let (planes, submitted, retries, stop) = (planes.clone(), submitted.clone(), retries.clone(), stop.clone());
        tasks.push(tokio::spawn(async move {
            let mut n = 0usize;
            while !stop.load(Ordering::SeqCst) {
                let request = format!("bench/{c}/{n}");
                let target = format!("Bench.c{c}.t{n}");
                loop {
                    let all: Vec<Arc<ControlPlane>> = planes.lock().unwrap().values().cloned().collect();
                    let mut done = false;
                    for cp in all {
                        match cp.handle(ControlRequest::SubmitWork { request: request.clone(), target: target.clone(), memory_mb: 1 }).await {
                            ControlResponse::Queued | ControlResponse::Duplicate { .. } => { done = true; break }
                            _ => {}
                        }
                    }
                    if done { break }
                    retries.fetch_add(1, Ordering::SeqCst);
                    tokio::time::sleep(Duration::from_millis(10)).await;
                }
                submitted.lock().unwrap().push((Instant::now(), request));
                n += 1;
            }
        }));
    }
    let phase = Duration::from_secs(std::env::var("W4R_RESHARD_PHASE_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(8));
    let t0 = Instant::now();
    let mut marks = vec![("2 shards".to_string(), t0)];
    tokio::time::sleep(phase).await;
    let mut moves = vec![];
    let mut next_id = 1000u64;
    let run_move = |id: u64, buckets: Vec<u16>, from: u32, to: u32| {
        let store = f.store.clone();
        async move {
            let begun = Instant::now();
            topology::begin_move(&store, id, &buckets, from, to).await.unwrap();
            let mut exported = None;
            loop {
                let m = topology::read_move(&store, id).await.unwrap().unwrap();
                if m.state == MoveState::Exported && exported.is_none() { exported = Some(begun.elapsed()) }
                if m.state == MoveState::Done { break }
                assert_ne!(m.state, MoveState::Aborted, "{}", m.reason);
                tokio::time::sleep(Duration::from_millis(5)).await;
            }
            serde_json::json!({"id": id, "buckets": buckets.len(), "from": from, "to": to, "handoff_bytes": topology::read_move(&store, id).await.unwrap().unwrap().handoff_len,
                "begin_to_done_s": begun.elapsed().as_secs_f64(), "begin_to_exported_s": exported.map(|d| d.as_secs_f64())})
        }
    };
    // 2 -> 3: add shard 2 and give it a third of each shard's buckets.
    marks.push(("resharding 2->3".into(), Instant::now()));
    let s2 = topology::add_shard(&f.store, None).await.unwrap();
    start_shard(s2);
    for (from, range) in [(0u32, 0u16..43), (1, 128..171)] {
        next_id += 1;
        moves.push(run_move(next_id, range.collect(), from, s2).await);
    }
    marks.push(("3 shards".into(), Instant::now()));
    tokio::time::sleep(phase).await;
    // 3 -> 4: add shard 3 and rebalance towards 64 buckets each.
    marks.push(("resharding 3->4".into(), Instant::now()));
    let s3 = topology::add_shard(&f.store, None).await.unwrap();
    start_shard(s3);
    for (from, range) in [(0u32, 43u16..64), (1, 171..192), (s2, 0..22)] {
        next_id += 1;
        moves.push(run_move(next_id, range.collect(), from, s3).await);
    }
    marks.push(("4 shards".into(), Instant::now()));
    tokio::time::sleep(phase).await;
    // 4 -> 3: move shard 3's buckets back and retire it.
    marks.push(("resharding 4->3".into(), Instant::now()));
    let owned: Vec<u16> = topology::read_buckets(&f.store).await.unwrap().iter().enumerate()
        .filter(|(_, r)| r.shard == s3).map(|(b, _)| b as u16).collect();
    let half = owned.len() / 2;
    for (to, part) in [(0u32, owned[..half].to_vec()), (1, owned[half..].to_vec())] {
        next_id += 1;
        moves.push(run_move(next_id, part, s3, to).await);
    }
    topology::remove_shard(&f.store, s3).await.unwrap();
    planes.lock().unwrap().remove(&s3);
    marks.push(("3 shards after removal".into(), Instant::now()));
    tokio::time::sleep(phase).await;
    let end = Instant::now();
    stop.store(true, Ordering::SeqCst);
    for t in tasks { t.await.unwrap(); }
    for m in monitors.lock().unwrap().drain(..) { m.abort(); }
    let submitted = submitted.lock().unwrap().clone();
    let mut phases = vec![];
    for (i, (name, from)) in marks.iter().enumerate() {
        let to = marks.get(i + 1).map_or(end, |(_, t)| *t);
        let count = submitted.iter().filter(|(t, _)| t >= from && *t < to).count();
        phases.push(serde_json::json!({"phase": name, "seconds": (to - *from).as_secs_f64(), "submissions": count,
            "submissions_per_second": count as f64 / (to - *from).as_secs_f64()}));
    }
    // Every submitted job exists exactly once over the remaining shards.
    let expected: BTreeSet<String> = submitted.iter().map(|(_, r)| r.clone()).collect();
    assert_eq!(expected.len(), submitted.len());
    let mut parts = vec![];
    let mut per_shard = BTreeMap::new();
    for n in [0u32, 1, s2] {
        f.expire(n).await;
        let w = work_of(&f.plane(n)).await;
        per_shard.insert(n, w.len());
        parts.push(w);
    }
    exactly_once(&parts.iter().collect::<Vec<_>>(), &expected);
    let report = serde_json::json!({
        "method": "one shared-host sample; live private FDB (w4r-b); in-process controller planes with monitor loops; direct controller API; debug build; no validation RPC",
        "clients": clients, "phase_seconds": phase.as_secs_f64(),
        "total_submitted": submitted.len(), "retried_attempts": retries.load(Ordering::SeqCst),
        "phases": phases, "moves": moves, "jobs_per_final_shard": per_shard,
        "exactly_once_verified": true,
    });
    let path = std::env::var("W4R_RESHARD_REPORT").unwrap_or_else(|_| format!("{}/results/w4r/reshard.json", common::repo().display()));
    std::fs::create_dir_all(std::path::Path::new(&path).parent().unwrap()).unwrap();
    std::fs::write(&path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    println!("{report}");
}

/// Design 1 x design 2: a dynamic shard's J1 references its envelope's objects, so the
/// store GC (enabled before the job exists, so backfill cannot cover for it) keeps them.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn dynamic_pending_jobs_protect_their_objects() {
    use paralean_store::gc::{self, GcConfig as StoreGcConfig, GcState};
    let f = fixture("w4r-shard-gc-job", 1).await;
    gc::backfill(&f.store).await.unwrap();
    gc::enable(&f.store).await.unwrap();
    let group = Opaque::new(Kind::Group, fixture::group_bytes("dyn-job"));
    let capsule = Opaque::new(Kind::Capsule, b"dynamic job capsule".to_vec());
    f.store.s3.put_opaque(&group).await.unwrap();
    f.store.s3.put_opaque(&capsule).await.unwrap();
    let job = fixture::job_by(&f.cfg.authority, "dyn-job", group.id(), capsule.id(), f.worker(0), &[]);
    let d = Durable::new_dynamic(f.store.clone(), LEASE, 0);
    let term = d.acquire_or_renew().await.unwrap().unwrap().term;
    d.issue_job(&job, term).await.unwrap();
    for _ in 0..4 { gc::sweep(&f.store, &StoreGcConfig { grace: 1 }).await.unwrap(); }
    for (kind, id) in [(Kind::Group, group.id()), (Kind::Capsule, capsule.id())] {
        let state = f.store.gc_state(kind, &id).await.unwrap();
        assert!(!matches!(state, Some(GcState::Doomed { .. } | GcState::Deleting { .. } | GcState::Gone { .. })),
            "a pending dynamic-shard job's {} was doomed: {state:?}", kind.name());
    }
}

/// The envelope request of a batch member (controller.rs `batch_request`).
fn member_request(coordinator: WorkspaceId, request: &str) -> Vec<u8> {
    format!("batch/{}/{request}", coordinator.hex()).into_bytes()
}

fn batch_member(w: WorkspaceId, request: &str, targets: &[&Name]) -> BatchMemberReq {
    BatchMemberReq::Publish {
        worker: w.hex(), request: request.into(), group: Id(paralean_store::id::sha256(request.as_bytes())).hex(),
        capsule: Id(paralean_store::id::sha256(b"capsule")).hex(), deps: vec![],
        targets: targets.iter().map(|t| TargetReq { name: t.to_string(), statement: String::new() }).collect(),
    }
}

/// Atomic batches (docs/atomic-pub-log.md) on a dynamic topology. A batch whose members'
/// buckets span shards is refused retryably before any envelope is issued (J1). Target-free
/// members take the batch's bucket, so one shard issues and fences every member even when
/// their own hash buckets belong to another shard. An in-flight batch holds its buckets
/// against export until its dispatch ends.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn dynamic_batches_issue_on_one_shard_and_drain_their_buckets() {
    let calls = Arc::new(AtomicUsize::new(0));
    let (vaddr, _validator) = slow_validator(Duration::from_millis(1500), calls.clone()).await;
    let f = fixture_with("w4r-batch", 2, vec![vaddr]).await;
    let (a, b) = (f.plane(0), f.plane(1));
    let w = f.worker(0);
    register(&a, w).await;
    register(&b, w).await;
    let mut owner = BTreeMap::new();
    for (bucket, r) in topology::read_buckets(&f.store).await.unwrap().into_iter().enumerate() { owner.insert(bucket as u16, r.shard); }
    let on = |shard: u32| *owner.iter().find(|(_, s)| **s == shard).unwrap().0;
    let job_issued = |request: &str| {
        let key = f.store.meta.keys.job_request(&w, &member_request(w, request));
        let store = f.store.clone();
        async move { store.meta.get(key).await.unwrap().is_some() }
    };
    // Members on two shards: refused before any J1, at either shard.
    let (t0, t1) = (in_bucket("Batch.zero", on(0)), in_bucket("Batch.one", on(1)));
    for (cp, t, r) in [(&a, &t0, "batch/assign0"), (&b, &t1, "batch/assign1")] {
        assert!(matches!(cp.handle(ControlRequest::AssignGroup { targets: vec![t.to_string()], worker: w.hex(), request: r.into(), statements: vec![] }).await,
            ControlResponse::AssignedGroup { .. }));
    }
    let span = ControlRequest::ValidateBatch { coordinator: w.hex(), request: "span".into(),
        members: vec![batch_member(w, "span/0", &[&t0]), batch_member(w, "span/1", &[&t1])] };
    assert_eq!(a.handle(span.clone()).await, ControlResponse::Inconclusive { reason: "batch spans controller shards".into() });
    assert_eq!(b.handle(span).await, not_shard());
    for r in ["span/0", "span/1"] { assert!(!job_issued(r).await, "a spanning batch issued member {r}") }
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    // Two target-free members whose own hash buckets are on different shards.
    let own = |r: &str| topology::validation_bucket(&w, &member_request(w, r));
    let r0 = (0..1000).map(|i| format!("free/a{i}")).find(|r| owner[&own(r)] == 0).unwrap();
    let r1 = (0..1000).map(|i| format!("free/b{i}")).find(|r| owner[&own(r)] == 1).unwrap();
    let primary = own(&r0);
    let batch = ControlRequest::ValidateBatch { coordinator: w.hex(), request: "free".into(),
        members: vec![batch_member(w, &r0, &[]), batch_member(w, &r1, &[])] };
    assert_eq!(b.handle(batch.clone()).await, not_shard(), "the batch's bucket is shard 0's");
    let a2 = a.clone();
    let req = batch.clone();
    let inflight = tokio::spawn(async move { a2.handle(req).await });
    let deadline = Instant::now() + Duration::from_secs(10);
    while calls.load(Ordering::SeqCst) == 0 {
        assert!(Instant::now() < deadline, "batch never dispatched");
        tokio::time::sleep(Duration::from_millis(20)).await;
    }
    for r in [&r0, &r1] { assert!(job_issued(r).await, "member {r} not issued") }
    let d = Durable::new_dynamic(f.store.clone(), LEASE, 0);
    assert_eq!(d.validation_route_bucket(&w, &member_request(w, &r1)).await.unwrap(), Some(primary), "a target-free member left its batch's bucket");
    topology::begin_move(&f.store, 71, &[primary], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 71).await, MoveState::Prepared, "exported with a batch in flight");
    let answer = inflight.await.unwrap();
    let ControlResponse::BatchReceipts { receipts, jobs, .. } = &answer else { panic!("drained batch: {answer:?}") };
    assert_eq!((receipts.len(), jobs.len()), (2, 2));
    a.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 71).await, MoveState::Exported);
    b.drive_moves_now().await.unwrap();
    assert_eq!(move_state(&f.store, 71).await, MoveState::Done);
    // The retry goes to the bucket's new shard and gets the recorded receipts.
    assert_eq!(a.handle(batch.clone()).await, not_shard());
    assert_eq!(b.handle(batch).await, answer, "retry at the destination");
    assert_eq!(calls.load(Ordering::SeqCst), 1, "the drained batch ran again");
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("move_preserves_every_job_exactly_once", || { move_preserves_every_job_exactly_once(); Ok(()) }),
        libtest_mimic::Trial::test("leaders_lost_around_export_and_import_complete_by_takeover", || { leaders_lost_around_export_and_import_complete_by_takeover(); Ok(()) }),
        libtest_mimic::Trial::test("stale_source_cannot_write_moved_buckets", || { stale_source_cannot_write_moved_buckets(); Ok(()) }),
        libtest_mimic::Trial::test("snapshot_saves_compare_the_loaded_generation", || { snapshot_saves_compare_the_loaded_generation(); Ok(()) }),
        libtest_mimic::Trial::test("stale_leader_export_is_fenced_by_lease", || { stale_leader_export_is_fenced_by_lease(); Ok(()) }),
        libtest_mimic::Trial::test("inflight_validation_is_drained_before_export", || { inflight_validation_is_drained_before_export(); Ok(()) }),
        libtest_mimic::Trial::test("compacted_work_and_poll_tokens_resolve_across_shards", || { compacted_work_and_poll_tokens_resolve_across_shards(); Ok(()) }),
        libtest_mimic::Trial::test("add_shard_takes_buckets_and_remove_shard_retires", || { add_shard_takes_buckets_and_remove_shard_retires(); Ok(()) }),
        libtest_mimic::Trial::test("second_import_does_not_resurrect_work", || { second_import_does_not_resurrect_work(); Ok(()) }),
        libtest_mimic::Trial::test("oversized_move_is_aborted_and_buckets_stay", || { oversized_move_is_aborted_and_buckets_stay(); Ok(()) }),
        libtest_mimic::Trial::test("fixed_and_dynamic_topologies_refuse_each_other", || { fixed_and_dynamic_topologies_refuse_each_other(); Ok(()) }),
        libtest_mimic::Trial::test("cross_shard_dependency_publication_after_move", || { cross_shard_dependency_publication_after_move(); Ok(()) }),
        libtest_mimic::Trial::test("dynamic_pending_jobs_protect_their_objects", || { dynamic_pending_jobs_protect_their_objects(); Ok(()) }),
        libtest_mimic::Trial::test("dynamic_batches_issue_on_one_shard_and_drain_their_buckets", || { dynamic_batches_issue_on_one_shard_and_drain_their_buckets(); Ok(()) }),
        libtest_mimic::Trial::test("kill_nine_mid_move_completes_by_takeover", || { kill_nine_mid_move_completes_by_takeover(); Ok(()) }),
        libtest_mimic::Trial::test("reshard_benchmark", || { reshard_benchmark(); Ok(()) }).with_ignored_flag(true),
    ]);
}
