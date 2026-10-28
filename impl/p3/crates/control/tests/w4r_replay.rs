//! Live W4-rest replay-horizon regressions (docs/w4-rest-log.md, design 3). No Lean checker.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::sync::Arc;
use std::time::Duration;

use common::deployment;
use foundationdb::options::StreamingMode;
use foundationdb::{KeySelector, RangeOption};
use paralean_control::controller::{replay_generation_hint, ControlCall, ControlPlane, ControlRequest, ControlResponse, ControllerConfig, TargetReq};
use paralean_control::durable::{Durable, PollReplay, TerminalState, WorkReplay};
use paralean_control::gc::GcConfig;
use paralean_control::replay::{ReplayConfig, ReplayGen};
use paralean_control::worker::WorkerNode;
use paralean_store::id::sha256;
use paralean_store::*;

/// The identity of `id` in generation `g > 0`, spelled out here rather than taken from
/// the library (docs/w4-rest-log.md design 3), so a mutated encoding cannot agree with itself.
fn scoped_id(g: u64, id: &str) -> String {
    format!("\u{1e}{g}/{id}")
}

/// Replay horizon of every test, in shard-clock ticks.
const H: u64 = 4;

fn config(store: Store, keys: &KeyFile) -> ControllerConfig {
    ControllerConfig {
        store, authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 1024, max_validations: 4,
        validation_deadline: Duration::from_secs(1), validation_memory_mb: 128,
        validator_attempts: 1,
    }
}

fn gc_on(grace_ticks: u64) -> GcConfig {
    GcConfig { enabled: true, grace_ticks, scan_limit: 128 }
}

fn horizon(grace_ticks: u64, require_generation: bool) -> ReplayConfig {
    ReplayConfig { horizon_ticks: Some(H), grace_ticks, require_generation }
}

struct Case {
    store: Store,
    keys: KeyFile,
    ctl: Arc<ControlPlane>,
    clock: Durable,
}

fn case(name: &str, gc: GcConfig, replay: ReplayConfig) -> Case {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment(name)).unwrap(), keys.ring(), Faults::none()).unwrap();
    let cfg = config(store.clone(), &keys);
    let ctl = ControlPlane::new_shard_with_replay(cfg.clone(), 0, 1, gc, replay);
    let clock = Durable::new(store.clone(), cfg.lease);
    Case { store, keys, ctl, clock }
}

impl Case {
    async fn call(&self, generation: u64, req: ControlRequest) -> ControlResponse {
        self.ctl.handle_call(ControlCall::scoped(generation, req)).await
    }
    async fn tick(&self, n: u64) {
        for _ in 0..n { self.clock.tick().await.unwrap(); }
    }
    /// Start generation 1 and advance to `target`, `H` ticks per step.
    async fn advance_to(&self, target: u64) {
        loop {
            let g = self.ctl.advance_replay().await.unwrap();
            if g.generation >= target {
                assert_eq!(g.generation, target);
                return;
            }
            self.tick(H).await;
        }
    }
    async fn generation(&self) -> u64 {
        self.clock.replay_generation().await.unwrap().generation
    }
    async fn status(&self) -> serde_json::Value {
        let ControlResponse::Status { status } = self.ctl.handle(ControlRequest::Status).await else { panic!("no status") };
        status
    }
    async fn work_state(&self, identity: &str) -> Option<String> {
        self.status().await["work"].as_array().unwrap().iter()
            .find(|j| j["request"] == identity).map(|j| j["state"].as_str().unwrap().to_string())
    }
    async fn register(&self, worker: WorkspaceId) {
        assert!(matches!(self.call(0, ControlRequest::Register { worker: worker.hex(), capacity_mb: 1024 }).await,
            ControlResponse::Registered { .. }));
    }
    /// Let settled history age past a one-tick grace and move it to replay rows.
    async fn compact(&self) {
        self.tick(1).await;
        for _ in 0..8 {
            let r = self.ctl.compact_history_once().await.unwrap();
            if r.compacted_work == 0 && r.compacted_polls == 0 { break }
        }
    }
    fn legacy_row_key(&self, kind: &str, id: &str) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", 0u64, kind, foundationdb::tuple::Bytes::from(&sha256(id.as_bytes())[..])))
    }
    /// Every key of `sub` with its value's length, paged.
    async fn scan(&self, sub: &foundationdb::tuple::Subspace) -> Vec<(Vec<u8>, usize)> {
        let (begin, end) = sub.range();
        let mut out: Vec<(Vec<u8>, usize)> = Vec::new();
        loop {
            let start = match out.last() {
                Some((k, _)) => KeySelector::first_greater_than(k.clone()),
                None => KeySelector::first_greater_or_equal(begin.clone()),
            };
            let opt = RangeOption { limit: Some(1000), mode: StreamingMode::WantAll,
                ..RangeOption::from((start, KeySelector::first_greater_or_equal(end.clone()))) };
            let trx = self.store.meta.db.create_trx().unwrap();
            let page = trx.get_range(&opt, 1, false).await.unwrap();
            let more = page.more();
            out.extend(page.iter().map(|kv| (kv.key().to_vec(), kv.value().len())));
            if !more { return out }
        }
    }
    /// (generation, kind) of every generation-scoped replay row.
    async fn scoped_rows(&self) -> Vec<(u64, String)> {
        let sub = self.clock.replay_rows_subspace();
        self.scan(&sub).await.into_iter()
            .map(|(k, _)| { let (g, kind, _): (u64, String, Vec<u8>) = sub.unpack(&k).unwrap(); (g, kind) })
            .collect()
    }
    /// Replay rows of every generation (W4's legacy keys and the scoped ranges): count, bytes.
    async fn replay_footprint(&self) -> (usize, usize) {
        let root = &self.store.meta.keys.root;
        let mut subs = vec![self.clock.replay_rows_subspace()];
        for kind in ["history-work", "history-poll"] { subs.push(root.subspace(&("controller", "shard", 0u64, kind))); }
        let (mut rows, mut bytes) = (0, 0);
        for sub in &subs {
            for (k, v) in self.scan(sub).await { rows += 1; bytes += k.len() + v; }
        }
        (rows, bytes)
    }
}

fn submit(request: &str, target: &str) -> ControlRequest {
    ControlRequest::SubmitWork { request: request.into(), target: target.into(), memory_mb: 1 }
}

fn poll(worker: WorkspaceId, token: &str) -> ControlRequest {
    ControlRequest::PollRequest { worker: worker.hex(), request: token.into() }
}

fn cancel(request: &str) -> ControlRequest {
    ControlRequest::Cancel { request: request.into(), worker: String::new() }
}

fn validate(worker: WorkspaceId, request: &str, target: &str) -> ControlRequest {
    ControlRequest::Validate {
        worker: worker.hex(), request: request.into(), group: Id(sha256(b"w4r-group")).hex(),
        capsule: Id(sha256(b"w4r-capsule")).hex(), deps: vec![],
        targets: vec![TargetReq { name: target.into(), statement: String::new() }], memory_mb: 0, deadline_ms: 0,
    }
}

fn is_expired(r: &ControlResponse) -> bool {
    matches!(r, ControlResponse::Refused { reason } if reason.starts_with("expired replay generation"))
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn legacy_generation_zero_is_unchanged_and_never_retired() {
    let c = case("w4r-legacy", gc_on(1), horizon(1, false));
    c.advance_to(1).await;
    let (worker, _) = c.keys.workspace("w0").unwrap();
    // A legacy client learns nothing new and keeps W4's identities and row keys.
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 1024 }).await,
        ControlResponse::Registered { replay_generation: 0, .. }));
    assert_eq!(c.ctl.handle(submit("legacy/a", "Replay.Legacy.A")).await, ControlResponse::Queued);
    assert_eq!(c.ctl.handle(submit("legacy/a", "Replay.Legacy.A")).await, ControlResponse::Duplicate { state: "Queued".into() });
    let work = c.ctl.handle(poll(worker, "legacy/tok")).await;
    assert!(matches!(&work, ControlResponse::Work { request, .. } if request == "legacy/a"), "{work:?}");
    assert_eq!(c.ctl.handle(ControlRequest::Finish { worker: worker.hex(), request: "legacy/a".into(), ok: true }).await,
        ControlResponse::Ok);
    c.compact().await;
    assert!(c.clock.work_replay("legacy/a").await.unwrap().is_some());
    for (kind, id) in [("history-work", "legacy/a"), ("history-poll", "legacy/tok")] {
        assert!(c.store.meta.get(c.legacy_row_key(kind, id)).await.unwrap().is_some(), "{kind} row not at its W4 key");
    }
    assert!(c.scoped_rows().await.is_empty(), "a generation-0 row left W4's key space");

    // Many generations later, after grace, the collector leaves generation 0 alone.
    c.advance_to(5).await;
    c.tick(2).await;
    let report = c.ctl.collect_replay().await.unwrap();
    assert_eq!(report.generation, 5);
    for (kind, id) in [("history-work", "legacy/a"), ("history-poll", "legacy/tok")] {
        assert!(c.store.meta.get(c.legacy_row_key(kind, id)).await.unwrap().is_some(), "generation-0 {kind} row was deleted");
    }
    c.register(worker).await;
    assert_eq!(c.ctl.handle(submit("legacy/a", "Replay.Legacy.A")).await, ControlResponse::Duplicate { state: "Done".into() });
    assert!(matches!(c.ctl.handle(submit("legacy/a", "Replay.Legacy.Other")).await, ControlResponse::Refused { .. }));
    assert_eq!(c.ctl.handle(submit("legacy/b", "Replay.Legacy.B")).await, ControlResponse::Queued);
    assert_eq!(c.ctl.handle(poll(worker, "legacy/tok")).await, ControlResponse::NoWork,
        "a legacy poll token took new work");
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn in_window_duplicates_are_deduplicated_after_compaction() {
    let c = case("w4r-window", gc_on(1), horizon(2, false));
    c.advance_to(1).await;
    let id = scoped_id(1, "dup");
    assert_eq!(c.call(1, submit("dup", "Replay.Dup")).await, ControlResponse::Queued);
    assert_eq!(c.call(1, submit("dup", "Replay.Dup")).await, ControlResponse::Duplicate { state: "Queued".into() });
    assert!(matches!(c.call(1, submit("dup", "Replay.Other")).await, ControlResponse::Refused { .. }));
    assert_eq!(c.work_state(&id).await.as_deref(), Some("Queued"), "the identity does not name its generation");
    assert_eq!(c.call(1, cancel("dup")).await, ControlResponse::Cancelled);
    c.compact().await;
    assert!(c.clock.work_replay(&id).await.unwrap().is_some());
    assert!(c.clock.work_replay("dup").await.unwrap().is_none());
    assert_eq!(c.scoped_rows().await, vec![(1, "work".to_string())]);
    assert_eq!(c.work_state(&id).await, None, "compaction left the request in the snapshot");

    // Generation 1 is now G - 1: still accepted, still deduplicated by its row, even
    // after a collection pass once the grace has passed.
    c.advance_to(2).await;
    c.tick(3).await;
    assert_eq!(c.ctl.collect_replay().await.unwrap().deleted_rows, 0, "a row of an accepted generation was deleted");
    assert_eq!(c.scoped_rows().await, vec![(1, "work".to_string())]);
    assert_eq!(c.call(1, submit("dup", "Replay.Dup")).await, ControlResponse::Duplicate { state: "Cancelled".into() });
    assert!(matches!(c.call(1, submit("dup", "Replay.Other")).await, ControlResponse::Refused { .. }));
    // The same ID in another generation is another request.
    assert_eq!(c.call(2, submit("dup", "Replay.Dup")).await, ControlResponse::Queued);
    assert_eq!(c.call(2, submit("dup", "Replay.Dup")).await, ControlResponse::Duplicate { state: "Queued".into() });
    assert_eq!(c.work_state(&scoped_id(2, "dup")).await.as_deref(), Some("Queued"));
    // A legacy client cannot alias the scoped identity under generation 0.
    assert_eq!(c.ctl.handle(submit(&id, "Replay.Dup")).await, ControlResponse::Duplicate { state: "Cancelled".into() });
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn retired_generations_are_refused_before_and_after_their_rows_go() {
    let c = case("w4r-retired", gc_on(1), horizon(2, false));
    c.advance_to(1).await;
    assert_eq!(c.call(1, submit("old", "Replay.Old")).await, ControlResponse::Queued);
    assert_eq!(c.call(1, cancel("old")).await, ControlResponse::Cancelled);
    assert_eq!(c.call(1, submit("old-active", "Replay.OldActive")).await, ControlResponse::Queued);
    c.compact().await;
    assert!(c.clock.work_replay(&scoped_id(1, "old")).await.unwrap().is_some());

    c.advance_to(3).await;
    let refused_at = c.clock.replay_refused_tick(1).await.unwrap().expect("generation 1 refusal not recorded");
    assert_eq!(refused_at, c.clock.replay_generation().await.unwrap().started_tick);
    assert_eq!(c.clock.replay_refused_tick(2).await.unwrap(), None);
    // Refused while its row still exists: neither a duplicate answer nor new work.
    for id in ["old", "fresh"] {
        let r = c.call(1, submit(id, "Replay.Old")).await;
        assert!(is_expired(&r), "{id}: {r:?}");
        assert_eq!(replay_generation_hint(&r), Some(3));
    }
    assert_eq!(c.work_state(&scoped_id(1, "fresh")).await, None, "a retired generation created work");
    // Not yet refused for the grace period: nothing is deleted.
    let early = c.ctl.collect_replay().await.unwrap();
    assert_eq!(early.deleted_rows, 0, "rows deleted before grace: {early:?}");
    assert!(c.clock.work_replay(&scoped_id(1, "old")).await.unwrap().is_some());

    c.tick(2).await;
    let report = c.ctl.collect_replay().await.unwrap();
    assert_eq!(report.deleted_rows, 1, "{report:?}");
    assert!(report.deleted_bytes > 0);
    assert!(c.clock.work_replay(&scoped_id(1, "old")).await.unwrap().is_none());
    assert!(c.scoped_rows().await.is_empty());
    // Refused after its row is gone too, and the current snapshot was not touched.
    for id in ["old", "fresh"] {
        let r = c.call(1, submit(id, "Replay.Old")).await;
        assert!(is_expired(&r), "{id}: {r:?}");
    }
    assert_eq!(c.work_state(&scoped_id(1, "old")).await, None);
    assert_eq!(c.work_state(&scoped_id(1, "old-active")).await.as_deref(), Some("Queued"), "retirement touched active work");
    assert_eq!(c.call(2, submit("in-window", "Replay.Window")).await, ControlResponse::Queued);
    // Counters: the report and Status agree with the durable totals.
    let stats = c.clock.replay_stats().await.unwrap();
    assert_eq!((stats.deleted_rows, stats.deleted_bytes), (1, report.deleted_bytes as u64));
    let status = c.status().await;
    assert_eq!(status["replay_generation"], 3);
    assert_eq!(status["replay_deleted_rows"], 1);
    assert_eq!(status["replay_deleted_bytes"], report.deleted_bytes as u64);
    assert_eq!(status["replay_horizon_ticks"], H);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn retirement_and_advance_need_the_fenced_leader() {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment("w4r-fence")).unwrap(), keys.ring(), Faults::none()).unwrap();
    let lease = Duration::from_millis(500);
    let replay = horizon(2, false);
    let stale = Durable::new(store.clone(), lease);
    let term = stale.acquire_or_renew().await.unwrap().unwrap().term;
    assert_eq!(stale.advance_replay_generation(term, H).await.unwrap().generation, 1);
    let work = WorkReplay { request: scoped_id(1, "fenced/w"), target: "Replay.Fenced".into(), memory_mb: 1, state: TerminalState::Done };
    let token = PollReplay { token: scoped_id(1, "fenced/p"), worker: "w".into(), work: None, epoch: None };
    let legacy = WorkReplay { request: "fenced/legacy".into(), target: "Replay.Fenced".into(), memory_mb: 1, state: TerminalState::Done };
    stale.save_with_history(b"fenced-head", term, &[work.clone(), legacy.clone()], &[token.clone()]).await.unwrap();
    for g in 2..=3 {
        for _ in 0..H { stale.tick().await.unwrap(); }
        assert_eq!(stale.acquire_or_renew().await.unwrap().unwrap().term, term);
        assert_eq!(stale.advance_replay_generation(term, H).await.unwrap().generation, g);
    }
    // Generation 1 has been refused for longer than the grace, then the leader is replaced.
    for _ in 0..9 { stale.tick().await.unwrap(); }
    let successor = Durable::new(store.clone(), lease);
    let new_term = successor.acquire_or_renew().await.unwrap().unwrap().term;
    assert!(new_term > term);
    let gc = gc_on(1);
    assert!(stale.collect_replay_rows(term, &replay, &gc).await.is_err(), "a stale leader retired replay rows");
    assert_eq!(successor.work_replay(&work.request).await.unwrap(), Some(work.clone()));
    let before = successor.replay_generation().await.unwrap();
    assert!(stale.advance_replay_generation(term, H).await.is_err(), "a stale leader advanced the generation");
    assert_eq!(successor.replay_generation().await.unwrap(), before);
    assert_eq!(before.generation, 3);
    // The fenced leader deletes both rows of generation 1 and nothing else.
    let report = successor.collect_replay_rows(new_term, &replay, &gc).await.unwrap();
    assert_eq!(report.deleted_rows, 2, "{report:?}");
    assert!(successor.work_replay(&work.request).await.unwrap().is_none());
    assert!(successor.poll_replay(&token.token).await.unwrap().is_none());
    assert_eq!(successor.work_replay("fenced/legacy").await.unwrap(), Some(legacy));
    let stats = successor.replay_stats().await.unwrap();
    assert_eq!((stats.deleted_rows, stats.deleted_bytes), (2, report.deleted_bytes as u64));
    assert_eq!(successor.collect_replay_rows(new_term, &replay, &gc).await.unwrap().deleted_rows, 0);
    // Retirement is opt-in.
    assert!(successor.collect_replay_rows(new_term, &replay, &GcConfig::default()).await.is_err());
}

/// Design 2 x design 3: a request's bucket can move between shards, and its retries
/// follow it. The generation window is deployment-wide, so a retry that lands at the
/// destination after the source retired the request's row is refused, never executed.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn dynamic_generations_follow_requests_across_moves() {
    use paralean_control::topology;
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment("w4r-dyn-replay")).unwrap(), keys.ring(), Faults::none()).unwrap();
    topology::init_dynamic(&store, 2).await.unwrap();
    let cfg = config(store.clone(), &keys);
    let a = ControlPlane::new_dynamic_with_replay(cfg.clone(), 0, gc_on(1), horizon(1, false));
    let b = ControlPlane::new_dynamic_with_replay(cfg.clone(), 1, gc_on(1), horizon(1, false));
    let clock_a = Durable::new_dynamic(store.clone(), cfg.lease, 0);
    let target = (0..100_000).map(|i| format!("Replay.Moved{i}"))
        .find(|t| topology::name_bucket(&Name::parse(t)) == 5).unwrap();
    let bucket = topology::name_bucket(&Name::parse(&target));
    assert_eq!(topology::read_bucket(&store, bucket).await.unwrap().shard, 0);
    let call = |cp: &Arc<ControlPlane>, g: u64, req: ControlRequest| { let cp = cp.clone(); async move { cp.handle_call(ControlCall::scoped(g, req)).await } };

    assert_eq!(a.advance_replay().await.unwrap().generation, 1);
    assert_eq!(b.advance_replay().await.unwrap().generation, 1, "the destination has its own generation");
    assert_eq!(call(&a, 1, submit("moved", &target)).await, ControlResponse::Queued);
    assert_eq!(call(&a, 1, cancel("moved")).await, ControlResponse::Cancelled);
    clock_a.tick().await.unwrap();
    while a.compact_history_once().await.unwrap().compacted_work > 0 {}

    topology::begin_move(&store, 7, &[bucket], 0, 1).await.unwrap();
    a.drive_moves_now().await.unwrap();
    b.drive_moves_now().await.unwrap();
    // In the window: the destination answers from the source's row.
    assert_eq!(call(&b, 1, submit("moved", &target)).await, ControlResponse::Duplicate { state: "Cancelled".into() });

    // The source (the lowest active shard) advances twice and retires generation 1.
    for _ in 0..2 {
        for _ in 0..H { clock_a.tick().await.unwrap(); }
        a.advance_replay().await.unwrap();
    }
    b.advance_replay().await.unwrap();
    for _ in 0..4 { clock_a.tick().await.unwrap(); a.collect_replay().await.unwrap(); }
    assert!(clock_a.work_replay(&scoped_id(1, "moved")).await.unwrap().is_none(), "the source kept its row");
    let r = call(&b, 1, submit("moved", &target)).await;
    assert!(is_expired(&r), "a retry of a retired request was not refused at the destination: {r:?}");
    let ControlResponse::Status { status } = b.handle(ControlRequest::Status).await else { panic!("no status") };
    assert!(status["work"].as_array().unwrap().iter().all(|j| j["request"] != scoped_id(1, "moved")), "the retry executed again");
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn retired_poll_tokens_cannot_take_new_work() {
    let c = case("w4r-poll", GcConfig::default(), horizon(2, false));
    c.advance_to(1).await;
    let (worker, _) = c.keys.workspace("w0").unwrap();
    c.register(worker).await;
    assert_eq!(c.call(1, poll(worker, "tok")).await, ControlResponse::NoWork);
    c.advance_to(3).await;
    c.register(worker).await;
    assert_eq!(c.call(3, submit("job", "Replay.Poll.Job")).await, ControlResponse::Queued);
    for token in ["tok", "fresh"] {
        let r = c.call(1, poll(worker, token)).await;
        assert!(is_expired(&r), "a generation-1 token {token}: {r:?}");
    }
    assert_eq!(c.work_state(&scoped_id(3, "job")).await.as_deref(), Some("Queued"), "a retired token took the job");
    let work = c.call(2, poll(worker, "cur")).await;
    assert!(matches!(&work, ControlResponse::Work { request, .. } if *request == scoped_id(3, "job")), "{work:?}");
    assert_eq!(c.call(2, poll(worker, "cur")).await, work);
    assert!(matches!(c.call(4, poll(worker, "ahead")).await, ControlResponse::Refused { reason } if reason.contains("ahead")));
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn active_work_of_an_old_generation_still_finishes() {
    let c = case("w4r-active", gc_on(1), horizon(1, false));
    c.advance_to(1).await;
    let (worker, _) = c.keys.workspace("w0").unwrap();
    c.register(worker).await;
    assert_eq!(c.call(1, submit("long", "Replay.Active")).await, ControlResponse::Queued);
    assert_eq!(c.call(1, submit("long-cancel", "Replay.ActiveCancel")).await, ControlResponse::Queued);
    let id = match c.call(1, poll(worker, "p")).await {
        ControlResponse::Work { request, .. } => request,
        other => panic!("no work: {other:?}"),
    };
    assert_eq!(id, scoped_id(1, "long"));
    c.advance_to(4).await;
    c.tick(2).await;
    c.ctl.collect_replay().await.unwrap();
    assert_eq!(c.ctl.handle(ControlRequest::Heartbeat { worker: worker.hex() }).await, ControlResponse::Ok);
    // The worker validates under the work ID it was given: not refused for its generation
    // (no validator is configured here, so the dispatch itself is inconclusive).
    let v = c.ctl.handle(validate(worker, &id, "Replay.Active")).await;
    assert!(matches!(&v, ControlResponse::Inconclusive { reason } if reason.contains("no validators")), "{v:?}");
    // A new validation ID in the retired generation is refused.
    let v = c.call(1, validate(worker, "dep/x", "Replay.Active")).await;
    assert!(is_expired(&v), "{v:?}");
    assert_eq!(c.ctl.handle(ControlRequest::Finish { worker: worker.hex(), request: id.clone(), ok: true }).await, ControlResponse::Ok);
    assert_eq!(c.work_state(&id).await.as_deref(), Some("Done"));
    assert_eq!(c.call(1, cancel("long-cancel")).await, ControlResponse::Cancelled);
    assert_eq!(c.work_state(&scoped_id(1, "long-cancel")).await.as_deref(), Some("Cancelled"));
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn require_replay_generation_refuses_generation_zero() {
    let c = case("w4r-require", GcConfig::default(), horizon(2, true));
    c.advance_to(1).await;
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 1024 }).await,
        ControlResponse::Registered { .. }));
    for r in [c.ctl.handle(submit("legacy", "Replay.Require")).await, c.call(0, submit("zero", "Replay.Require")).await,
              c.ctl.handle(poll(worker, "legacy-token")).await] {
        assert!(matches!(&r, ControlResponse::Refused { reason } if reason.starts_with("replay generation required")), "{r:?}");
        assert_eq!(replay_generation_hint(&r), Some(1));
    }
    assert_eq!(c.work_state("legacy").await, None);
    assert_eq!(c.work_state("zero").await, None);
    assert_eq!(c.ctl.handle(ControlRequest::Poll { worker: worker.hex() }).await, ControlResponse::NoWork);
    assert_eq!(c.call(1, submit("scoped", "Replay.Require")).await, ControlResponse::Queued);
    assert_eq!(c.status().await["replay_require_generation"], true);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn workers_learn_and_follow_the_generation_over_rpc() {
    let c = case("w4r-worker", GcConfig::default(), ReplayConfig { horizon_ticks: Some(1_000_000), ..ReplayConfig::default() });
    assert_eq!(c.ctl.advance_replay().await.unwrap().generation, 1);
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap().to_string();
    let service = c.ctl.serve(listener);
    let path = std::env::temp_dir().join(deployment("w4r-empty-p1"));
    std::fs::create_dir_all(path.join("meta")).unwrap();
    let (id, signer) = c.keys.workspace("w0").unwrap();
    let worker = WorkerNode::new(Writer::new(c.store.clone(), id, signer), &addr, 1024, &path).unwrap();
    assert!(matches!(worker.register().await.unwrap(), ControlResponse::Registered { replay_generation: 1, .. }));
    assert_eq!(worker.replay_generation(&addr), 1);
    let heartbeats = worker.spawn_heartbeats(Duration::from_millis(50));
    assert_eq!(c.call(1, submit("w/one", "Replay.Worker.One")).await, ControlResponse::Queued);
    let first = worker.poll().await.unwrap().expect("no work");
    assert_eq!(first.request, scoped_id(1, "w/one"));
    // The shard moves on two generations: the worker's next poll is refused, it learns
    // the generation from the refusal and polls again in it.
    let now = c.clock.clock().await.unwrap();
    let key = c.store.meta.keys.root.pack(&("controller", "shard", 0u64, "replay-gen"));
    let trx = c.store.meta.db.create_trx().unwrap();
    trx.set(&key, &serde_json::to_vec(&ReplayGen { generation: 3, started_tick: now, clock_shard: None }).unwrap());
    trx.commit().await.unwrap();
    assert_eq!(c.generation().await, 3);
    assert_eq!(c.call(3, submit("w/two", "Replay.Worker.Two")).await, ControlResponse::Queued);
    let second = worker.poll().await.unwrap().expect("no work after a generation change");
    assert_eq!(second.request, scoped_id(3, "w/two"));
    assert_eq!(worker.replay_generation(&addr), 3);
    // Old-generation work still finishes through the worker's ordinary path.
    assert_eq!(worker.call(&ControlRequest::Finish { worker: id.hex(), request: first.request.clone(), ok: true }).await.unwrap(),
        ControlResponse::Ok);
    heartbeats.abort();
    service.abort();
}

/// Measurement (not a regression): replay rows retained over a run of terminal requests
/// across several generations, with a horizon and without. Writes `W4R_REPLAY_REPORT`
/// (default `results/w4r/replay.json` at the repository root).
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn replay_rows_with_and_without_a_horizon() {
    const PHASES: u64 = 8;
    const REQUESTS: usize = 64;
    const POLLS: usize = 16;
    let mut legs = serde_json::Map::new();
    for with_horizon in [true, false] {
        let replay = if with_horizon { horizon(1, false) } else { ReplayConfig::default() };
        let c = case(if with_horizon { "w4r-measure-h" } else { "w4r-measure-0" }, gc_on(1), replay);
        let (worker, _) = c.keys.workspace("w0").unwrap();
        if with_horizon { c.advance_to(1).await; }
        let started = std::time::Instant::now();
        let mut samples = Vec::new();
        for phase in 0..PHASES {
            c.register(worker).await;
            let g = c.generation().await;
            for i in 0..REQUESTS {
                let request = format!("measure/{phase}/{i}");
                assert_eq!(c.call(g, submit(&request, &format!("Replay.Measure.p{phase}.t{i}"))).await, ControlResponse::Queued);
                assert_eq!(c.call(g, cancel(&request)).await, ControlResponse::Cancelled);
            }
            for i in 0..POLLS {
                assert_eq!(c.call(g, poll(worker, &format!("measure-poll/{phase}/{i}"))).await, ControlResponse::NoWork);
            }
            c.compact().await;
            c.tick(H).await;
            if with_horizon {
                c.ctl.advance_replay().await.unwrap();
                c.ctl.collect_replay().await.unwrap();
            }
            let (rows, bytes) = c.replay_footprint().await;
            let stats = c.clock.replay_stats().await.unwrap();
            samples.push(serde_json::json!({
                "phase": phase, "generation_written": g, "generation_after": c.generation().await,
                "rows_retained": rows, "bytes_retained": bytes,
                "rows_deleted": stats.deleted_rows, "bytes_deleted": stats.deleted_bytes,
            }));
        }
        legs.insert(if with_horizon { "with_horizon" } else { "without_horizon" }.into(), serde_json::json!({
            "samples": samples, "seconds": started.elapsed().as_secs_f64(),
        }));
    }
    let report = serde_json::json!({
        "description": "Replay rows (W4 history-work/history-poll and W4-rest replay-rows) retained on one shard after each phase of terminal requests; each phase's requests are cancelled and compacted to replay rows, then the shard clock advances one horizon.",
        "phases": PHASES, "requests_per_phase": REQUESTS, "poll_tokens_per_phase": POLLS,
        "horizon_ticks": H, "replay_grace_ticks": 1, "history_grace_ticks": 1,
        "legs": legs,
    });
    let path = std::env::var("W4R_REPLAY_REPORT").map(std::path::PathBuf::from)
        .unwrap_or_else(|_| common::repo().join("results/w4r/replay.json"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(&path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("legacy_generation_zero_is_unchanged_and_never_retired", || { legacy_generation_zero_is_unchanged_and_never_retired(); Ok(()) }),
        libtest_mimic::Trial::test("in_window_duplicates_are_deduplicated_after_compaction", || { in_window_duplicates_are_deduplicated_after_compaction(); Ok(()) }),
        libtest_mimic::Trial::test("retired_generations_are_refused_before_and_after_their_rows_go", || { retired_generations_are_refused_before_and_after_their_rows_go(); Ok(()) }),
        libtest_mimic::Trial::test("retirement_and_advance_need_the_fenced_leader", || { retirement_and_advance_need_the_fenced_leader(); Ok(()) }),
        libtest_mimic::Trial::test("retired_poll_tokens_cannot_take_new_work", || { retired_poll_tokens_cannot_take_new_work(); Ok(()) }),
        libtest_mimic::Trial::test("active_work_of_an_old_generation_still_finishes", || { active_work_of_an_old_generation_still_finishes(); Ok(()) }),
        libtest_mimic::Trial::test("require_replay_generation_refuses_generation_zero", || { require_replay_generation_refuses_generation_zero(); Ok(()) }),
        libtest_mimic::Trial::test("dynamic_generations_follow_requests_across_moves", || { dynamic_generations_follow_requests_across_moves(); Ok(()) }),
        libtest_mimic::Trial::test("workers_learn_and_follow_the_generation_over_rpc", || { workers_learn_and_follow_the_generation_over_rpc(); Ok(()) }),
        libtest_mimic::Trial::test("replay_rows_with_and_without_a_horizon", || { replay_rows_with_and_without_a_horizon(); Ok(()) }).with_ignored_flag(true),
    ]);
}
