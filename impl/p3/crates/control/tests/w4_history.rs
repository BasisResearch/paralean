//! Live W4 controller-history compaction and replay regressions. No Lean checker.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::sync::Arc;
use std::time::Duration;

use common::deployment;
use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::durable::{Durable, PollReplay, TerminalState, WorkReplay};
use paralean_control::gc::GcConfig;
use paralean_store::id::sha256;
use paralean_store::*;

// The crash-window test uses a process-wide fault hook; keep this test binary serial.
static HISTORY_TEST_LOCK: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

fn config(store: Store, keys: &KeyFile) -> ControllerConfig {
    ControllerConfig {
        store, authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 32, max_validations: 1,
        validation_deadline: Duration::from_secs(1), validation_memory_mb: 128,
        validator_attempts: 1,
    }
}

fn enabled(grace_ticks: u64) -> GcConfig {
    GcConfig { enabled: true, grace_ticks, scan_limit: 128 }
}

fn submit(request: &str, target: &str, memory_mb: u64) -> ControlRequest {
    ControlRequest::SubmitWork { request: request.into(), target: target.into(), memory_mb }
}

fn poll(worker: WorkspaceId, token: &str) -> ControlRequest {
    ControlRequest::PollRequest { worker: worker.hex(), request: token.into() }
}

fn is_refused(response: ControlResponse) -> bool {
    matches!(response, ControlResponse::Refused { .. })
}

async fn head(store: &Store, shard: u32) -> serde_json::Value {
    let key = store.meta.keys.root.pack(&("controller", "shard", shard as u64, "state"));
    serde_json::from_slice(&store.meta.get(key).await.unwrap().unwrap()).unwrap()
}

async fn snapshot_bytes(store: &Store, shard: u32, h: &serde_json::Value) -> Vec<u8> {
    let hash = h["hash"].as_str().unwrap();
    let mut bytes = Vec::new();
    for index in 0..h["chunks"].as_u64().unwrap() {
        let key = store.meta.keys.root.pack(&("controller", "shard", shard as u64, "chunk", hash, index));
        bytes.extend_from_slice(&store.meta.get(key).await.unwrap().unwrap());
    }
    assert_eq!(bytes.len(), h["len"].as_u64().unwrap() as usize);
    assert_eq!(hex::encode(sha256(&bytes)), hash);
    bytes
}

async fn advance(d: &Durable, n: usize) {
    for _ in 0..n { d.tick().await.unwrap(); }
}

struct Case {
    store: Store,
    keys: KeyFile,
    cfg: ControllerConfig,
    ctl: Arc<ControlPlane>,
    clock: Durable,
}

fn case(name: &str, policy: GcConfig) -> Case {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment(name)).unwrap(), keys.ring(), Faults::none()).unwrap();
    let cfg = config(store.clone(), &keys);
    let ctl = ControlPlane::new_shard_with_gc(cfg.clone(), 0, 1, policy);
    let clock = Durable::new(store.clone(), cfg.lease);
    Case { store, keys, cfg, ctl, clock }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn terminal_history_obeys_grace_and_preserves_active_and_retained_snapshot() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-grace", enabled(3));
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    assert_eq!(c.ctl.handle(submit("hist/done", "History.Done", 1)).await, ControlResponse::Queued);
    let first = c.ctl.handle(poll(worker, "hist/poll-done")).await;
    assert!(matches!(&first, ControlResponse::Work { request, .. } if request == "hist/done"), "{first:?}");
    assert_eq!(c.ctl.handle(ControlRequest::Finish { worker: worker.hex(), request: "hist/done".into(), ok: true }).await,
        ControlResponse::Ok);
    assert_eq!(c.ctl.handle(submit("hist/active", "History.Active", 1)).await, ControlResponse::Queued);
    for i in 0..12 {
        let request = format!("hist/cancel/{i}");
        assert_eq!(c.ctl.handle(submit(&request, &format!("History.Cancel.t{i}"), 1)).await, ControlResponse::Queued);
        assert_eq!(c.ctl.handle(ControlRequest::Cancel { request, worker: String::new() }).await, ControlResponse::Cancelled);
    }
    let old = head(&c.store, 0).await;
    let old_bytes = snapshot_bytes(&c.store, 0, &old).await;
    c.ctl.retain_snapshot(old["hash"].as_str().unwrap()).await.unwrap();

    let early = c.ctl.compact_history_once().await.unwrap();
    assert_eq!(early.compacted_work, 0, "terminal work retired before grace");
    assert!(c.clock.work_replay("hist/done").await.unwrap().is_none());
    advance(&c.clock, 2).await;
    assert_eq!(c.ctl.compact_history_once().await.unwrap().compacted_work, 0);
    advance(&c.clock, 1).await;
    let settled = c.ctl.compact_history_once().await.unwrap();
    assert!(settled.compacted_work >= 13, "terminal work did not compact: {settled:?}");
    assert!(c.clock.work_replay("hist/done").await.unwrap().is_some());
    assert!(c.clock.poll_replay("hist/poll-done").await.unwrap().is_some());

    let current = head(&c.store, 0).await;
    assert!(current["len"].as_u64().unwrap() < old["len"].as_u64().unwrap(), "current snapshot did not shrink");
    assert_eq!(snapshot_bytes(&c.store, 0, &old).await, old_bytes, "retained snapshot was changed");
    let current_bytes = snapshot_bytes(&c.store, 0, &current).await;
    let current_state: serde_json::Value = serde_json::from_slice(&current_bytes).unwrap();
    assert!(current_state["work"].get("hist/active").is_some(), "active work was pruned");
    assert!(current_state["work"].get("hist/done").is_none(), "terminal work remained in current snapshot");
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn default_disabled_preserves_history_after_logical_grace() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-disabled", GcConfig::default());
    assert_eq!(c.ctl.handle(submit("hist/disabled", "History.Disabled", 1)).await, ControlResponse::Queued);
    assert_eq!(c.ctl.handle(ControlRequest::Cancel { request: "hist/disabled".into(), worker: String::new() }).await, ControlResponse::Cancelled);
    let old = head(&c.store, 0).await;
    let first_tick = c.clock.clock().await.unwrap();
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let monitor = c.ctl.serve(listener);
    tokio::time::timeout(Duration::from_secs(4), async {
        while c.clock.clock().await.unwrap() < first_tick + 16 {
            tokio::time::sleep(Duration::from_millis(20)).await;
        }
    }).await.expect("default monitor did not advance logical grace");
    monitor.abort();
    assert!(c.ctl.compact_history_once().await.is_err(), "disabled GC accepted manual compaction");
    assert!(c.clock.work_replay("hist/disabled").await.unwrap().is_none());
    let current = head(&c.store, 0).await;
    assert_eq!(current["hash"], old["hash"]);
    let state: serde_json::Value = serde_json::from_slice(&snapshot_bytes(&c.store, 0, &current).await).unwrap();
    assert!(state["work"].get("hist/disabled").is_some());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn active_poll_tokens_cannot_starve_terminal_work() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let mut policy = enabled(2);
    policy.scan_limit = 1;
    let c = case("history-fair", policy);
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    for i in 0..2 {
        let request = format!("hist/running/{i}");
        assert_eq!(c.ctl.handle(submit(&request, &format!("History.Running.t{i}"), 1)).await,
            ControlResponse::Queued);
        assert!(matches!(c.ctl.handle(poll(worker, &format!("hist/running-token/{i}"))).await,
            ControlResponse::Work { request: selected, .. } if selected == request));
    }
    assert_eq!(c.ctl.handle(submit("hist/unrelated", "History.Unrelated", 1)).await,
        ControlResponse::Queued);
    assert_eq!(c.ctl.handle(ControlRequest::Cancel { request: "hist/unrelated".into(), worker: String::new() }).await,
        ControlResponse::Cancelled);
    advance(&c.clock, 2).await;
    for _ in 0..10 {
        let _ = c.ctl.compact_history_once().await.unwrap();
        if c.clock.work_replay("hist/unrelated").await.unwrap().is_some() { break; }
    }
    assert!(c.clock.work_replay("hist/unrelated").await.unwrap().is_some(),
        "active poll tokens starved unrelated settled work with scan_limit=1");
    for i in 0..2 {
        assert!(c.clock.work_replay(&format!("hist/running/{i}")).await.unwrap().is_none());
        assert!(c.clock.poll_replay(&format!("hist/running-token/{i}")).await.unwrap().is_none());
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn old_poll_token_waits_for_its_work_to_settle_and_age() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-token-age", enabled(3));
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    assert_eq!(c.ctl.handle(submit("hist/long", "History.Long", 1)).await, ControlResponse::Queued);
    assert!(matches!(c.ctl.handle(poll(worker, "hist/old-token")).await,
        ControlResponse::Work { request, .. } if request == "hist/long"));
    for _ in 0..12 {
        c.clock.tick().await.unwrap();
        assert_eq!(c.ctl.handle(ControlRequest::Heartbeat { worker: worker.hex() }).await,
            ControlResponse::Ok);
    }
    assert_eq!(c.ctl.handle(ControlRequest::Finish { worker: worker.hex(), request: "hist/long".into(), ok: true }).await,
        ControlResponse::Ok);
    let early = c.ctl.compact_history_once().await.unwrap();
    assert_eq!(early.compacted_polls, 0, "work-bound token retired at finish without grace");
    assert!(c.clock.poll_replay("hist/old-token").await.unwrap().is_none());
    advance(&c.clock, 3).await;
    assert!(c.ctl.compact_history_once().await.unwrap().compacted_polls >= 1);
    assert!(c.clock.poll_replay("hist/old-token").await.unwrap().is_some());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn old_poll_token_cannot_claim_new_epoch_on_same_worker() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-poll-epoch", GcConfig::default());
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    assert_eq!(c.ctl.handle(submit("hist/epoch-work", "History.Epoch", 1)).await,
        ControlResponse::Queued);
    let first = c.ctl.handle(poll(worker, "hist/epoch-old-token")).await;
    let first_epoch = match first {
        ControlResponse::Work { request, epoch, .. } if request == "hist/epoch-work" => epoch,
        other => panic!("first assignment missing: {other:?}"),
    };
    advance(&c.clock, 9).await;
    c.ctl.expire_leases().await; // Fence the expired owner to the unowned sentinel.
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    let second = c.ctl.handle(poll(worker, "hist/epoch-new-token")).await;
    let second_epoch = match second {
        ControlResponse::Work { request, epoch, .. } if request == "hist/epoch-work" => epoch,
        other => panic!("same worker did not receive reassigned work: {other:?}"),
    };
    assert!(second_epoch > first_epoch, "reassignment did not advance the target epoch");
    assert_eq!(c.ctl.handle(poll(worker, "hist/epoch-old-token")).await,
        ControlResponse::NoWork,
        "old poll token claimed a newer assignment of the same work and worker");
    assert_eq!(c.ctl.handle(poll(worker, "hist/epoch-new-token")).await,
        ControlResponse::Work { request: "hist/epoch-work".into(), target: "History.Epoch".into(),
            epoch: second_epoch, memory_mb: 1 });
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-replay", enabled(2));
    let (worker, _) = c.keys.workspace("w0").unwrap();
    let (other, _) = c.keys.workspace("w1").unwrap();
    for id in [worker, other] {
        assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: id.hex(), capacity_mb: 128 }).await,
            ControlResponse::Registered { .. }));
    }
    assert_eq!(c.ctl.handle(submit("hist/replay", "History.Replay", 1)).await, ControlResponse::Queued);
    assert!(matches!(c.ctl.handle(poll(worker, "hist/poll-work")).await,
        ControlResponse::Work { request, .. } if request == "hist/replay"));
    assert_eq!(c.ctl.handle(ControlRequest::Finish { worker: worker.hex(), request: "hist/replay".into(), ok: true }).await,
        ControlResponse::Ok);
    assert_eq!(c.ctl.handle(poll(worker, "hist/poll-empty")).await, ControlResponse::NoWork);
    assert_eq!(c.ctl.handle(submit("hist/new", "History.New", 1)).await, ControlResponse::Queued);
    let _ = c.ctl.compact_history_once().await.unwrap();
    advance(&c.clock, 2).await;
    let result = c.ctl.compact_history_once().await.unwrap();
    assert!(result.compacted_work >= 1 && result.compacted_polls >= 2, "{result:?}");
    assert!(c.clock.work_replay("hist/replay").await.unwrap().is_some());
    assert!(c.clock.poll_replay("hist/poll-work").await.unwrap().is_some());
    assert!(c.clock.poll_replay("hist/poll-empty").await.unwrap().is_some());

    // A deployment can turn GC off after records exist. Replay reads remain
    // mandatory on the replacement leader.
    advance(&c.clock, 9).await;
    let replacement = ControlPlane::new_shard_with_gc(c.cfg.clone(), 0, 1, GcConfig::default());
    assert!(matches!(replacement.handle(ControlRequest::Status).await,
        ControlResponse::Status { status } if status["leader"] == true));
    for id in [worker, other] {
        assert!(matches!(replacement.handle(ControlRequest::Register { worker: id.hex(), capacity_mb: 128 }).await,
            ControlResponse::Registered { .. }));
    }
    assert_eq!(replacement.handle(submit("hist/replay", "History.Replay", 1)).await,
        ControlResponse::Duplicate { state: "Done".into() });
    assert!(is_refused(replacement.handle(submit("hist/replay", "History.Other", 1)).await));
    assert!(is_refused(replacement.handle(submit("hist/replay", "History.Replay", 2)).await));
    assert_eq!(replacement.handle(poll(worker, "hist/poll-work")).await, ControlResponse::NoWork);
    assert_eq!(replacement.handle(poll(worker, "hist/poll-empty")).await, ControlResponse::NoWork);
    assert!(is_refused(replacement.handle(poll(other, "hist/poll-work")).await));
    let ControlResponse::Status { status } = replacement.handle(ControlRequest::Status).await else { panic!("no status") };
    assert!(status["work"].as_array().unwrap().iter().any(|j| j["request"] == "hist/new" && j["state"] == "Queued"));
    let work = replacement.handle(poll(worker, "hist/poll-new")).await;
    assert!(matches!(&work, ControlResponse::Work { request, .. } if request == "hist/new"), "{work:?}");
    assert_eq!(replacement.handle(poll(worker, "hist/poll-new")).await, work);

    // J3 cancellation is an authoritative overlay on an immutable Done replay.
    assert_eq!(replacement.handle(ControlRequest::Cancel { request: "hist/replay".into(), worker: String::new() }).await,
        ControlResponse::Cancelled);
    assert_eq!(replacement.handle(submit("hist/replay", "History.Replay", 1)).await,
        ControlResponse::Duplicate { state: "Cancelled".into() });
    assert!(is_refused(replacement.handle(submit("hist/replay", "History.Other", 1)).await));
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn compacted_work_keeps_its_cross_shard_route() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment("history-route")).unwrap(), keys.ring(), Faults::none()).unwrap();
    let cfg = config(store.clone(), &keys);
    let ctl = ControlPlane::new_shard_with_gc(cfg.clone(), 0, 2, enabled(2));
    let clock = Durable::new_shard(store.clone(), cfg.lease, 0, 2);
    let target = (0..100).map(|n| Name::parse(&format!("History.Route.t{n}")))
        .find(|name| Durable::hash_shard(name, 2) == 0).unwrap();
    let request = "hist/route";
    assert_eq!(ctl.handle(submit(request, &target.to_string(), 1)).await, ControlResponse::Queued);
    assert_eq!(ctl.handle(ControlRequest::Cancel { request: request.into(), worker: String::new() }).await, ControlResponse::Cancelled);
    let _ = ctl.compact_history_once().await.unwrap();
    advance(&clock, 2).await;
    assert!(ctl.compact_history_once().await.unwrap().compacted_work >= 1);
    assert_eq!(clock.shard_for_target(&target).await.unwrap(), 0);
    assert!(clock.work_replay(request).await.unwrap().is_some());

    advance(&clock, 9).await;
    let replacement = ControlPlane::new_shard_with_gc(cfg.clone(), 0, 2, GcConfig::default());
    let wrong = ControlPlane::new_shard_with_gc(cfg, 1, 2, GcConfig::default());
    assert_eq!(replacement.handle(submit(request, &target.to_string(), 1)).await,
        ControlResponse::Duplicate { state: "Cancelled".into() });
    assert!(matches!(wrong.handle(submit(request, &target.to_string(), 1)).await,
        ControlResponse::Inconclusive { reason } if reason.contains("not controller shard")));
    assert_eq!(clock.shard_for_target(&target).await.unwrap(), 0);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn stale_history_compactor_cannot_prune() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-stale", enabled(2));
    let stale = Durable::new(c.store.clone(), c.cfg.lease);
    let term = stale.acquire_or_renew().await.unwrap().unwrap().term;
    stale.save(b"old-head", term).await.unwrap();
    advance(&stale, 9).await;
    let successor = Durable::new(c.store.clone(), c.cfg.lease);
    assert!(successor.acquire_or_renew().await.unwrap().unwrap().term > term);
    let before = successor.current_snapshot_hash().await.unwrap();
    let row = WorkReplay {
        request: "hist/stale".into(), target: "History.Stale".into(),
        memory_mb: 1, state: TerminalState::Done,
    };
    let result = stale.save_with_history(b"illicit-pruned-head", term, &[row], &[]).await;
    assert!(result.is_err(), "stale leader published a pruned head and replay marker");
    assert_eq!(successor.current_snapshot_hash().await.unwrap(), before);
    assert!(successor.work_replay("hist/stale").await.unwrap().is_none());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn history_batch_commit_survives_crash_before_memory_update() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-atomic", enabled(2));
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    for i in 0..2 {
        let request = format!("hist/batch/{i}");
        let token = format!("hist/batch-poll/{i}");
        assert_eq!(c.ctl.handle(submit(&request, &format!("History.Batch.t{i}"), 1)).await, ControlResponse::Queued);
        assert!(matches!(c.ctl.handle(poll(worker, &token)).await,
            ControlResponse::Work { request: selected, .. } if selected == request));
        assert_eq!(c.ctl.handle(ControlRequest::Finish { worker: worker.hex(), request, ok: true }).await,
            ControlResponse::Ok);
    }
    let _ = c.ctl.compact_history_once().await.unwrap(); // Stamp legacy/missing times.
    advance(&c.clock, 2).await;
    std::env::set_var("PARALEAN_TEST_PAUSE_AFTER_HISTORY_COMMIT_MS", "1500");
    let ctl = c.ctl.clone();
    let mut task = tokio::spawn(async move { ctl.compact_history_once().await });
    let committed = tokio::time::timeout(Duration::from_secs(5), async {
        loop {
            if c.clock.work_replay("hist/batch/0").await.unwrap().is_some() { break; }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }).await;
    std::env::remove_var("PARALEAN_TEST_PAUSE_AFTER_HISTORY_COMMIT_MS");
    assert!(committed.is_ok(), "two-ID history batch never committed");
    assert!(!task.is_finished(), "compactor returned before the post-commit crash window");
    for i in 0..2 {
        assert!(c.clock.work_replay(&format!("hist/batch/{i}")).await.unwrap().is_some(),
            "work marker {i} absent after batch commit");
        assert!(c.clock.poll_replay(&format!("hist/batch-poll/{i}")).await.unwrap().is_some(),
            "poll marker {i} absent after batch commit");
    }
    let current = head(&c.store, 0).await;
    let state: serde_json::Value = serde_json::from_slice(&snapshot_bytes(&c.store, 0, &current).await).unwrap();
    for i in 0..2 {
        assert!(state["work"].get(format!("hist/batch/{i}")).is_none(),
            "pruned head retained work {i}");
    }
    task.abort(); // Commit succeeded, caller never learned its outcome.
    let _ = (&mut task).await;
    advance(&c.clock, 9).await;
    let replacement = ControlPlane::new_shard_with_gc(c.cfg.clone(), 0, 1, GcConfig::default());
    assert!(matches!(replacement.handle(ControlRequest::Status).await,
        ControlResponse::Status { status } if status["leader"] == true));
    assert!(matches!(replacement.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    for i in 0..2 {
        let request = format!("hist/batch/{i}");
        assert_eq!(replacement.handle(submit(&request, &format!("History.Batch.t{i}"), 1)).await,
            ControlResponse::Duplicate { state: "Done".into() });
        assert_eq!(replacement.handle(poll(worker, &format!("hist/batch-poll/{i}"))).await,
            ControlResponse::NoWork);
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn history_replay_rows_reject_conflicting_rewrites() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-immutable", enabled(2));
    let durable = Durable::new(c.store.clone(), c.cfg.lease);
    let term = durable.acquire_or_renew().await.unwrap().unwrap().term;
    let work = WorkReplay {
        request: "hist/immutable".into(), target: "History.Immutable".into(),
        memory_mb: 1, state: TerminalState::Done,
    };
    let poll = PollReplay {
        token: "hist/immutable-token".into(), worker: "worker-a".into(),
        work: Some(work.request.clone()), epoch: Some(7),
    };
    durable.save_with_history(b"first-head", term, &[work.clone()], &[poll.clone()]).await.unwrap();
    let original_head = durable.current_snapshot_hash().await.unwrap();
    let mut changed_work = work.clone();
    changed_work.memory_mb = 2;
    assert!(durable.save_with_history(b"conflicting-work-head", term, &[changed_work], &[]).await.is_err(),
        "same request accepted changed work descriptor");
    assert_eq!(durable.work_replay(&work.request).await.unwrap(), Some(work));
    assert_eq!(durable.current_snapshot_hash().await.unwrap(), original_head);
    let mut changed_poll = poll.clone();
    changed_poll.worker = "worker-b".into();
    assert!(durable.save_with_history(b"conflicting-poll-head", term, &[], &[changed_poll]).await.is_err(),
        "same token accepted changed worker binding");
    assert_eq!(durable.poll_replay(&poll.token).await.unwrap(), Some(poll));
    assert_eq!(durable.current_snapshot_hash().await.unwrap(), original_head);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn oversized_poll_token_does_not_block_small_history_replay() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-large-row", enabled(2));
    let (worker, _) = c.keys.workspace("w0").unwrap();
    assert!(matches!(c.ctl.handle(ControlRequest::Register { worker: worker.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    let huge_token = format!("hist/huge/{}", "x".repeat(92 * 1024));
    assert_eq!(c.ctl.handle(poll(worker, &huge_token)).await, ControlResponse::NoWork);
    assert_eq!(c.ctl.handle(submit("hist/small", "History.Small", 1)).await, ControlResponse::Queued);
    assert_eq!(c.ctl.handle(ControlRequest::Cancel { request: "hist/small".into(), worker: String::new() }).await,
        ControlResponse::Cancelled);
    advance(&c.clock, 2).await;
    for _ in 0..4 {
        let _ = c.ctl.compact_history_once().await.unwrap();
        if c.clock.work_replay("hist/small").await.unwrap().is_some() { break; }
    }
    assert!(c.clock.work_replay("hist/small").await.unwrap().is_some(),
        "oversized poll marker blocked independent small work replay");
    assert!(c.clock.poll_replay(&huge_token).await.unwrap().is_none());
    let current = head(&c.store, 0).await;
    let state: serde_json::Value = serde_json::from_slice(&snapshot_bytes(&c.store, 0, &current).await).unwrap();
    assert!(state["poll_responses"].get(&huge_token).is_some(), "oversized token was lost");
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn durable_history_write_limits_leave_head_and_markers_unchanged() {
    let _serial = HISTORY_TEST_LOCK.lock().await;
    let c = case("history-limits", enabled(2));
    let durable = Durable::new(c.store.clone(), c.cfg.lease);
    let term = durable.acquire_or_renew().await.unwrap().unwrap().term;
    let large = WorkReplay {
        request: "hist/too-large".into(), target: "x".repeat(91 * 1024),
        memory_mb: 1, state: TerminalState::Done,
    };
    let small = WorkReplay {
        request: "hist/small-before-large".into(), target: "History.Small".into(),
        memory_mb: 1, state: TerminalState::Done,
    };
    assert!(durable.save_with_history(b"bad-large-head", term, &[small, large], &[]).await.is_err());
    assert!(durable.current_snapshot_hash().await.unwrap().is_none());
    assert!(durable.work_replay("hist/small-before-large").await.unwrap().is_none());
    assert!(durable.work_replay("hist/too-large").await.unwrap().is_none());

    let rows: Vec<WorkReplay> = (0..4).map(|i| WorkReplay {
        request: format!("hist/budget/{i}"), target: "y".repeat(70 * 1024),
        memory_mb: 1, state: TerminalState::Done,
    }).collect();
    assert!(durable.save_with_history(b"bad-budget-head", term, &rows, &[]).await.is_err());
    assert!(durable.current_snapshot_hash().await.unwrap().is_none());
    for row in &rows { assert!(durable.work_replay(&row.request).await.unwrap().is_none()); }
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("terminal_history_obeys_grace_and_preserves_active_and_retained_snapshot", || { terminal_history_obeys_grace_and_preserves_active_and_retained_snapshot(); Ok(()) }),
        libtest_mimic::Trial::test("default_disabled_preserves_history_after_logical_grace", || { default_disabled_preserves_history_after_logical_grace(); Ok(()) }),
        libtest_mimic::Trial::test("active_poll_tokens_cannot_starve_terminal_work", || { active_poll_tokens_cannot_starve_terminal_work(); Ok(()) }),
        libtest_mimic::Trial::test("old_poll_token_waits_for_its_work_to_settle_and_age", || { old_poll_token_waits_for_its_work_to_settle_and_age(); Ok(()) }),
        libtest_mimic::Trial::test("old_poll_token_cannot_claim_new_epoch_on_same_worker", || { old_poll_token_cannot_claim_new_epoch_on_same_worker(); Ok(()) }),
        libtest_mimic::Trial::test("replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work", || { replay_survives_restart_with_gc_disabled_and_poll_tokens_do_not_steal_work(); Ok(()) }),
        libtest_mimic::Trial::test("compacted_work_keeps_its_cross_shard_route", || { compacted_work_keeps_its_cross_shard_route(); Ok(()) }),
        libtest_mimic::Trial::test("stale_history_compactor_cannot_prune", || { stale_history_compactor_cannot_prune(); Ok(()) }),
        libtest_mimic::Trial::test("history_batch_commit_survives_crash_before_memory_update", || { history_batch_commit_survives_crash_before_memory_update(); Ok(()) }),
        libtest_mimic::Trial::test("history_replay_rows_reject_conflicting_rewrites", || { history_replay_rows_reject_conflicting_rewrites(); Ok(()) }),
        libtest_mimic::Trial::test("oversized_poll_token_does_not_block_small_history_replay", || { oversized_poll_token_does_not_block_small_history_replay(); Ok(()) }),
        libtest_mimic::Trial::test("durable_history_write_limits_leave_head_and_markers_unchanged", || { durable_history_write_limits_leave_head_and_markers_unchanged(); Ok(()) }),
    ]);
}
