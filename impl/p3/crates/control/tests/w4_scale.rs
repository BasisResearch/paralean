//! Live FDB scale measurements; no Lean checker or shared fixture cache is used.
mod common;

use std::time::{Duration, Instant};
use common::deployment;
use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::durable::Durable;
use paralean_control::gc::GcConfig;
use paralean_store::*;

fn config(store: Store, keys: &KeyFile) -> ControllerConfig {
    ControllerConfig {
        store, authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_secs(2),
        max_work_queue: 4096, max_validations: 4,
        validation_deadline: Duration::from_secs(2), validation_memory_mb: 128,
        validator_attempts: 1,
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
#[ignore = "live isolated W4 benchmark"]
async fn controller_throughput_failover_and_gc() {
    let keys = KeyFile::demo(2);
    let total = std::env::var("W4_SCALE_JOBS").ok().map(|s| s.parse::<usize>().unwrap()).unwrap_or(512);
    let mut rows = vec![];
    for shards in [1u32, 2, 4] {
        let dep = deployment(&format!("w4-scale-{shards}"));
        let store = Store::open(&StoreConfig::from_env(&dep).unwrap(), keys.ring(), Faults::none()).unwrap();
        let cfg = config(store.clone(), &keys);
        let controllers: Vec<_> = (0..shards).map(|s| ControlPlane::new_shard(cfg.clone(), s, shards)).collect();
        let route = Durable::new_shard(store.clone(), cfg.lease, 0, shards);
        let mut inputs = vec![vec![]; shards as usize];
        for n in 0..total {
            let target = format!("W4.scale.t{n}");
            let shard = route.shard_for_target(&Name::parse(&target)).await.unwrap();
            inputs[shard as usize].push((format!("work/{n}"), target));
        }
        let counts: Vec<_> = inputs.iter().map(Vec::len).collect();
        let start = Instant::now();
        let mut tasks = vec![];
        for (ctl, input) in controllers.iter().cloned().zip(inputs) {
            tasks.push(tokio::spawn(async move {
                for (request, target) in input {
                    let result = ctl.handle(ControlRequest::SubmitWork { request, target, memory_mb: 1 }).await;
                    assert_eq!(result, ControlResponse::Queued);
                }
            }));
        }
        for t in tasks { t.await.unwrap(); }
        let seconds = start.elapsed().as_secs_f64();
        let mut recovered = 0;
        let failover = Instant::now();
        for s in 0..shards {
            // A paused holder performs no renewal. Only committed counter advances
            // cause expiry; wall time is used solely to report this measurement.
            let clock = Durable::new_shard(store.clone(), cfg.lease, s, shards);
            for _ in 0..8 { clock.tick().await.unwrap(); }
            let standby = ControlPlane::new_shard(cfg.clone(), s, shards);
            let ControlResponse::Status { status } = standby.handle(ControlRequest::Status).await else {
                panic!("standby failed to recover shard {s}")
            };
            assert_eq!(status["leader"], true);
            let jobs = status["work"].as_array().unwrap().len();
            assert_eq!(jobs, counts[s as usize]);
            recovered += jobs;
            let ControlResponse::Status { status } = controllers[s as usize].handle(ControlRequest::Status).await else {
                panic!("old leader status")
            };
            assert_eq!(status["leader"], false);
        }
        assert_eq!(recovered, total);
        rows.push(serde_json::json!({
            "shards": shards, "jobs": total, "jobs_per_shard": counts,
            "submit_seconds": seconds, "jobs_per_second": total as f64 / seconds,
            "failover_and_recovery_seconds": failover.elapsed().as_secs_f64(),
            "recovered_jobs": recovered,
            "failover_trigger": "8 committed logical ticks per shard; holders paused",
        }));
    }

    let store = Store::open(&StoreConfig::from_env(&deployment("w4-scale-gc")).unwrap(), keys.ring(), Faults::none()).unwrap();
    let start = Instant::now();
    let mut reclaimed = 0;
    let mut deleted = 0;
    let snapshot_bytes = 3 * 1024 * 1024;
    for shard in 0..4u32 {
        let durable = Durable::new_shard(store.clone(), Duration::from_secs(2), shard, 4);
        let term = durable.acquire_or_renew().await.unwrap().unwrap().term;
        for generation in 0..4u8 {
            durable.save(&vec![generation + shard as u8 * 4; snapshot_bytes], term).await.unwrap();
        }
        durable.tick().await.unwrap();
        durable.tick().await.unwrap();
        let report = durable.collect_retired_snapshots(term,
            &GcConfig { enabled: true, grace_ticks: 2, scan_limit: 128 }, None).await.unwrap();
        assert_eq!(report.deleted_snapshots, 3);
        assert_eq!(report.reclaimed_bytes, snapshot_bytes * 3);
        reclaimed += report.reclaimed_bytes;
        deleted += report.deleted_snapshots;
        let fresh = Durable::new_shard(store.clone(), Duration::from_secs(2), shard, 4);
        assert_eq!(fresh.load().await.unwrap().unwrap(), vec![3 + shard as u8 * 4; snapshot_bytes]);
    }
    let gc_seconds = start.elapsed().as_secs_f64();
    // History compaction retains durable retry markers but removes terminal
    // payloads from the current shard snapshot. Drive only store-ordered ticks.
    let history_store = Store::open(&StoreConfig::from_env(&deployment("w4-scale-history")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let history_cfg = config(history_store.clone(), &keys);
    let history_ctl = ControlPlane::new_shard_with_gc(history_cfg.clone(), 0, 1,
        GcConfig { enabled: true, grace_ticks: 2, scan_limit: 128 });
    let history_reader = Durable::new_shard(history_store, history_cfg.lease, 0, 1);
    let history_jobs = 256usize;
    let history_polls = 128usize;
    let worker = keys.workspace("w0").unwrap().0.hex();
    assert!(matches!(history_ctl.handle(ControlRequest::Register {
        worker: worker.clone(), capacity_mb: 1,
    }).await, ControlResponse::Registered { .. }));
    for n in 0..history_jobs {
        let request = format!("history/work/{n}");
        assert_eq!(history_ctl.handle(ControlRequest::SubmitWork {
            request: request.clone(), target: format!("W4.history.t{n}"), memory_mb: 1,
        }).await, ControlResponse::Queued);
        assert_eq!(history_ctl.handle(ControlRequest::Cancel { request }).await, ControlResponse::Cancelled);
    }
    for n in 0..history_polls {
        assert_eq!(history_ctl.handle(ControlRequest::PollRequest {
            worker: worker.clone(), request: format!("history/poll/{n}"),
        }).await, ControlResponse::NoWork);
    }
    let history_before = history_reader.load().await.unwrap().unwrap().len();
    let history_start = Instant::now();
    let mut compacted = (0, 0);
    for _ in 0..16 {
        history_ctl.expire_leases().await;
        let ControlResponse::Status { status } = history_ctl.handle(ControlRequest::Status).await else {
            panic!("history controller status")
        };
        compacted = (status["history_compacted_work"].as_u64().unwrap_or(0),
            status["history_compacted_polls"].as_u64().unwrap_or(0));
        if compacted == (history_jobs as u64, history_polls as u64) { break }
        history_reader.tick().await.unwrap();
    }
    assert_eq!(compacted, (history_jobs as u64, history_polls as u64));
    let history_after = history_reader.load().await.unwrap().unwrap().len();
    assert!(history_after < history_before / 2, "{history_before} -> {history_after}");
    let history_seconds = history_start.elapsed().as_secs_f64();
    for _ in 0..8 { history_reader.tick().await.unwrap(); }
    // Turning GC off must not turn retry protection off.
    let recovered_history = ControlPlane::new_shard(history_cfg, 0, 1);
    assert_eq!(recovered_history.handle(ControlRequest::SubmitWork {
        request: "history/work/0".into(), target: "W4.history.t0".into(), memory_mb: 1,
    }).await, ControlResponse::Duplicate { state: "Cancelled".into() });
    assert!(matches!(recovered_history.handle(ControlRequest::Register {
        worker: worker.clone(), capacity_mb: 1,
    }).await, ControlResponse::Registered { .. }));
    assert_eq!(recovered_history.handle(ControlRequest::SubmitWork {
        request: "history/fresh".into(), target: "W4.history.fresh".into(), memory_mb: 1,
    }).await, ControlResponse::Queued);
    assert_eq!(recovered_history.handle(ControlRequest::PollRequest {
        worker, request: "history/poll/0".into(),
    }).await, ControlResponse::NoWork);

    let report = serde_json::json!({
        "method": "one shared-host sample; live private FDB; direct controller API; no validation RPC",
        "controller": rows,
        "gc": { "shards": 4, "current_snapshot_bytes_total": snapshot_bytes * 4,
            "deleted_snapshots": deleted, "reclaimed_bytes": reclaimed,
            "write_collect_recover_seconds": gc_seconds,
            "fresh_reader_recovery_verified": true },
        "history": { "compacted_work": history_jobs, "compacted_polls": history_polls,
            "snapshot_bytes_before": history_before, "snapshot_bytes_after": history_after,
            "compact_seconds": history_seconds,
            "replay_after_restart_with_gc_disabled_verified": true,
            "replay_records_retained": true }
    });
    if let Ok(path) = std::env::var("W4_SCALE_REPORT") {
        std::fs::write(path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
    }
    println!("{report}");
}
