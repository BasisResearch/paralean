//! Live FoundationDB tests for opt-in controller snapshot collection.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::time::Duration;

use common::deployment;
use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::durable::Durable;
use paralean_control::gc::GcConfig;
use paralean_store::id::sha256;
use paralean_store::*;

fn controller_config(store: Store, keys: &KeyFile) -> ControllerConfig {
    ControllerConfig {
        store,
        authority: keys.authority_signer().unwrap(),
        validators: vec![],
        base: fixture::base_id(),
        policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(),
        lease: Duration::from_millis(500),
        max_work_queue: 8,
        max_validations: 1,
        validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128,
        validator_attempts: 1,
    }
}

async fn controller_head_hash(store: &Store) -> String {
    let state_key = store.meta.keys.root.pack(&("controller", "shard", 0u64, "state"));
    let head: serde_json::Value = serde_json::from_slice(&store.meta.get(state_key).await.unwrap().unwrap()).unwrap();
    head["hash"].as_str().unwrap().to_string()
}

struct MonitorCase {
    store: Store,
    ctl: std::sync::Arc<ControlPlane>,
    durable: Durable,
    task: tokio::task::JoinHandle<()>,
    old_hash: String,
    current_hash: String,
}

async fn monitor_case(label: &str, gc: GcConfig) -> MonitorCase {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment(label)).unwrap(), keys.ring(), Faults::none()).unwrap();
    let cfg = controller_config(store.clone(), &keys);
    let durable = Durable::new(store.clone(), cfg.lease);
    let ctl = ControlPlane::new_shard_with_gc(cfg, 0, 1, gc);
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let task = ctl.serve(listener);
    let mut old_hash = None;
    for i in 0..2 {
        assert_eq!(ctl.handle(ControlRequest::SubmitWork {
            request: format!("gc-monitor/{label}/{i}"),
            target: format!("GC.Monitor.{label}.t{i}"), memory_mb: 1,
        }).await, ControlResponse::Queued);
        if i == 0 {
            let hash = controller_head_hash(&store).await;
            assert!(store.meta.get(chunks(&store, &hash)).await.unwrap().is_some());
            old_hash = Some(hash);
        }
    }
    let old_hash = old_hash.unwrap();
    let current_hash = controller_head_hash(&store).await;
    assert_ne!(old_hash, current_hash);
    assert!(store.meta.get(chunks(&store, &old_hash)).await.unwrap().is_some(), "old chunk collected before grace");
    MonitorCase { store, ctl, durable, task, old_hash, current_hash }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn controller_monitor_collects_only_when_enabled_and_preserves_queued_work() {
    let enabled = monitor_case("enabled", GcConfig {
        enabled: true, grace_ticks: 16, scan_limit: 128,
    }).await;
    let disabled = monitor_case("disabled", GcConfig::default()).await;

    let start = std::time::Instant::now();
    loop {
        if enabled.store.meta.get(chunks(&enabled.store, &enabled.old_hash)).await.unwrap().is_none() {
            break;
        }
        assert!(start.elapsed() < Duration::from_secs(5), "enabled monitor did not reclaim a retired chunk");
        tokio::time::sleep(Duration::from_millis(40)).await;
    }
    let retired_key = enabled.store.meta.keys.root.pack(&(
        "controller", "shard", 0u64, "retired", enabled.old_hash.as_str(),
    ));
    assert!(enabled.store.meta.get(retired_key).await.unwrap().is_none(), "retirement marker was not collected");

    // The disabled monitor also advances its logical clock, far past the same
    // grace, yet its superseded chunk remains.
    let wait = std::time::Instant::now();
    while disabled.durable.clock().await.unwrap() < 24 {
        assert!(wait.elapsed() < Duration::from_secs(5), "disabled monitor stopped ticking");
        tokio::time::sleep(Duration::from_millis(40)).await;
    }
    assert!(disabled.store.meta.get(chunks(&disabled.store, &disabled.old_hash)).await.unwrap().is_some());

    for case in [&enabled, &disabled] {
        assert_eq!(controller_head_hash(&case.store).await, case.current_hash);
        let bytes = case.durable.load().await.unwrap().unwrap();
        assert_eq!(hex::encode(sha256(&bytes)), case.current_hash);
        let ControlResponse::Status { status } = case.ctl.handle(ControlRequest::Status).await else { panic!("status failed") };
        let work = status["work"].as_array().unwrap();
        assert_eq!(work.len(), 2, "queued work was lost");
        assert!(work.iter().all(|job| job["state"] == "Queued"));
    }
    enabled.task.abort();
    disabled.task.abort();
}

fn chunks(store: &Store, hash: &str) -> Vec<u8> {
    store
        .meta
        .keys
        .root
        .pack(&("controller", "shard", 0u64, "chunk", hash, 0u64))
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn gc_requires_opt_in_grace_and_unpinned_superseded_root() {
    let cfg = StoreConfig::from_env(&deployment("gc-roots")).unwrap();
    let store = Store::open(&cfg, KeyFile::demo(2).ring(), Faults::none()).unwrap();
    let d = Durable::new(store.clone(), Duration::from_millis(500));
    let term = d.acquire_or_renew().await.unwrap().unwrap().term;
    let old = vec![42u8; 130_000];
    let old_hash = hex::encode(sha256(&old));
    d.save(&old, term).await.unwrap();
    d.save(b"new state", term).await.unwrap();
    let mut policy = GcConfig::default();
    assert!(d
        .collect_retired_snapshots(term, &policy, None)
        .await
        .is_err());
    policy.enabled = true;
    assert_eq!(
        d.collect_retired_snapshots(term, &policy, None)
            .await
            .unwrap()
            .deleted_snapshots,
        0
    );
    d.retain_snapshot(&old_hash, term).await.unwrap();
    d.tick().await.unwrap();
    d.tick().await.unwrap();
    assert_eq!(
        d.collect_retired_snapshots(term, &policy, None)
            .await
            .unwrap()
            .deleted_snapshots,
        0
    );
    assert!(store
        .meta
        .get(chunks(&store, &old_hash))
        .await
        .unwrap()
        .is_some());
    d.release_snapshot(&old_hash, term).await.unwrap();
    let reclaimed = d
        .collect_retired_snapshots(term, &policy, None)
        .await
        .unwrap();
    assert_eq!(reclaimed.deleted_snapshots, 1);
    assert_eq!(reclaimed.deleted_chunks, 3);
    assert_eq!(reclaimed.reclaimed_bytes, old.len());
    assert!(store
        .meta
        .get(chunks(&store, &old_hash))
        .await
        .unwrap()
        .is_none());
    assert_eq!(d.load().await.unwrap(), Some(b"new state".to_vec()));
    assert!(d.retain_snapshot(&old_hash, term).await.is_err());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn gc_rechecks_current_head_and_rejects_stale_leader() {
    let cfg = StoreConfig::from_env(&deployment("gc-head")).unwrap();
    let store = Store::open(&cfg, KeyFile::demo(2).ring(), Faults::none()).unwrap();
    let d = Durable::new(store.clone(), Duration::from_millis(500));
    let term = d.acquire_or_renew().await.unwrap().unwrap().term;
    let a = b"A snapshot";
    let a_hash = hex::encode(sha256(a));
    d.save(a, term).await.unwrap();
    d.save(b"B snapshot", term).await.unwrap();
    d.save(a, term).await.unwrap();
    d.tick().await.unwrap();
    d.tick().await.unwrap();
    let policy = GcConfig {
        enabled: true,
        ..GcConfig::default()
    };
    let result = d
        .collect_retired_snapshots(term, &policy, None)
        .await
        .unwrap();
    assert_eq!(result.deleted_snapshots, 1); // B only
    assert!(store
        .meta
        .get(chunks(&store, &a_hash))
        .await
        .unwrap()
        .is_some());
    assert_eq!(d.load().await.unwrap(), Some(a.to_vec()));

    // A lease transition makes a former leader unable to collect even after grace.
    for _ in 0..8 {
        d.tick().await.unwrap();
    }
    let replacement = Durable::new(store, Duration::from_millis(500));
    assert!(replacement.acquire_or_renew().await.unwrap().is_some());
    assert!(d
        .collect_retired_snapshots(term, &policy, None)
        .await
        .is_err());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn load_during_collection_and_new_incarnation_of_same_hash() {
    let cfg = StoreConfig::from_env(&deployment("gc-load-race")).unwrap();
    let store = Store::open(&cfg, KeyFile::demo(2).ring(), Faults::none()).unwrap();
    let d = std::sync::Arc::new(Durable::new(store.clone(), Duration::from_millis(500)));
    let term = d.acquire_or_renew().await.unwrap().unwrap().term;
    let old = vec![17u8; 180_123];
    let old_hash = hex::encode(sha256(&old));
    let new = vec![29u8; 180_123];
    d.save(&old, term).await.unwrap();
    let reader = {
        let d = d.clone();
        let old = old.clone();
        let new = new.clone();
        tokio::spawn(async move {
            for _ in 0..80 {
                let loaded = d.load().await.unwrap().unwrap();
                assert!(loaded == old || loaded == new);
                tokio::task::yield_now().await;
            }
        })
    };
    d.save(&new, term).await.unwrap();
    d.tick().await.unwrap();
    d.tick().await.unwrap();
    let policy = GcConfig {
        enabled: true,
        ..GcConfig::default()
    };
    assert_eq!(
        d.collect_retired_snapshots(term, &policy, None)
            .await
            .unwrap()
            .deleted_snapshots,
        1
    );
    reader.await.unwrap();
    assert!(store
        .meta
        .get(chunks(&store, &old_hash))
        .await
        .unwrap()
        .is_none());

    // A later save may use identical bytes, but its head generation is new and
    // the save transaction re-creates all chunks before publishing that head.
    d.save(&old, term).await.unwrap();
    assert!(store
        .meta
        .get(chunks(&store, &old_hash))
        .await
        .unwrap()
        .is_some());
    assert_eq!(d.load().await.unwrap(), Some(old));
    let state_key = store
        .meta
        .keys
        .root
        .pack(&("controller", "shard", 0u64, "state"));
    let head: serde_json::Value =
        serde_json::from_slice(&store.meta.get(state_key).await.unwrap().unwrap()).unwrap();
    assert_eq!(head["generation"], 3);
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("controller_monitor_collects_only_when_enabled_and_preserves_queued_work", || { controller_monitor_collects_only_when_enabled_and_preserves_queued_work(); Ok(()) }),
        libtest_mimic::Trial::test("gc_requires_opt_in_grace_and_unpinned_superseded_root", || { gc_requires_opt_in_grace_and_unpinned_superseded_root(); Ok(()) }),
        libtest_mimic::Trial::test("gc_rechecks_current_head_and_rejects_stale_leader", || { gc_rechecks_current_head_and_rejects_stale_leader(); Ok(()) }),
        libtest_mimic::Trial::test("load_during_collection_and_new_incarnation_of_same_hash", || { load_during_collection_and_new_incarnation_of_same_hash(); Ok(()) }),
    ]);
}
