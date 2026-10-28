//! An unresponsive endpoint must not delay heartbeats to live shards.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;

use std::time::Duration;

use common::deployment;
use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::worker::WorkerNode;
use paralean_store::*;

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn unresponsive_endpoint_does_not_starve_live_shard_heartbeats() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("w4-worker-heartbeat")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let cfg = ControllerConfig {
        store: store.clone(), authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 16, max_validations: 1, validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    };
    let controllers: Vec<_> = (0..2).map(|shard| ControlPlane::new_shard(cfg.clone(), shard, 2)).collect();
    let live_a = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr_a = live_a.local_addr().unwrap();
    let live_b = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr_b = live_b.local_addr().unwrap();
    let services = [controllers[0].serve(live_a), controllers[1].serve(live_b)];
    let blackhole = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let dead_addr = blackhole.local_addr().unwrap();
    let path = std::env::temp_dir().join(deployment("w4-empty-p1"));
    std::fs::create_dir_all(path.join("meta")).unwrap();
    let (id, signer) = keys.workspace("w0").unwrap();
    let worker = WorkerNode::new(Writer::new(store, id, signer),
        &format!("{dead_addr},{addr_a},{addr_b}"), 1024, &path).unwrap();
    assert!(matches!(worker.register().await.unwrap(), ControlResponse::Registered { .. }));
    let heartbeats = worker.spawn_heartbeats(Duration::from_millis(50));
    tokio::time::sleep(Duration::from_millis(1600)).await;
    for controller in controllers {
        let ControlResponse::Status { status } = controller.handle(ControlRequest::Status).await else { panic!("no leader status") };
        let workers = status["workers"].as_array().unwrap();
        assert_eq!(workers.len(), 1);
        assert_eq!(workers[0]["alive"], true);
    }
    heartbeats.abort();
    for service in services { service.abort(); }
    drop(blackhole);
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("unresponsive_endpoint_does_not_starve_live_shard_heartbeats", || { unresponsive_endpoint_does_not_starve_live_shard_heartbeats(); Ok(()) }),
    ]);
}
