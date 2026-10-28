//! FoundationDB controller lease and snapshot invariants, using a fresh deployment.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::time::Duration;

use common::deployment;
use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::durable::Durable;
use paralean_store::*;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn elapsed_wall_time_alone_cannot_expire_a_lease() {
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-no-wall-expiry")).unwrap(),
        KeyFile::demo(1).ring(), Faults::none()).unwrap();
    let holder = Durable::new(store.clone(), Duration::from_millis(500));
    let standby = Durable::new(store, Duration::from_millis(500));
    let term = holder.acquire_or_renew().await.unwrap().unwrap().term;
    let before = holder.clock().await.unwrap();
    tokio::time::sleep(Duration::from_millis(650)).await;
    assert_eq!(holder.clock().await.unwrap(), before);
    assert!(standby.acquire_or_renew().await.unwrap().is_none());
    holder.save(b"still current after wall-clock pause", term).await.unwrap();
    for _ in 0..8 { standby.tick().await.unwrap(); }
    assert!(standby.acquire_or_renew().await.unwrap().unwrap().term > term);
    assert!(holder.save(b"stale after store-ordered expiry", term).await.is_err());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn large_snapshot_roundtrips_and_old_leader_writes_are_fenced() {
    let cfg = StoreConfig::from_env(&deployment("durable-chunks")).unwrap();
    let keys = KeyFile::demo(2);
    let store = Store::open(&cfg, keys.ring(), Faults::none()).unwrap();
    let old = Durable::new(store.clone(), Duration::from_millis(500));
    let next = Durable::new(store.clone(), Duration::from_millis(500));
    let first = old.acquire_or_renew().await.unwrap().unwrap();
    assert!(next.acquire_or_renew().await.unwrap().is_none());

    // Three 60 KiB chunks, plus a tail: FDB cannot store this as one value.
    let bytes = (0..180_123usize).map(|i| ((i * 131 + i / 977) % 251) as u8).collect::<Vec<_>>();
    old.save(&bytes, first.term).await.unwrap();
    assert_eq!(old.load().await.unwrap(), Some(bytes.clone()));
    assert_eq!(next.load().await.unwrap(), Some(bytes));

    // Store ticks, rather than either process's wall clock, decide expiry.
    for _ in 0..8 { next.tick().await.unwrap(); }
    let second = next.acquire_or_renew().await.unwrap().unwrap();
    assert!(second.term > first.term);
    assert!(old.save(b"stale state", first.term).await.is_err());
    assert!(old.assign_group(&[Name::parse("Durable.target")], keys.workspace("w0").unwrap().0,
        b"stale assignment", first.term).await.is_err());
    let (worker, _) = keys.workspace("w0").unwrap();
    let receipt = fixture::package("stale-receipt", worker, &Signer::derive("validator"),
        &Name::parse("Durable.free"), vec![], None, 1).receipt;
    assert!(old.record_receipt(&worker, b"stale-j2", &receipt, first.term).await.is_err());
    assert!(store.meta.get(store.meta.keys.job_receipt(&worker, b"stale-j2")).await.unwrap().is_none());

    next.save(b"new leader state", second.term).await.unwrap();
    assert_eq!(old.load().await.unwrap(), Some(b"new leader state".to_vec()));
    assert_eq!(next.assign_group(&[Name::parse("Durable.target")], worker, b"new assignment", second.term).await.unwrap(), vec![0]);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn shard_terms_and_target_catalog_are_independent() {
    let cfg = StoreConfig::from_env(&deployment("durable-shards")).unwrap();
    let keys = KeyFile::demo(2);
    let store = Store::open(&cfg, keys.ring(), Faults::none()).unwrap();
    let a = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    let b = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let stale = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    let la = a.acquire_or_renew().await.unwrap().unwrap();
    let lb = b.acquire_or_renew().await.unwrap().unwrap();
    a.save(b"shard a", la.term).await.unwrap();
    b.save(b"shard b", lb.term).await.unwrap();
    assert_eq!(a.load().await.unwrap().unwrap(), b"shard a");
    assert_eq!(b.load().await.unwrap().unwrap(), b"shard b");
    for _ in 0..8 { stale.tick().await.unwrap(); }
    let takeover = stale.acquire_or_renew().await.unwrap().unwrap();
    assert!(takeover.term > la.term);
    assert!(a.save(b"stale", la.term).await.is_err());
    // Shard 1 has its own clock and remains live during shard 0 takeover.
    b.save(b"shard b live", lb.term).await.unwrap();
    let (owner, _) = keys.workspace("w0").unwrap();
    let name = Name::parse("Shared.Target");
    b.assign_group(&[name.clone()], owner, b"shared-group", lb.term).await.unwrap();
    assert_eq!(a.shard_for_target(&name).await.unwrap(), 1);
    assert!(stale.assign_group(&[name], owner, b"wrong-shard", takeover.term).await.is_err());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn expired_same_holder_cannot_reuse_old_term_or_write_during_gap() {
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-term-gap")).unwrap(),
        KeyFile::demo(1).ring(), Faults::none()).unwrap();
    let ctl = Durable::new(store, Duration::from_millis(500));
    let first = ctl.acquire_or_renew().await.unwrap().unwrap();
    for _ in 0..8 { ctl.tick().await.unwrap(); }
    assert!(ctl.save(b"expired", first.term).await.is_err());
    let second = ctl.acquire_or_renew().await.unwrap().unwrap();
    assert!(second.term > first.term);
    assert!(ctl.save(b"old term", first.term).await.is_err());
    ctl.save(b"new term", second.term).await.unwrap();
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn different_topology_is_rejected_before_a_leader_can_write() {
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-topology")).unwrap(),
        KeyFile::demo(1).ring(), Faults::none()).unwrap();
    let two = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    two.acquire_or_renew().await.unwrap().unwrap();
    let three = Durable::new_shard(store, Duration::from_millis(500), 1, 3);
    assert!(three.acquire_or_renew().await.is_err());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn legacy_controller_state_requires_offline_migration() {
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-legacy-reject")).unwrap(),
        KeyFile::demo(1).ring(), Faults::none()).unwrap();
    let old_key = store.meta.keys.root.pack(&("controller", "state"));
    let trx = store.meta.db.create_trx().unwrap();
    trx.set(&old_key, b"legacy snapshot head");
    trx.commit().await.unwrap();
    let new = Durable::new(store, Duration::from_millis(500));
    assert!(new.acquire_or_renew().await.is_err());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn queued_target_claim_blocks_another_shards_assignment() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-queued-claim")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let owner = keys.workspace("w0").unwrap().0;
    let a = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    let b = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let ta = a.acquire_or_renew().await.unwrap().unwrap().term;
    let tb = b.acquire_or_renew().await.unwrap().unwrap().term;
    let name = (0..100).map(|n| Name::parse(&format!("Queued.target{n}")))
        .find(|n| Durable::hash_shard(n, 2) == 0).unwrap();
    a.reserve_work_shard("queued/1", &name, ta).await.unwrap();
    assert_eq!(b.shard_for_target(&name).await.unwrap(), 0);
    assert!(b.assign_group(&[name.clone()], owner, b"steal", tb).await.is_err());
    assert!(store.meta.target(&name).await.unwrap().is_none());
    assert_eq!(a.assign_group(&[name], owner, b"owner", ta).await.unwrap(), vec![0]);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn submitted_work_routes_before_another_shard_can_claim_target() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-submit-route")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let cfg = ControllerConfig {
        store: store.clone(), authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 4, max_validations: 1, validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    };
    let a = ControlPlane::new_shard(cfg.clone(), 0, 2);
    let b = ControlPlane::new_shard(cfg, 1, 2);
    let name = (0..100).map(|n| Name::parse(&format!("Submit.target{n}")))
        .find(|n| Durable::hash_shard(n, 2) == 0).unwrap();
    assert_eq!(a.handle(ControlRequest::SubmitWork {
        request: "submit/1".into(), target: name.to_string(), memory_mb: 1,
    }).await, ControlResponse::Queued);
    assert_eq!(b.handle(ControlRequest::AssignGroup {
        targets: vec![name.to_string()], worker: keys.workspace("w0").unwrap().0.hex(), request: "steal/1".into(), statements: vec![],
    }).await, ControlResponse::Inconclusive { reason: "not controller shard".into() });
    assert!(store.meta.target(&name).await.unwrap().is_none());
    let ControlResponse::Status { status } = a.handle(ControlRequest::Status).await else { panic!("no shard status") };
    assert_eq!(status["work"].as_array().unwrap().len(), 1);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn target_free_job_routes_its_cancellation_to_issuing_shard() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-validation-route")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let issuer = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let reader = Durable::new_shard(store, Duration::from_millis(500), 0, 2);
    let term = issuer.acquire_or_renew().await.unwrap().unwrap().term;
    let (worker, _) = keys.workspace("w0").unwrap();
    let package = fixture::package("target-free-route", worker, &Signer::derive("validator"),
        &Name::parse("Route.Free"), vec![], None, 1);
    let request = String::from_utf8(package.job.body.request.clone()).unwrap();
    issuer.issue_job(&package.job, term).await.unwrap();
    assert_eq!(reader.shard_for_validation(&worker, &request).await.unwrap(), Some(1));
    let wrong = ControlPlane::new_shard(ControllerConfig {
        store: issuer.store.clone(), authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 4, max_validations: 1, validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    }, 0, 2);
    let response = wrong.handle(ControlRequest::Validate {
        worker: worker.hex(), request: request.clone(), group: "bad".into(), capsule: "bad".into(),
        deps: vec![], targets: vec![], memory_mb: 0, deadline_ms: 0,
    }).await;
    assert_eq!(response, ControlResponse::Inconclusive { reason: "not controller shard".into() });
    let other_term = reader.acquire_or_renew().await.unwrap().unwrap().term;
    assert!(reader.record_receipt(&worker, request.as_bytes(), &package.receipt, other_term).await.is_err());
    issuer.record_receipt(&worker, request.as_bytes(), &package.receipt, term).await.unwrap();
    issuer.cancel_job(&worker, request.as_bytes(), term).await.unwrap();
    assert!(issuer.store.meta.is_cancelled(&worker, request.as_bytes()).await.unwrap());
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn unowned_fence_can_be_taken_by_later_registered_worker() {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-unowned-handoff")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let cfg = ControllerConfig {
        store: store.clone(), authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 4, max_validations: 1, validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    };
    let ctl = ControlPlane::new(cfg);
    let (old, _) = keys.workspace("w0").unwrap();
    let (next, _) = keys.workspace("w1").unwrap();
    let target = Name::parse("Unowned.Handoff");
    assert!(matches!(ctl.handle(ControlRequest::Register { worker: old.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    assert_eq!(ctl.handle(ControlRequest::SubmitWork {
        request: "unowned/1".into(), target: target.to_string(), memory_mb: 1,
    }).await, ControlResponse::Queued);
    let ControlResponse::Work { epoch: first_epoch, .. } = ctl.handle(ControlRequest::Poll {
        worker: old.hex(),
    }).await else { panic!("initial poll did not assign work") };
    let clock = Durable::new(store.clone(), Duration::from_millis(500));
    for _ in 0..9 { clock.tick().await.unwrap(); }
    ctl.expire_leases().await;
    let fenced = store.target(&target).await.unwrap().unwrap();
    assert_eq!(fenced.owner, paralean_control::controller::unowned());
    assert!(fenced.epoch > first_epoch);
    assert!(matches!(ctl.handle(ControlRequest::Register { worker: next.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    let poll = ControlRequest::PollRequest { worker: next.hex(), request: "unowned/poll".into() };
    let response = ctl.handle(poll.clone()).await;
    assert_eq!(matches!(&response, ControlResponse::Work { request, epoch, .. }
        if request == "unowned/1" && *epoch > fenced.epoch), true,
        "later worker did not receive fenced work: {response:?}");
    assert_eq!(ctl.handle(poll).await, response, "poll retry changed assignment");
    assert_eq!(store.target(&target).await.unwrap().unwrap().owner, next);
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn replay_of_external_assignment_commits_the_controller_shard_claim() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-external-t4-claim")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let a = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    let b = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let aterm = a.acquire_or_renew().await.unwrap().unwrap().term;
    let bterm = b.acquire_or_renew().await.unwrap().unwrap().term;
    let target = Name::parse("External.Assignment");
    let (owner, _) = keys.workspace("w0").unwrap();
    let request = b"external-request";
    let epoch = paralean_store::Controller::new(store.clone(), keys.authority_signer().unwrap())
        .reassign(&target, owner, request).await.unwrap();
    assert_eq!(a.assign_group(&[target.clone()], owner, request, aterm).await.unwrap(), vec![epoch]);
    assert_eq!(b.shard_for_target(&target).await.unwrap(), 0);
    assert!(b.assign_group(&[target.clone()], owner, b"cross-shard", bterm).await.is_err());
    assert_eq!(store.target(&target).await.unwrap().unwrap().epoch, epoch);
}

/// W2-32 over W4's validation catalog: one request ID of two workspaces is two
/// requests. Each routes to its own shard, is issued, receipted and cancelled there,
/// and neither squats the other's route.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn sharded_validation_routes_are_scoped_per_workspace() {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-scoped-routes")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let a = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    let b = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let ta = a.acquire_or_renew().await.unwrap().unwrap().term;
    let tb = b.acquire_or_renew().await.unwrap().unwrap().term;
    let ((wa, _), (wb, _)) = (keys.workspace("w0").unwrap(), keys.workspace("w1").unwrap());
    let validator = Signer::derive("validator");
    let pa = fixture::package("scoped-route", wa, &validator, &Name::parse("Route.A"), vec![], None, 1);
    // One request ID for both workspaces (the routing keys under test read only the body).
    let mut pb = fixture::package("scoped-route", wb, &validator, &Name::parse("Route.B"), vec![], None, 1);
    pb.job.body.request = pa.job.body.request.clone();
    let request = String::from_utf8(pa.job.body.request.clone()).unwrap();
    a.issue_job(&pa.job, ta).await.unwrap();
    b.issue_job(&pb.job, tb).await.unwrap();
    assert_eq!(a.shard_for_validation(&wa, &request).await.unwrap(), Some(0));
    assert_eq!(a.shard_for_validation(&wb, &request).await.unwrap(), Some(1));
    b.record_receipt(&wb, request.as_bytes(), &pb.receipt, tb).await.unwrap();
    a.record_receipt(&wa, request.as_bytes(), &pa.receipt, ta).await.unwrap();
    b.cancel_job(&wb, request.as_bytes(), tb).await.unwrap();
    assert!(store.meta.is_cancelled(&wb, request.as_bytes()).await.unwrap());
    assert!(!store.meta.is_cancelled(&wa, request.as_bytes()).await.unwrap());
}

/// W2-33's request-ID bound runs before W4's shard routing: an over-long ID is refused
/// without reserving a work shard or claiming its target.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn overlong_request_id_is_refused_before_shard_routing() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-long-request")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let cfg = ControllerConfig {
        store: store.clone(), authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 4, max_validations: 1, validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    };
    let ctl = ControlPlane::new_shard(cfg, 0, 2);
    let request = "r".repeat(paralean_control::controller::MAX_REQUEST_ID + 1);
    let name = Name::parse("Long.request");
    let response = ctl.handle(ControlRequest::SubmitWork {
        request: request.clone(), target: name.to_string(), memory_mb: 1,
    }).await;
    assert!(matches!(response, ControlResponse::Refused { .. }), "{response:?}");
    let reader = Durable::new_shard(store, Duration::from_millis(500), 0, 2);
    assert_eq!(reader.shard_for_work(&request).await.unwrap(), None, "a refused request reserved a work shard");
    assert_eq!(reader.mapped_shard(&name).await.unwrap(), None, "a refused request claimed its target");
}

/// W2-33 over W4 history: the snapshot keeps a worker's newest poll tokens only, and an
/// older token leaves it as a replay row, so a late retry of it still returns its first
/// answer rather than a fresh poll's.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn spilled_poll_tokens_keep_their_first_answer() {
    let keys = KeyFile::demo(1);
    let store = Store::open(&StoreConfig::from_env(&deployment("durable-spilled-poll")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let cfg = ControllerConfig {
        store, authority: keys.authority_signer().unwrap(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: Duration::from_millis(500),
        max_work_queue: 4, max_validations: 1, validation_deadline: Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    };
    let ctl = ControlPlane::new(cfg);
    let (w, _) = keys.workspace("w0").unwrap();
    assert!(matches!(ctl.handle(ControlRequest::Register { worker: w.hex(), capacity_mb: 128 }).await,
        ControlResponse::Registered { .. }));
    assert_eq!(ctl.handle(ControlRequest::SubmitWork {
        request: "spill/1".into(), target: "Spill.target".into(), memory_mb: 1,
    }).await, ControlResponse::Queued);
    let first = ControlRequest::PollRequest { worker: w.hex(), request: "spill/token/0".into() };
    let answer = ctl.handle(first.clone()).await;
    assert!(matches!(&answer, ControlResponse::Work { request, .. } if request == "spill/1"), "{answer:?}");
    for i in 1..=paralean_control::controller::MAX_POLL_TOKENS_PER_WORKER + 2 {
        let later = ControlRequest::PollRequest { worker: w.hex(), request: format!("spill/token/{i}") };
        assert_eq!(ctl.handle(later).await, ControlResponse::NoWork);
    }
    assert_eq!(ctl.handle(first).await, answer, "a retried spilled token lost its first answer");
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("elapsed_wall_time_alone_cannot_expire_a_lease", || { elapsed_wall_time_alone_cannot_expire_a_lease(); Ok(()) }),
        libtest_mimic::Trial::test("large_snapshot_roundtrips_and_old_leader_writes_are_fenced", || { large_snapshot_roundtrips_and_old_leader_writes_are_fenced(); Ok(()) }),
        libtest_mimic::Trial::test("shard_terms_and_target_catalog_are_independent", || { shard_terms_and_target_catalog_are_independent(); Ok(()) }),
        libtest_mimic::Trial::test("expired_same_holder_cannot_reuse_old_term_or_write_during_gap", || { expired_same_holder_cannot_reuse_old_term_or_write_during_gap(); Ok(()) }),
        libtest_mimic::Trial::test("different_topology_is_rejected_before_a_leader_can_write", || { different_topology_is_rejected_before_a_leader_can_write(); Ok(()) }),
        libtest_mimic::Trial::test("legacy_controller_state_requires_offline_migration", || { legacy_controller_state_requires_offline_migration(); Ok(()) }),
        libtest_mimic::Trial::test("queued_target_claim_blocks_another_shards_assignment", || { queued_target_claim_blocks_another_shards_assignment(); Ok(()) }),
        libtest_mimic::Trial::test("submitted_work_routes_before_another_shard_can_claim_target", || { submitted_work_routes_before_another_shard_can_claim_target(); Ok(()) }),
        libtest_mimic::Trial::test("target_free_job_routes_its_cancellation_to_issuing_shard", || { target_free_job_routes_its_cancellation_to_issuing_shard(); Ok(()) }),
        libtest_mimic::Trial::test("unowned_fence_can_be_taken_by_later_registered_worker", || { unowned_fence_can_be_taken_by_later_registered_worker(); Ok(()) }),
        libtest_mimic::Trial::test("replay_of_external_assignment_commits_the_controller_shard_claim", || { replay_of_external_assignment_commits_the_controller_shard_claim(); Ok(()) }),
        libtest_mimic::Trial::test("sharded_validation_routes_are_scoped_per_workspace", || { sharded_validation_routes_are_scoped_per_workspace(); Ok(()) }),
        libtest_mimic::Trial::test("overlong_request_id_is_refused_before_shard_routing", || { overlong_request_id_is_refused_before_shard_routing(); Ok(()) }),
        libtest_mimic::Trial::test("spilled_poll_tokens_keep_their_first_answer", || { spilled_poll_tokens_keep_their_first_answer(); Ok(()) }),
    ]);
}
