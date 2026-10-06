//! Controller and validator operation against the live services: retry deduplication,
//! validator timeouts and memory limits, cancellation, backpressure, memory admission.

mod common;

use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};

use common::*;
use paralean_control::controller::{ControlRequest, ControlResponse};
use paralean_control::worker::WorkerError;
use paralean_store::*;
use paralean_validator_api::{rpc, ValidatorRequest, ValidatorResponse};

fn n(s: &str) -> Name {
    Name::parse(s)
}

fn checks_run(c: &Cluster) -> u64 {
    c.validators.iter().map(|v| v.checks_run.load(Ordering::SeqCst)).sum()
}

fn validate_req(w: &paralean_control::worker::WorkerNode, g: &paralean_control::p1::P1Group, request: &str) -> ControlRequest {
    ControlRequest::Validate {
        worker: w.id().hex(),
        request: request.into(),
        group: g.decl.hex(),
        capsule: g.capsule_id().hex(),
        deps: vec![],
        targets: vec![],
        memory_mb: 0,
        deadline_ms: 0,
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn duplicate_and_retried_jobs_are_deduplicated() {
    let c = Cluster::start("dedup", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    w.writer.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    // Four concurrent copies of one request: one check, one receipt.
    let mut hs = Vec::new();
    for _ in 0..4 {
        let addr = c.ctl_addr.clone();
        let req = validate_req(&w, &g, "dup/1");
        hs.push(tokio::spawn(async move {
            rpc::call::<_, ControlResponse>(&addr, &req, Duration::from_secs(300)).await.unwrap()
        }));
    }
    let mut answers = Vec::new();
    for h in hs {
        answers.push(h.await.unwrap());
    }
    assert!(matches!(answers[0], ControlResponse::Receipt { .. }), "{:?}", answers[0]);
    assert!(answers.iter().all(|a| *a == answers[0]), "{answers:?}");
    assert_eq!(checks_run(&c), 1);
    // A retry after completion: the recorded receipt, no new check.
    assert_eq!(c.call(validate_req(&w, &g, "dup/1")).await, answers[0]);
    assert_eq!(checks_run(&c), 1);
    // The request ID reused for another group is refused.
    let other = w.group_declaring(&n("F01.two_eq")).unwrap().clone();
    w.writer.store.s3.put_opaque(&other.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&other.capsule_object()).await.unwrap();
    match c.call(validate_req(&w, &other, "dup/1")).await {
        ControlResponse::Refused { reason } => assert!(reason.contains("another envelope"), "{reason}"),
        r => panic!("{r:?}"),
    }
    // The validator deduplicates envelopes sent to it directly, too.
    let ControlResponse::Receipt { job, .. } = &answers[0] else { unreachable!() };
    let job = paralean_store::receipt::SignedJob::from_bytes(&hex::decode(job).unwrap()).unwrap();
    let before = c.validators[0].checks_run.load(Ordering::SeqCst);
    let (a, b) = tokio::join!(
        paralean_validator_api::validate(&c.vaddrs[0], &job, Duration::from_secs(300)),
        paralean_validator_api::validate(&c.vaddrs[0], &job, Duration::from_secs(300))
    );
    assert_eq!(a.unwrap(), b.unwrap());
    assert!(c.validators[0].checks_run.load(Ordering::SeqCst) <= before + 1);
    // Work submissions and publications are idempotent by request and by content.
    let sub = ControlRequest::SubmitWork { request: "dup/work".into(), target: "F01.uses_small".into(), memory_mb: 64 };
    assert_eq!(c.call(sub.clone()).await, ControlResponse::Queued);
    assert!(matches!(c.call(sub).await, ControlResponse::Duplicate { .. }));
    let ControlResponse::Receipt { receipt, job } = &answers[0] else { unreachable!() };
    let r = Receipt::from_bytes(&hex::decode(receipt).unwrap()).unwrap();
    let j = paralean_store::receipt::SignedJob::from_bytes(&hex::decode(job).unwrap()).unwrap();
    let p = w.package(&g, r, j, vec![]);
    assert!(w.writer.publish(&p).await.unwrap().fresh);
    assert!(!w.writer.publish(&p).await.unwrap().fresh);
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn validator_timeouts_give_no_receipt() {
    // Every validator hangs: no verdict within the deadline, nothing recorded.
    let o = Opts { validators: vec![Mode::Sleep, Mode::Sleep], deadline_ms: 700, attempts: 2, ..Opts::default() };
    let c = Cluster::start("timeout", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    let t0 = Instant::now();
    match w.validate(&g, "to/1", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Inconclusive { reason })) => assert!(reason.contains("deadline"), "{reason}"),
        other => panic!("{other:?}"),
    }
    assert!(t0.elapsed() < Duration::from_secs(20));
    assert!(c.store.meta.get(c.store.meta.keys.job_receipt(b"to/1")).await.unwrap().is_none());
    assert_eq!(checks_run(&c), 0);
    for v in &c.validators {
        assert!(matches!(v.handle(ValidatorRequest::Status).await, ValidatorResponse::Status { running: 0, .. }));
    }
    assert!(!published(&c.store, &g.decl).await);
    // One hanging validator, one working: the controller moves on and gets a receipt.
    let o = Opts { validators: vec![Mode::Sleep, Mode::Wrapped], deadline_ms: 5_000, attempts: 4, ..Opts::default() };
    let c = Cluster::start("timeout2", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let (r, j) = w.validate(&g, "to/2", &[], 0).await.unwrap();
    assert_eq!(r.body.validator_key, c.vsigners[1].public());
    w.writer.publish(&w.package(&g, r, j, vec![])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn checker_memory_limit_gives_no_receipt() {
    let o = Opts { validators: vec![Mode::Memory], memory_mb: 200, deadline_ms: 30_000, attempts: 1, ..Opts::default() };
    let c = Cluster::start("memory", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    let t0 = Instant::now();
    match w.validate(&g, "mem/1", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Inconclusive { reason })) => assert!(reason.contains("memory limit"), "{reason}"),
        other => panic!("{other:?}"),
    }
    assert!(t0.elapsed() < Duration::from_secs(20), "killed long before the deadline");
    // The real checker fits in the default limit (4 GiB) and in 1 GiB.
    let c = Cluster::start("memory2", Opts { memory_mb: 1024, ..Opts::default() }).await;
    let w = c.worker(0, 8192, &core_store()).await;
    w.validate(&g, "mem/2", &[], 0).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn cancellation_stops_checks_and_publication() {
    let o = Opts { validators: vec![Mode::Sleep], deadline_ms: 60_000, attempts: 1, ..Opts::default() };
    let c = Cluster::start("cancel", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    w.writer.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    let addr = c.ctl_addr.clone();
    let req = validate_req(&w, &g, "cx/1");
    let running = tokio::spawn(async move { rpc::call::<_, ControlResponse>(&addr, &req, Duration::from_secs(120)).await.unwrap() });
    // Wait until the checker runs.
    let t0 = Instant::now();
    while !matches!(c.validators[0].handle(ValidatorRequest::Status).await, ValidatorResponse::Status { running: 1, .. }) {
        assert!(t0.elapsed() < Duration::from_secs(10));
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let t1 = Instant::now();
    assert_eq!(c.call(ControlRequest::Cancel { request: "cx/1".into() }).await, ControlResponse::Cancelled);
    assert_eq!(running.await.unwrap(), ControlResponse::Cancelled);
    assert!(t1.elapsed() < Duration::from_secs(10));
    // The checker process was killed.
    let t0 = Instant::now();
    while !matches!(c.validators[0].handle(ValidatorRequest::Status).await, ValidatorResponse::Status { running: 0, .. }) {
        assert!(t0.elapsed() < Duration::from_secs(5), "checker still running after cancel");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    // Retrying a cancelled request gives nothing.
    assert_eq!(c.call(validate_req(&w, &g, "cx/1")).await, ControlResponse::Cancelled);
    // A queued work job is cancelled and never handed out.
    let sub = ControlRequest::SubmitWork { request: "cx/work".into(), target: "F01.uses_small".into(), memory_mb: 64 };
    assert_eq!(c.call(sub).await, ControlResponse::Queued);
    assert_eq!(c.call(ControlRequest::Cancel { request: "cx/work".into() }).await, ControlResponse::Cancelled);
    assert!(w.poll().await.unwrap().is_none());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn queues_apply_backpressure() {
    let o = Opts {
        validators: vec![Mode::Sleep],
        deadline_ms: 60_000,
        attempts: 1,
        max_validations: 1,
        max_work_queue: 2,
        validator_max_running: 1,
        validator_max_queued: 0,
        ..Opts::default()
    };
    let c = Cluster::start("busy", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    w.writer.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    let addr = c.ctl_addr.clone();
    let req = validate_req(&w, &g, "bp/1");
    let first = tokio::spawn(async move { rpc::call::<_, ControlResponse>(&addr, &req, Duration::from_secs(120)).await.unwrap() });
    let t0 = Instant::now();
    while !matches!(c.validators[0].handle(ValidatorRequest::Status).await, ValidatorResponse::Status { running: 1, .. }) {
        assert!(t0.elapsed() < Duration::from_secs(10));
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    // The controller's validation queue is full, and nothing is recorded for the refusal.
    assert_eq!(c.call(validate_req(&w, &g, "bp/2")).await, ControlResponse::Busy);
    assert!(c.store.meta.get(c.store.meta.keys.job_request(b"bp/2")).await.unwrap().is_none());
    // The validator's own queue is full as well.
    let ControlResponse::Status { .. } = c.call(ControlRequest::Status).await else { panic!() };
    let mut env = paralean_store::receipt::JobEnvelope {
        request: b"bp/direct".to_vec(),
        group: g.decl,
        capsule: g.capsule_id(),
        deps: vec![],
        base: paralean_control::checker::base_id(&c.checker.lean_githash),
        policy: paralean_store::receipt::Policy::v1().id(),
        checker: c.validators[0].checker_id(),
        worker: w.id(),
        targets: vec![],
        deadline_ms: 60_000,
        memory_mb: 0,
    };
    env.request = b"bp/direct".to_vec();
    let job = paralean_store::receipt::SignedJob::sign(env, &c.kf.authority_signer().unwrap());
    assert_eq!(paralean_validator_api::validate(&c.vaddrs[0], &job, Duration::from_secs(10)).await.unwrap(), ValidatorResponse::Busy);
    // The work queue holds two jobs.
    for (i, want) in [ControlResponse::Queued, ControlResponse::Queued, ControlResponse::Busy].into_iter().enumerate() {
        let sub = ControlRequest::SubmitWork { request: format!("bp/work{i}"), target: format!("T{i}"), memory_mb: 64 };
        assert_eq!(c.call(sub).await, want);
    }
    c.call(ControlRequest::Cancel { request: "bp/1".into() }).await;
    assert_eq!(first.await.unwrap(), ControlResponse::Cancelled);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn work_is_admitted_within_each_workers_memory() {
    let c = Cluster::start("admit", Opts::default()).await;
    let small = c.worker(0, 1000, &core_store()).await;
    let big = c.worker(1, 4000, &core_store()).await;
    for (r, t, m) in [("ad/1", "A.one", 600), ("ad/2", "A.two", 600), ("ad/3", "A.three", 3000)] {
        let sub = ControlRequest::SubmitWork { request: r.into(), target: t.into(), memory_mb: m };
        assert_eq!(c.call(sub).await, ControlResponse::Queued);
    }
    let a = small.poll().await.unwrap().expect("first job fits");
    assert_eq!(a.request, "ad/1");
    // 400 MiB left: neither the second (600) nor the third (3000) job fits.
    assert!(small.poll().await.unwrap().is_none());
    let b = big.poll().await.unwrap().expect("the big worker takes the next job");
    assert_eq!(b.request, "ad/2");
    // 3400 MiB left on the big worker: the 3000 MiB job fits there only.
    let b2 = big.poll().await.unwrap().expect("3000 fits in 3400");
    assert_eq!(b2.request, "ad/3");
    // Finishing frees the memory.
    let fin = ControlRequest::Finish { worker: small.id().hex(), request: "ad/1".into(), ok: true };
    assert_eq!(c.call(fin).await, ControlResponse::Ok);
    let sub = ControlRequest::SubmitWork { request: "ad/4".into(), target: "A.four".into(), memory_mb: 900 };
    assert_eq!(c.call(sub).await, ControlResponse::Queued);
    assert_eq!(small.poll().await.unwrap().unwrap().request, "ad/4");
    // Every handed-out job assigned its target to the worker that took it (T4).
    for (t, w) in [("A.one", small.id()), ("A.two", big.id()), ("A.three", big.id()), ("A.four", small.id())] {
        assert_eq!(c.store.target(&n(t)).await.unwrap().unwrap().owner, w);
    }
}
