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
        let signer = c.kf.workspace("w0").unwrap().1;
        let server = c.kf.authority_signer().unwrap().public();
        hs.push(tokio::spawn(async move {
            rpc::call_authenticated::<_, ControlResponse>(&addr, &req, &signer, &server, Duration::from_secs(300)).await.unwrap()
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
    let authority = c.kf.authority_signer().unwrap();
    let validator_keys = vec![c.vsigners[0].public()];
    let (a, b) = tokio::join!(
        paralean_validator_api::validate(&c.vaddrs[0], &job, &authority, &validator_keys, Duration::from_secs(300)),
        paralean_validator_api::validate(&c.vaddrs[0], &job, &authority, &validator_keys, Duration::from_secs(300))
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
    assert!(c.store.meta.get(c.store.meta.keys.job_receipt(&w.id(), b"to/1")).await.unwrap().is_none());
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
    let signer = c.kf.workspace("w0").unwrap().1;
    let server = c.kf.authority_signer().unwrap().public();
    let running = tokio::spawn(async move { rpc::call_authenticated::<_, ControlResponse>(&addr, &req, &signer, &server, Duration::from_secs(120)).await.unwrap() });
    // Wait until the checker runs.
    let t0 = Instant::now();
    while !matches!(c.validators[0].handle(ValidatorRequest::Status).await, ValidatorResponse::Status { running: 1, .. }) {
        assert!(t0.elapsed() < Duration::from_secs(10));
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let t1 = Instant::now();
    assert_eq!(c.call(ControlRequest::Cancel { request: "cx/1".into(), worker: String::new() }).await, ControlResponse::Cancelled);
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
    assert_eq!(c.call(ControlRequest::Cancel { request: "cx/work".into(), worker: String::new() }).await, ControlResponse::Cancelled);
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
    let signer = c.kf.workspace("w0").unwrap().1;
    let server = c.kf.authority_signer().unwrap().public();
    let first = tokio::spawn(async move { rpc::call_authenticated::<_, ControlResponse>(&addr, &req, &signer, &server, Duration::from_secs(120)).await.unwrap() });
    let t0 = Instant::now();
    while !matches!(c.validators[0].handle(ValidatorRequest::Status).await, ValidatorResponse::Status { running: 1, .. }) {
        assert!(t0.elapsed() < Duration::from_secs(10));
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    // The controller's validation queue is full, and nothing is recorded for the refusal.
    assert_eq!(c.call(validate_req(&w, &g, "bp/2")).await, ControlResponse::Busy);
    assert!(c.store.meta.get(c.store.meta.keys.job_request(&w.id(), b"bp/2")).await.unwrap().is_none());
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
    assert_eq!(paralean_validator_api::validate(&c.vaddrs[0], &job, &c.kf.authority_signer().unwrap(), &[c.vsigners[0].public()], Duration::from_secs(10)).await.unwrap(), ValidatorResponse::Busy);
    // The work queue holds two jobs.
    for (i, want) in [ControlResponse::Queued, ControlResponse::Queued, ControlResponse::Busy].into_iter().enumerate() {
        let sub = ControlRequest::SubmitWork { request: format!("bp/work{i}"), target: format!("T{i}"), memory_mb: 64 };
        assert_eq!(c.call(sub).await, want);
    }
    c.call(ControlRequest::Cancel { request: "bp/1".into(), worker: String::new() }).await;
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

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn request_ids_are_scoped_per_workspace() {
    // Worker w1 claims the request ID w0 will use for a dependency (`dep/<decl>` is
    // guessable) and the authority cancels w1's request. Neither the claim (J1, the
    // in-flight map, the validators' slots, J2) nor the cancellation (J3) reaches w0's
    // request of the same ID.
    let c = Cluster::start("scoped", Opts::default()).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let g = w0.group_declaring(&n("F01.small")).unwrap().clone();
    let request = format!("dep/{}", g.decl.hex());
    let (_, squat) = w1.validate(&g, &request, &[], 0).await.unwrap();
    assert_eq!(squat.body.worker, w1.id());
    let cancel = ControlRequest::Cancel { request: request.clone(), worker: w1.id().hex() };
    assert_eq!(c.call(cancel).await, ControlResponse::Cancelled);
    let (r, j) = w0.validate(&g, &request, &[], 0).await.expect("w0's own request ID");
    assert_eq!(j.body.worker, w0.id());
    assert_ne!(j.id(), squat.id());
    match w1.validate(&g, &request, &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Cancelled)) => {}
        other => panic!("w1's cancelled request: {other:?}"),
    }
    assert!(c.store.meta.is_cancelled(&w1.id(), request.as_bytes()).await.unwrap());
    assert!(!c.store.meta.is_cancelled(&w0.id(), request.as_bytes()).await.unwrap());
    w0.writer.publish(&w0.package(&g, r, j, vec![])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn inconclusive_recovery_is_bounded() {
    // An envelope (J1) whose client is gone and that no validator decides: a validator
    // address that accepts and drops every connection. Each takeover re-dispatches it once,
    // not on every lease tick, and only `validator_attempts` times over all leaders.
    let cfg = StoreConfig::from_env(&deployment("recover")).unwrap();
    let kf = KeyFile::demo(2);
    let store = Store::open(&cfg, kf.ring(), Faults::none()).unwrap();
    let authority = kf.authority_signer().unwrap();
    let sink = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let sink_addr = sink.local_addr().unwrap().to_string();
    let accepted = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let count = accepted.clone();
    let sink_task = tokio::spawn(async move {
        loop {
            let Ok((sock, _)) = sink.accept().await else { continue };
            count.fetch_add(1, Ordering::SeqCst);
            drop(sock);
        }
    });
    let (worker, _) = kf.workspace("w0").unwrap();
    let job = paralean_store::receipt::SignedJob::sign(paralean_store::receipt::JobEnvelope {
        request: b"recover/lost-client".to_vec(), group: Id([1; 32]), capsule: Id([2; 32]), deps: vec![],
        base: Id([3; 32]), policy: Id([4; 32]), checker: Id([5; 32]), worker, targets: vec![],
        deadline_ms: 1000, memory_mb: 0,
    }, &authority);
    store.meta.issue_job(&job).await.unwrap();
    let attempts = 2;
    let leader = || paralean_control::controller::ControlPlane::new(paralean_control::controller::ControllerConfig {
        store: store.clone(), authority: authority.clone(), validators: vec![sink_addr.clone()],
        base: Id([3; 32]), policy: Id([4; 32]), checker: Id([5; 32]), lease: Duration::from_millis(500),
        max_work_queue: 4, max_validations: 4, validation_deadline: Duration::from_secs(1), validation_memory_mb: 1024,
        validator_attempts: attempts,
    });
    // One dispatch tries the one validator `attempts` times.
    let per_dispatch = attempts;
    let mut seen = Vec::new();
    for _ in 0..3 {
        let ctl = leader();
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let serving = ctl.serve(listener);
        // Many lease ticks (every 125 ms) under one leader.
        tokio::time::sleep(Duration::from_millis(2500)).await;
        serving.abort();
        seen.push(accepted.load(Ordering::SeqCst));
        // Let its lease lapse so the next replica takes over with a new term.
        tokio::time::sleep(Duration::from_millis(700)).await;
    }
    sink_task.abort();
    assert_eq!(seen, vec![per_dispatch, 2 * per_dispatch, 2 * per_dispatch],
        "recovery dispatches per leader (cumulative connection counts)");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn dropped_validation_still_finishes_and_releases_its_resources() {
    // The RPC server drops a handler future at its execution limit (and a client may go
    // away). Two checks are dropped: one running, one waiting in the queue. Both still
    // finish, their receipts land in their slots for a retry, and the queued and running
    // counts and scratch directories return to nothing.
    let o = Opts { validators: vec![Mode::Real], validator_max_running: 1, ..Opts::default() };
    let c = Cluster::start("detached", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    w.writer.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    let authority = c.kf.authority_signer().unwrap();
    let job = |request: &str| paralean_store::receipt::SignedJob::sign(paralean_store::receipt::JobEnvelope {
        request: request.as_bytes().to_vec(),
        group: g.decl,
        capsule: g.capsule_id(),
        deps: vec![],
        base: paralean_control::checker::base_id(&c.checker.lean_githash),
        policy: paralean_store::receipt::Policy::v1().id(),
        checker: c.validators[0].checker_id(),
        worker: w.id(),
        targets: vec![],
        deadline_ms: 120_000,
        memory_mb: 0,
    }, &authority);
    let v = c.validators[0].clone();
    let jobs = [job("detached/1"), job("detached/2")];
    for j in &jobs {
        assert!(tokio::time::timeout(Duration::from_millis(30), v.validate(j.clone())).await.is_err(), "check finished before the drop");
    }
    let t0 = Instant::now();
    while checks_run(&c) < 2 {
        assert!(t0.elapsed() < Duration::from_secs(120), "a dropped check did not finish");
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    let ValidatorResponse::Status { running, queued, .. } = v.handle(ValidatorRequest::Status).await else { panic!() };
    assert_eq!((running, queued), (0, 0));
    for j in &jobs {
        match v.validate(j.clone()).await {
            ValidatorResponse::Receipt { receipt } => {
                assert_eq!(paralean_validator_api::decode_receipt(&receipt).unwrap().body.request, Some(j.id().0.to_vec()));
            }
            other => panic!("retry after a dropped check: {other:?}"),
        }
    }
    assert_eq!(checks_run(&c), 2, "a retry checked again instead of taking the finished receipt");
    let left: Vec<_> = std::fs::read_dir(c.tmp.join("validator-0")).unwrap().collect();
    assert!(left.is_empty(), "scratch directories left behind: {left:?}");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn validator_slots_are_scoped_by_issuer_and_workspace() {
    // One request ID in envelopes for two workspaces, and from a job issuer and the
    // controller for one workspace: each envelope gets its own receipt.
    let issuer = Signer::derive("p3-scoped-issuer");
    let c = Cluster::start("vslots", Opts { validators: vec![Mode::Real], job_issuers: vec![issuer.clone()], ..Opts::default() }).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let g = w0.group_declaring(&n("F01.small")).unwrap().clone();
    w0.writer.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w0.writer.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    let authority = c.kf.authority_signer().unwrap();
    let env = |worker: WorkspaceId| paralean_store::receipt::JobEnvelope {
        request: b"same/request".to_vec(),
        group: g.decl,
        capsule: g.capsule_id(),
        deps: vec![],
        base: paralean_control::checker::base_id(&c.checker.lean_githash),
        policy: paralean_store::receipt::Policy::v1().id(),
        checker: c.validators[0].checker_id(),
        worker,
        targets: vec![],
        deadline_ms: 120_000,
        memory_mb: 0,
    };
    let jobs = [
        paralean_store::receipt::SignedJob::sign(env(w1.id()), &issuer),
        paralean_store::receipt::SignedJob::sign(env(w1.id()), &authority),
        paralean_store::receipt::SignedJob::sign(env(w0.id()), &authority),
    ];
    for job in &jobs {
        match c.validators[0].validate(job.clone()).await {
            ValidatorResponse::Receipt { receipt } => {
                let r = paralean_validator_api::decode_receipt(&receipt).unwrap();
                assert_eq!(r.body.request, Some(job.id().0.to_vec()));
            }
            other => panic!("envelope for {} refused: {other:?}", job.body.worker.hex()),
        }
    }
    assert_eq!(checks_run(&c), 3);
}
