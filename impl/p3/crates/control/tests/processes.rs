//! The control plane as separate processes (`paralean-p3` controller, two validators, two
//! workers) against the live services. A worker is SIGKILLed while it holds a target job;
//! its lease expires, the target is reassigned with a new epoch, and the other worker
//! publishes the proof. The killed worker's state is gone with it, so this checks the
//! liveness side; the safety side (a stale owner's publication is fenced) is
//! `adversarial::stale_owner_after_lease_expiry_cannot_publish`.

mod common;

use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

use common::*;
use paralean_control::checker::CheckerConfig;
use paralean_control::controller::{ControlRequest, ControlResponse};
use paralean_store::*;
use paralean_validator_api::rpc;

struct Proc(Child);
impl Drop for Proc {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn free_port() -> u16 {
    std::net::TcpListener::bind("127.0.0.1:0").unwrap().local_addr().unwrap().port()
}

fn spawn(args: &[&str], env: &[(&str, String)], log: &std::path::Path) -> Proc {
    let out = std::fs::File::create(log).unwrap();
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_paralean-p3"));
    cmd.args(args).stdout(out.try_clone().unwrap()).stderr(out).stdin(Stdio::null());
    for (k, v) in env {
        cmd.env(k, v);
    }
    Proc(cmd.spawn().unwrap())
}

async fn call(addr: &str, req: ControlRequest, signer: &Signer) -> Option<ControlResponse> {
    rpc::call_authenticated(addr, &req, signer, &signer.public(), Duration::from_secs(30)).await.ok()
}

async fn worker_call(addr: &str, req: ControlRequest, signer: &Signer, authority: &Signer) -> Option<ControlResponse> {
    rpc::call_authenticated(addr, &req, signer, &authority.public(), Duration::from_secs(30)).await.ok()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn leader_killed_after_durable_assignment_redelivers_once() {
    let tmp = scratch("controller-failover");
    let dep = deployment("controller-failover");
    let kf = KeyFile::demo(2);
    let keys = tmp.join("keys.json");
    std::fs::write(&keys, serde_json::to_string(&kf).unwrap()).unwrap();
    let base_env = vec![("PARALEAN_KEYS", keys.display().to_string()), ("PARALEAN_DEPLOYMENT", dep.clone()), ("TMPDIR", tmp.display().to_string())];
    let a = format!("127.0.0.1:{}", free_port());
    let b = format!("127.0.0.1:{}", free_port());
    let mut paused_env = base_env.clone();
    paused_env.push(("PARALEAN_TEST_PAUSE_AFTER_ASSIGN_MS", "10000".into()));
    let mut leader = spawn(&["controller", "--listen", &a, "--validators", "127.0.0.1:1", "--lease-ms", "1200"], &paused_env, &tmp.join("leader.log"));
    let authority = kf.authority_signer().unwrap();
    let (wid, worker_signer) = kf.workspace("w0").unwrap();
    let (replacement_id, replacement_signer) = kf.workspace("w1").unwrap();
    let start = Instant::now();
    loop {
        if matches!(call(&a, ControlRequest::Status, &authority).await,
            Some(ControlResponse::Status { status }) if status["leader"] == true) { break }
        assert!(start.elapsed() < Duration::from_secs(20), "first controller did not lead");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let _standby = spawn(&["controller", "--listen", &b, "--validators", "127.0.0.1:1", "--lease-ms", "1200"], &base_env, &tmp.join("standby.log"));
    let start = Instant::now();
    while !matches!(call(&b, ControlRequest::Status, &authority).await,
        Some(ControlResponse::Status { status }) if status["leader"] == false) {
        assert!(start.elapsed() < Duration::from_secs(20), "standby did not start");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(matches!(worker_call(&a, ControlRequest::Register { worker: wid.hex(), capacity_mb: 4096 }, &worker_signer, &authority).await,
        Some(ControlResponse::Registered { .. })));
    assert_eq!(call(&a, ControlRequest::SubmitWork { request: "failover/one".into(), target: "Failover.target".into(), memory_mb: 64 }, &authority).await,
        Some(ControlResponse::Queued));
    let poll_addr = a.clone();
    let poll_signer = worker_signer.clone();
    let server = authority.public();
    let lost_reply = tokio::spawn(async move {
        rpc::call_authenticated::<_, ControlResponse>(&poll_addr, &ControlRequest::Poll { worker: wid.hex() },
            &poll_signer, &server, Duration::from_secs(20)).await
    });
    let store = Store::open(&StoreConfig::from_env(&dep).unwrap(), kf.ring(), Faults::none()).unwrap();
    let name = Name::parse("Failover.target");
    let start = Instant::now();
    let assigned_epoch = loop {
        if let Some(record) = store.target(&name).await.unwrap() {
            assert_eq!(record.owner, wid);
            break record.epoch;
        }
        assert!(start.elapsed() < Duration::from_secs(20), "assignment was not durable before pause");
        tokio::time::sleep(Duration::from_millis(25)).await;
    };
    leader.0.kill().unwrap();
    leader.0.wait().unwrap();
    assert!(lost_reply.await.unwrap().is_err(), "killed leader returned the pending reply");
    let start = Instant::now();
    loop {
        if matches!(call(&b, ControlRequest::Status, &authority).await,
            Some(ControlResponse::Status { status }) if status["leader"] == true) { break }
        assert!(start.elapsed() < Duration::from_secs(20), "standby did not take over");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    assert!(matches!(worker_call(&b, ControlRequest::Register { worker: replacement_id.hex(), capacity_mb: 4096 },
        &replacement_signer, &authority).await, Some(ControlResponse::Registered { .. })));
    let heartbeat_addr = b.clone();
    let heartbeat_signer = replacement_signer.clone();
    let heartbeat_authority = authority.clone();
    let heartbeat = tokio::spawn(async move {
        loop {
            tokio::time::sleep(Duration::from_millis(200)).await;
            let _ = worker_call(&heartbeat_addr, ControlRequest::Heartbeat { worker: replacement_id.hex() },
                &heartbeat_signer, &heartbeat_authority).await;
        }
    });
    let start = Instant::now();
    loop {
        let record = store.target(&name).await.unwrap().unwrap();
        if record.owner == replacement_id { break }
        assert!(start.elapsed() < Duration::from_secs(20), "lost worker's target was not reassigned");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let work = worker_call(&b, ControlRequest::Poll { worker: replacement_id.hex() }, &replacement_signer, &authority).await;
    assert!(matches!(&work, Some(ControlResponse::Work { request, epoch, .. })
        if request == "failover/one" && *epoch > assigned_epoch), "{work:?}");
    let new_epoch = store.target(&name).await.unwrap().unwrap().epoch;
    assert!(new_epoch > assigned_epoch);
    assert_eq!(worker_call(&b, ControlRequest::Finish { worker: replacement_id.hex(), request: "failover/one".into(), ok: true }, &replacement_signer, &authority).await,
        Some(ControlResponse::Ok));
    let Some(ControlResponse::Status { status }) = call(&b, ControlRequest::Status, &authority).await else { panic!("no leader status") };
    assert_eq!(status["work"].as_array().unwrap().len(), 1);
    assert_eq!(status["work"][0]["state"], "Done");
    assert_eq!(worker_call(&b, ControlRequest::Poll { worker: replacement_id.hex() }, &replacement_signer, &authority).await,
        Some(ControlResponse::NoWork));
    heartbeat.abort();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn killed_owner_is_replaced_and_the_target_published() {
    let tmp = scratch("procs");
    let dep = deployment("procs");
    let checker = CheckerConfig::from_env().unwrap();
    let mut kf = KeyFile::demo(4);
    kf.validators.clear();
    kf.add_validator("v0", &validator_signer(0));
    kf.add_validator("v1", &validator_signer(1));
    kf.policies = vec![paralean_store::receipt::Policy::v1().id().hex()];
    kf.checkers = vec![checker.version().unwrap().id().hex()];
    let keys = tmp.join("keys.json");
    std::fs::write(&keys, serde_json::to_string(&kf).unwrap()).unwrap();
    let env = vec![("PARALEAN_KEYS", keys.display().to_string()), ("PARALEAN_DEPLOYMENT", dep.clone()), ("TMPDIR", tmp.display().to_string())];
    let (pv0, pv1, pc) = (free_port(), free_port(), free_port());
    let (v0, v1, ctl) = (format!("127.0.0.1:{pv0}"), format!("127.0.0.1:{pv1}"), format!("127.0.0.1:{pc}"));
    let _v0 = spawn(&["validator", "--listen", &v0, "--key", "v0"], &env, &tmp.join("v0.log"));
    let _v1 = spawn(&["validator", "--listen", &v1, "--key", "v1"], &env, &tmp.join("v1.log"));
    let vs = format!("{v0},{v1}");
    let _c = spawn(&["controller", "--listen", &ctl, "--validators", &vs, "--lease-ms", "1000"], &env, &tmp.join("ctl.log"));
    let authority = kf.authority_signer().unwrap();
    let t0 = Instant::now();
    while call(&ctl, ControlRequest::Status, &authority).await.is_none() {
        assert!(t0.elapsed() < Duration::from_secs(30), "controller did not start");
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    let core = core_store().display().to_string();
    // w0 takes the job and holds it for a minute before proving.
    let mut w0 = spawn(&["worker", "--name", "w0", "--controller", &ctl, "--p1-store", &core, "--hold-ms", "60000"], &env, &tmp.join("w0.log"));
    tokio::time::sleep(Duration::from_millis(500)).await;
    let r = call(&ctl, ControlRequest::SubmitWork { request: "procs/t".into(), target: "F04.cons_inj".into(), memory_mb: 1024 }, &authority).await;
    assert_eq!(r, Some(ControlResponse::Queued));
    let store = Store::open(&StoreConfig::from_env(&dep).unwrap(), kf.ring(), Faults::none()).unwrap();
    let (w0id, _) = kf.workspace("w0").unwrap();
    let (w1id, _) = kf.workspace("w1").unwrap();
    let t = Name::parse("F04.cons_inj");
    let t0 = Instant::now();
    let e0 = loop {
        if let Some(rec) = store.target(&t).await.unwrap() {
            if rec.owner == w0id {
                break rec.epoch;
            }
        }
        assert!(t0.elapsed() < Duration::from_secs(30), "w0 never took the job");
        tokio::time::sleep(Duration::from_millis(100)).await;
    };
    // Kill w0 mid-job, then start w1.
    w0.0.kill().unwrap();
    w0.0.wait().unwrap();
    let _w1 = spawn(&["worker", "--name", "w1", "--controller", &ctl, "--p1-store", &core], &env, &tmp.join("w1.log"));
    let t0 = Instant::now();
    let rec = loop {
        let rec = store.target(&t).await.unwrap().unwrap();
        if rec.head.is_some() {
            break rec;
        }
        assert!(t0.elapsed() < Duration::from_secs(120), "target never published; logs in {}", tmp.display());
        tokio::time::sleep(Duration::from_millis(200)).await;
    };
    assert_eq!(rec.owner, w1id);
    assert!(rec.epoch > e0);
    let rev = store.revision(&rec.head.unwrap()).await.unwrap().unwrap();
    assert_eq!(rev.workspace, w1id);
    let a = audit::audit(&store).await.unwrap();
    a.assert_ok();
    assert_eq!(a.counts["markers"], 4, "the target and its three dependencies");
}
