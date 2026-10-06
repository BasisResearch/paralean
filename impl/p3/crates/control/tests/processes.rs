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

async fn call(addr: &str, req: ControlRequest) -> Option<ControlResponse> {
    rpc::call(addr, &req, Duration::from_secs(30)).await.ok()
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
    let t0 = Instant::now();
    while call(&ctl, ControlRequest::Status).await.is_none() {
        assert!(t0.elapsed() < Duration::from_secs(30), "controller did not start");
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    let core = core_store().display().to_string();
    // w0 takes the job and holds it for a minute before proving.
    let mut w0 = spawn(&["worker", "--name", "w0", "--controller", &ctl, "--p1-store", &core, "--hold-ms", "60000"], &env, &tmp.join("w0.log"));
    tokio::time::sleep(Duration::from_millis(500)).await;
    let r = call(&ctl, ControlRequest::SubmitWork { request: "procs/t".into(), target: "F04.cons_inj".into(), memory_mb: 1024 }).await;
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
