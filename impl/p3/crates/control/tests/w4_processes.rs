//! Real controller processes with opposing realtime skew and SIGSTOP/SIGCONT.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;

use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};
use common::{deployment, scratch};
use paralean_control::controller::{ControlRequest, ControlResponse};
use paralean_control::durable::Durable;
use paralean_store::*;
use paralean_validator_api::rpc;

struct Process(Child);
impl Drop for Process {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

async fn status(addr: &str, signer: &Signer) -> Option<serde_json::Value> {
    match rpc::call_authenticated(addr, &ControlRequest::Status, signer, &signer.public(), Duration::from_secs(1)).await {
        Ok(ControlResponse::Status { status }) => Some(status),
        _ => None,
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn opposing_wall_clock_skew_and_paused_leader_preserve_handover() {
    let dir = scratch("w4-skew");
    let source = dir.join("clock.c");
    let preload = dir.join("clock.so");
    std::fs::write(&source, r#"
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdlib.h>
#include <time.h>
int clock_gettime(clockid_t id, struct timespec *ts) {
    static int (*real_clock)(clockid_t, struct timespec*);
    if (!real_clock) real_clock = dlsym(RTLD_NEXT, "clock_gettime");
    int result = real_clock(id, ts);
    if (!result && id == CLOCK_REALTIME) {
        const char *offset = getenv("W4_REALTIME_SKEW");
        if (offset) ts->tv_sec += strtoll(offset, NULL, 10);
    }
    return result;
}
"#).unwrap();
    assert!(Command::new("cc").args(["-shared", "-fPIC", "-o"]).arg(&preload).arg(&source).arg("-ldl").status().unwrap().success());
    // Establish that the injected shim changes CLOCK_REALTIME by 100 days.
    let date = |offset: &str| -> i64 {
        let out = Command::new("date").arg("+%s").env("LD_PRELOAD", &preload)
            .env("W4_REALTIME_SKEW", offset).output().unwrap();
        assert!(out.status.success());
        String::from_utf8(out.stdout).unwrap().trim().parse().unwrap()
    };
    assert!((date("8640000") - date("-8640000") - 17_280_000).abs() <= 2);

    let dep = deployment("w4-skew-process");
    let keys = KeyFile::demo(2);
    let keypath = dir.join("keys.json");
    std::fs::write(&keypath, serde_json::to_vec(&keys).unwrap()).unwrap();
    let authority = keys.authority_signer().unwrap();
    let store = Store::open(&StoreConfig::from_env(&dep).unwrap(), keys.ring(), Faults::none()).unwrap();
    let ports: Vec<_> = (0..3).map(|_| std::net::TcpListener::bind("127.0.0.1:0").unwrap()).collect();
    let addrs: Vec<_> = ports.iter().map(|p| p.local_addr().unwrap().to_string()).collect();
    drop(ports);
    let spawn = |index: usize, shard: &str, offset: &str| {
        let log = std::fs::File::create(dir.join(format!("controller-{index}.log"))).unwrap();
        Process(Command::new(env!("CARGO_BIN_EXE_paralean-p3"))
            .args(["controller", "--listen", &addrs[index], "--validators", "127.0.0.1:1",
                "--lease-ms", "1200", "--shard", shard, "--shards", "2"])
            .env("PARALEAN_KEYS", &keypath).env("PARALEAN_DEPLOYMENT", &dep)
            // No validation is requested; this file is only hashed for checker identity.
            .env("PARALEAN_BIN", "/bin/true")
            .env("ELAN_TOOLCHAIN", "leanprover/lean4-nightly:nightly-2026-10-03")
            .env("LD_PRELOAD", &preload).env("W4_REALTIME_SKEW", offset)
            .stdout(log.try_clone().unwrap()).stderr(log).stdin(Stdio::null()).spawn().unwrap())
    };
    let old = spawn(0, "0", "8640000");
    let other = spawn(2, "1", "-8640000");
    for index in [0, 2] {
        let deadline = Instant::now() + Duration::from_secs(20);
        loop {
            if status(&addrs[index], &authority).await.is_some_and(|s| s["leader"] == true) { break }
            assert!(Instant::now() < deadline, "controller startup failed; logs: {}", dir.display());
            tokio::time::sleep(Duration::from_millis(50)).await;
        }
    }
    let target = (0..100).map(|n| Name::parse(&format!("Skew.target{n}")))
        .find(|name| Durable::hash_shard(name, 2) == 0).unwrap();
    let req = ControlRequest::SubmitWork { request: "skew/pending".into(), target: target.to_string(), memory_mb: 1 };
    let result: ControlResponse = rpc::call_authenticated(&addrs[0], &req, &authority, &authority.public(), Duration::from_secs(3)).await.unwrap();
    assert_eq!(result, ControlResponse::Queued);
    let old_term = status(&addrs[0], &authority).await.unwrap()["term"].as_u64().unwrap();
    let standby = spawn(1, "0", "-8640000");
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if status(&addrs[1], &authority).await.is_some_and(|s| s["leader"] == false) { break }
        assert!(Instant::now() < deadline, "skewed standby stole unexpired leadership");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    unsafe { assert_eq!(libc::kill(old.0.id() as i32, libc::SIGSTOP), 0); }
    let failover = Instant::now();
    let recovered = loop {
        if let Some(s) = status(&addrs[1], &authority).await {
            if s["leader"] == true { break s }
        }
        assert!(failover.elapsed() < Duration::from_secs(10), "paused leader prevented takeover");
        tokio::time::sleep(Duration::from_millis(50)).await;
    };
    assert!(recovered["term"].as_u64().unwrap() > old_term);
    assert_eq!(recovered["work"].as_array().unwrap().len(), 1);
    assert_eq!(recovered["work"][0]["request"], "skew/pending");
    assert_eq!(status(&addrs[2], &authority).await.unwrap()["leader"], true);
    unsafe { assert_eq!(libc::kill(old.0.id() as i32, libc::SIGCONT), 0); }
    assert_eq!(status(&addrs[0], &authority).await.unwrap()["leader"], false);
    assert_eq!(status(&addrs[1], &authority).await.unwrap()["work"].as_array().unwrap().len(), 1);
    // The authoritative target remains unassigned: recovery preserved queued work.
    assert!(store.target(&target).await.unwrap().is_none());
    println!("W4 realtime skew ±100 days, SIGSTOP takeover: {:.3}s; queued request preserved; other shard stayed leader", failover.elapsed().as_secs_f64());
    drop((old, standby, other));
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("opposing_wall_clock_skew_and_paused_leader_preserve_handover", || { opposing_wall_clock_skew_and_paused_leader_preserve_handover(); Ok(()) }),
    ]);
}
