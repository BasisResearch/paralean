//! Concurrent writers in separate processes against the real services: several
//! `paralean-p2 stress` workers race on shared target names, the fence and the catalogue,
//! with injected unknown commit results, S3 timeouts and corrupt reads; some abort at random
//! crash points and the test SIGKILLs others mid-flight. Afterwards the audit, discovery and
//! catalogue recovery must satisfy store.md's invariants.

use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use paralean_store::recovery::{discover, recover_catalog};
use paralean_store::*;

fn deployment() -> String {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    format!("t-multiproc-{}-{}", std::process::id(), nanos % 1_000_000_000)
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn concurrent_writers_multi_process() {
    let dep = deployment();
    let cfg = StoreConfig::from_env(&dep).expect("run through scripts/test.sh");
    let kf = KeyFile::demo(6);
    let keys = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{dep}-keys.json"));
    std::fs::write(&keys, serde_json::to_string(&kf).unwrap()).unwrap();
    let bin = env!("CARGO_BIN_EXE_paralean-p2");

    let mut children = Vec::new();
    for round in 0..2u64 {
        for wi in 0..6usize {
            let seed = 1000 * round + wi as u64 + 1;
            // Workers 4 and 5 also crash at random points (abort); all see random faults.
            let crash = if wi >= 4 { "0.02" } else { "0" };
            let child = Command::new(bin)
                .args(["stress", "--worker", &wi.to_string(), "--ops", "40", "--seed", &seed.to_string(), "--crash-p", crash, "--fault-p", "0.05"])
                .env("PARALEAN_DEPLOYMENT", &dep)
                .env("PARALEAN_KEYS", &keys)
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .unwrap();
            children.push((round, wi, child));
        }
    }
    // SIGKILL two workers mid-flight.
    tokio::time::sleep(Duration::from_millis(1500)).await;
    for (_, wi, c) in children.iter_mut() {
        if *wi == 3 {
            let _ = c.kill();
        }
    }
    let start = Instant::now();
    let mut crashed = 0;
    let mut killed = 0;
    let mut ok = 0;
    for (round, wi, c) in children {
        let out = c.wait_with_output().unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        match out.status.code() {
            Some(0) => {
                ok += 1;
                eprintln!("round {round} {}", stdout.trim());
            }
            Some(3) | Some(2) => panic!("worker {wi} failed: {stderr}"),
            None => {
                if stderr.contains("injected crash") {
                    crashed += 1;
                } else {
                    killed += 1;
                }
            }
            Some(other) => panic!("worker {wi} exit {other}: {stderr}"),
        }
    }
    eprintln!("workers: {ok} completed, {crashed} aborted at injected crash points, {killed} killed; {:?}", start.elapsed());
    assert!(ok >= 6);

    let store = Store::open(&cfg, kf.ring(), Faults::none()).unwrap();
    let r = audit::audit(&store).await.unwrap();
    eprintln!("audit counts {:?}", r.counts);
    r.assert_ok();
    assert!(r.uncertified_markers.is_empty(), "published implies certified");
    let d = discover(&store).await.unwrap();
    for i in 0..3 {
        let t = Name::parse(&format!("Stress.t{i}"));
        if let Some(rec) = store.target(&t).await.unwrap() {
            let heads = d.heads.get(&t).cloned().unwrap_or_default();
            assert!(heads.len() <= 1, "{t}: {heads:?}");
            assert_eq!(heads.first().copied(), rec.head, "{t}");
        }
    }
    // Recovery for every workspace selects a fenced record or none, never a conflict
    // between records of one writer's chain.
    for i in 0..6 {
        let (id, _) = kf.workspace(&format!("w{i}")).unwrap();
        let rec = recover_catalog(&store, id).await.unwrap();
        if let Some(c) = rec.selected {
            let r = store.record(&c).await.unwrap().unwrap();
            assert!(store.valid_rcert(&c, &r.body).await.unwrap().is_some());
        }
    }
}
