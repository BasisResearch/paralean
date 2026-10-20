//! Sandbox overhead measurement (ignored by default):
//!   cargo test -p paralean-control --test overhead -- --ignored --nocapture
//! Needs PARALEAN_BIN (and, for warm numbers, PARALEAN_P3_WARM_BIN). It builds its own P1
//! fixtures and reports cold direct vs sandboxed (cgroup on/off), the cgroup scope's
//! startup cost, and warm-direct reuse vs sandboxed single-use.

use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use paralean_control::checker::{self, CheckerConfig, WarmPool};
use tokio::sync::watch;

fn tmp(tag: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("paralean-overhead-{tag}-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    root
}

fn capture(tag: &str, files: &[&str], want_member: &str, drop_mathlib: bool) -> (PathBuf, String) {
    let bin = std::env::var("PARALEAN_BIN").unwrap();
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../..").canonicalize().unwrap();
    let root = tmp(tag);
    let store = root.join("store");
    for f in files {
        let mut cmd = std::process::Command::new(&bin);
        cmd.args(["capture", "--store"]).arg(&store).args(["--ws", "A", "--root"]).arg(repo.join("corpus/fixtures")).arg(f);
        if drop_mathlib { cmd.env_remove("PARALEAN_MATHLIB"); }
        let out = cmd.output().unwrap();
        assert!(out.status.success(), "capture {f}: {}", String::from_utf8_lossy(&out.stderr));
    }
    let _ = std::fs::remove_dir_all(store.join("materialized"));
    let mut decl = None;
    for e in std::fs::read_dir(store.join("meta")).unwrap() {
        let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(e.unwrap().path()).unwrap()).unwrap();
        let declares = meta["members"].as_array().map(|ms| ms.iter().any(|m| {
            m.get("name").and_then(|n| n.as_array()).map(|p|
                p.iter().filter_map(|x| x.as_str()).collect::<Vec<_>>().join(".") == want_member).unwrap_or(false)
        })).unwrap_or(false);
        if declares { decl = Some(meta["declId"].as_str().unwrap().to_string()); }
    }
    (store, decl.expect("decl"))
}

fn all_gids(store: &Path) -> Vec<String> {
    std::fs::read_dir(store.join("meta")).unwrap().map(|e|
        e.unwrap().file_name().to_str().unwrap().trim_end_matches(".json").to_string()).collect()
}

fn pct(mut v: Vec<f64>, p: f64) -> f64 {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let i = ((v.len() as f64) * p).ceil() as usize;
    v[i.saturating_sub(1).min(v.len() - 1)]
}

fn copy_tree(src: &Path, dst: &Path) {
    std::fs::create_dir_all(dst).unwrap();
    for e in std::fs::read_dir(src).unwrap() {
        let e = e.unwrap();
        let (from, to) = (e.path(), dst.join(e.file_name()));
        if e.file_type().unwrap().is_dir() { copy_tree(&from, &to); } else { std::fs::copy(&from, &to).unwrap(); }
    }
}

async fn cold(cfg: &CheckerConfig, store: &Path, gids: &[String], decl: &str) -> f64 {
    // Production gives every job a fresh scratch store, so no materialize cache survives
    // between jobs. Copy the store fresh each run (dropping any cached `materialized`) so
    // the direct and sandboxed numbers are comparable; the sandbox always builds in a
    // fresh tmpfs anyway.
    let scratch = tmp("run");
    let run_store = scratch.join("store");
    copy_tree(store, &run_store);
    let _ = std::fs::remove_dir_all(run_store.join("materialized"));
    let (_tx, cancel) = watch::channel(false);
    let t = Instant::now();
    let out = checker::run(cfg, &run_store, gids, decl, &[], Duration::from_secs(120), 2048, cancel).await.unwrap();
    assert!(out.ok, "rejected: {:?}", out.diags);
    let ms = t.elapsed().as_secs_f64() * 1000.0;
    let _ = std::fs::remove_dir_all(&scratch);
    ms
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore]
async fn measure_sandbox_overhead() {
    let bin = match std::env::var("PARALEAN_BIN") { Ok(b) => b, Err(_) => { eprintln!("skip: PARALEAN_BIN not set"); return; } };
    const N: usize = 12;

    let fixtures = [
        ("plain", capture("plain", &["Fixtures/F01Theorem.lean"], "F01.two_eq", false)),
        ("initializer", capture("init", &["Fixtures/F13InitDecl.lean", "Fixtures/F13InitUse.lean"], "f13Counter", true)),
    ];

    println!("\n=== cold check latency (ms), {N} runs each ===");
    println!("{:<12} {:>10} {:>8} {:>8} {:>8}", "fixture", "mode", "p50", "p90", "min");
    for (name, (store, decl)) in &fixtures {
        let gids = all_gids(store);
        let base = CheckerConfig { default_memory_mb: 4096, ..CheckerConfig::sandboxed(PathBuf::from(&bin), "bench") };
        for (label, sandbox, cgroup) in [("direct", false, false), ("sandbox+cg", true, true), ("sandbox-nocg", true, false)] {
            let mut cfg = base.clone();
            cfg.sandbox = sandbox; cfg.cgroup = cgroup;
            if *name == "initializer" { cfg.env.retain(|(k, _)| k != "PARALEAN_MATHLIB"); }
            // Initializer runs each do a full stock build (~seconds); fewer samples suffice.
            let runs = if *name == "initializer" { 10 } else { N };
            let mut ts = Vec::new();
            for _ in 0..runs { ts.push(cold(&cfg, store, &gids, decl).await); }
            println!("{:<12} {:>10} {:>8.0} {:>8.0} {:>8.0}", name, label,
                pct(ts.clone(), 0.5), pct(ts.clone(), 0.9), pct(ts, 0.0));
        }
    }

    // cgroup scope startup cost: a trivial sandboxed checker with cgroup on vs off.
    let shell = tmp("scope");
    let script = shell.join("noop.py");
    std::fs::write(&script, "#!/usr/bin/env python3\nimport json\nprint('CHECK ' + json.dumps({'ok': True}), flush=True)\n").unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o700)).unwrap();
    println!("\n=== scope startup cost (ms), trivial checker, {N} runs ===");
    for (label, cgroup) in [("sandbox+cg", true), ("sandbox-nocg", false)] {
        let cfg = CheckerConfig { default_memory_mb: 256, cgroup, ..CheckerConfig::sandboxed(script.clone(), "bench") };
        let mut ts = Vec::new();
        for _ in 0..N {
            let (_tx, cancel) = watch::channel(false);
            let t = Instant::now();
            let _ = checker::run(&cfg, &shell, &["x".into()], "x", &[], Duration::from_secs(10), 256, cancel).await.unwrap();
            ts.push(t.elapsed().as_secs_f64() * 1000.0);
        }
        println!("{:<14} p50={:>6.0} p90={:>6.0}", label, pct(ts.clone(), 0.5), pct(ts, 0.9));
    }

    // Warm reuse (unsandboxed) vs sandboxed single-use, on the plain fixture.
    if let Ok(warm) = std::env::var("PARALEAN_P3_WARM_BIN") {
        let (store, decl) = &fixtures[0].1;
        let gids = all_gids(store);
        let mut base = CheckerConfig { default_memory_mb: 4096, ..CheckerConfig::sandboxed(PathBuf::from(&bin), "bench") };
        base.env.push(("PARALEAN_P3_WARM_BIN".into(), warm));
        println!("\n=== warm path latency (ms), plain fixture ===");
        // Unsandboxed warm pool: first run is a cold spawn, the rest reuse one process.
        {
            let mut cfg = base.clone(); cfg.sandbox = false;
            let pool = WarmPool::default();
            let mut first = 0.0; let mut reuse = Vec::new();
            for i in 0..N {
                let (_tx, cancel) = watch::channel(false);
                let t = Instant::now();
                let out = pool.run(&cfg, store, &gids, decl, &[], Duration::from_secs(120), 2048, cancel).await.unwrap();
                assert!(out.ok);
                let ms = t.elapsed().as_secs_f64() * 1000.0;
                if i == 0 { first = ms; } else { reuse.push(ms); }
            }
            println!("{:<18} first_spawn={:>6.0}  reuse p50={:>6.0} p90={:>6.0}  spawned={}",
                "warm-direct", first, pct(reuse.clone(), 0.5), pct(reuse, 0.9),
                pool.spawned.load(std::sync::atomic::Ordering::SeqCst));
        }
        // Sandboxed warm pool: every run spawns a fresh single-use process.
        {
            let cfg = base.clone();
            let pool = WarmPool::default();
            let mut ts = Vec::new();
            for _ in 0..N {
                let (_tx, cancel) = watch::channel(false);
                let t = Instant::now();
                let out = pool.run(&cfg, store, &gids, decl, &[], Duration::from_secs(120), 2048, cancel).await.unwrap();
                assert!(out.ok);
                ts.push(t.elapsed().as_secs_f64() * 1000.0);
            }
            println!("{:<18} single-use p50={:>6.0} p90={:>6.0}  spawned={} (one per job)",
                "warm-sandbox", pct(ts.clone(), 0.5), pct(ts, 0.9),
                pool.spawned.load(std::sync::atomic::Ordering::SeqCst));
        }
    } else {
        println!("\n(warm measurements skipped: PARALEAN_P3_WARM_BIN not set)");
    }

    println!();
}
