//! Process exit with the FDB client loaded. The FDB C API requires the network thread to be
//! stopped and joined before the process exits; exiting while `fdb_run_network` still runs
//! is undefined behaviour and can crash in the client library's teardown (the class of the
//! p2-rest run-1 stress-worker SIGSEGV). Many short `paralean-p2` processes each open FDB,
//! run a few operations and exit; none may die from a signal.
//! This is a smoke regression, not a detector: with `mutate-no-network-shutdown` (no
//! stop/join) it still passed in W2, because the undefined exit did not crash in practice.

use std::os::unix::process::ExitStatusExt;
use std::process::{Command, Stdio};

fn deployment() -> String {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    format!("t-exit-{}-{}", std::process::id(), nanos % 1_000_000_000)
}

#[test]
fn cli_processes_exit_without_a_signal() {
    std::env::var("PARALEAN_FDB_CLUSTER").expect("run through scripts/test.sh");
    let runs: usize = std::env::var("PARALEAN_EXIT_RUNS").ok().and_then(|s| s.parse().ok()).unwrap_or(400);
    let lanes: usize = std::env::var("PARALEAN_EXIT_LANES").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let dep = deployment();
    let keys = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{dep}-keys.json"));
    let bin = env!("CARGO_BIN_EXE_paralean-p2");
    let st = Command::new(bin).args(["keys", "init", keys.to_str().unwrap(), "--demo", "--workspaces", "6"]).status().unwrap();
    assert!(st.success());
    let mut signalled = Vec::new();
    let mut failed = Vec::new();
    let mut started = 0;
    while started < runs {
        let wave: Vec<_> = (started..runs.min(started + lanes))
            .map(|i| {
                let child = Command::new(bin)
                    .args(["stress", "--worker", &(i % 6).to_string(), "--ops", "2", "--seed", &(i + 1).to_string()])
                    .env("PARALEAN_DEPLOYMENT", &dep)
                    .env("PARALEAN_KEYS", &keys)
                    .stdout(Stdio::null())
                    .stderr(Stdio::piped())
                    .spawn()
                    .unwrap();
                (i, child)
            })
            .collect();
        started += wave.len();
        for (i, child) in wave {
            let out = child.wait_with_output().unwrap();
            if let Some(sig) = out.status.signal() {
                signalled.push((i, sig, String::from_utf8_lossy(&out.stderr).lines().take(3).collect::<Vec<_>>().join(" | ")));
            } else if !out.status.success() {
                failed.push((i, out.status.code(), String::from_utf8_lossy(&out.stderr).into_owned()));
            }
        }
    }
    assert!(signalled.is_empty(), "{} of {runs} CLI processes died from a signal: {signalled:?}", signalled.len());
    assert!(failed.is_empty(), "CLI processes failed: {failed:?}");
}
