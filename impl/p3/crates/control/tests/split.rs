//! W2-13: the validator's verdict comes from `kernel-check`, a process that elaborates no
//! capsule, not from `source-check`, the process that elaborates them. A stand-in for a
//! compromised frontend prints a forged acceptance and forged evidence for every group; the
//! real kernel checker must still reject every negative fixture (sorry, a new axiom, a
//! kernel-skipped ill-typed proof, `native_decide`) and still accept a genuine group.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use paralean_control::checker::{self, CheckerConfig};
use tokio::sync::watch;

/// Forges for every command but `kernel-check`, which it hands to the real binary.
const FORGING_FRONTEND: &str = r#"#!/bin/sh
if [ "$1" = kernel-check ]; then exec "$PARALEAN_REAL_BIN" "$@"; fi
exec python3 - "$@" <<'PY'
import json, os, sys
args = sys.argv[1:]
store = args[args.index('--store') + 1]
groups = [{'gid': f[:-5], 'sourceOk': True, 'diags': [], 'realized': []}
          for f in os.listdir(os.path.join(store, 'meta'))]
print('CHECK ' + json.dumps({'ok': True, 'axioms': [], 'targetOk': True, 'diags': []}), flush=True)
print('EVIDENCE ' + json.dumps({'groups': groups, 'diags': []}), flush=True)
PY
"#;

fn copy_store(from: &Path, into: &Path) -> PathBuf {
    for d in ["meta", "objects", "files"] {
        std::fs::create_dir_all(into.join(d)).unwrap();
        if let Ok(entries) = std::fs::read_dir(from.join(d)) {
            for e in entries {
                let e = e.unwrap();
                if e.file_type().unwrap().is_file() {
                    std::fs::copy(e.path(), into.join(d).join(e.file_name())).unwrap();
                }
            }
        }
    }
    into.to_path_buf()
}

/// (package ID, declaration ID) of every group in `store`.
fn groups(store: &Path) -> Vec<(String, String)> {
    let mut out: Vec<(String, String)> = std::fs::read_dir(store.join("meta")).unwrap().map(|e| {
        let e = e.unwrap();
        let pid = e.file_name().to_string_lossy().trim_end_matches(".json").to_string();
        let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(e.path()).unwrap()).unwrap();
        (pid, meta["declId"].as_str().unwrap().to_string())
    }).collect();
    out.sort();
    out
}

fn forging_config(root: &Path) -> CheckerConfig {
    let real = CheckerConfig::from_env().expect("checker config (PARALEAN_BIN)");
    let wrapper = root.join("forging-frontend.sh");
    std::fs::write(&wrapper, FORGING_FRONTEND).unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o700)).unwrap();
    let mut env = real.env.clone();
    env.push(("PARALEAN_REAL_BIN".into(), real.bin.display().to_string()));
    // The provenance of the verdict, not containment (tests/sandbox.rs), is under test; the
    // stand-in execs the real binary by its host path.
    CheckerConfig { bin: wrapper, env, sandbox: false, cgroup: false, ..real }
}

async fn check(cfg: &CheckerConfig, store: &Path, decl: &str) -> checker::CheckOutcome {
    let gids: Vec<String> = groups(store).into_iter().map(|(p, _)| p).collect();
    let (_tx, cancel) = watch::channel(false);
    checker::run(cfg, store, &gids, decl, &[], Duration::from_secs(300), 4096, cancel).await
        .unwrap_or_else(|e| panic!("no verdict for {decl}: {e}"))
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn forged_frontend_acceptance_cannot_pass_the_kernel_check() {
    let root = common::scratch("split-forged");
    let cfg = forging_config(&root);
    let negative = common::negative_store(&root.join("negative"));
    let negatives = groups(&negative);
    assert!(negatives.len() >= 4, "negative fixtures missing");
    for (pid, decl) in &negatives {
        let out = check(&cfg, &negative, decl).await;
        assert!(!out.ok, "forged frontend acceptance of negative group {pid} passed: {:?}", out.diags);
    }
    // A genuine group passes the same forged frontend: the kernel check, not the frontend,
    // decides, and accepts valid stored terms.
    let core = copy_store(&common::core_store(), &root.join("core"));
    let (pid, decl) = groups(&core).into_iter().find(|(pid, _)| {
        let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(core.join("meta").join(format!("{pid}.json"))).unwrap()).unwrap();
        meta["capsule"]["file"].as_str() == Some("Fixtures/F01Theorem.lean")
    }).expect("an F01 group");
    let out = check(&cfg, &core, &decl).await;
    assert!(out.ok, "genuine group {pid} rejected: {:?}", out.diags);
    std::fs::remove_dir_all(&root).unwrap();
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("forged_frontend_acceptance_cannot_pass_the_kernel_check", || { forged_frontend_acceptance_cannot_pass_the_kernel_check(); Ok(()) }),
    ]);
}
