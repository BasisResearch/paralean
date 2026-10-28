//! Execute a stand-in checker, and the real `paralean check-group`, inside the production
//! OS sandbox. A stand-in's attempted side effects are observations the untrusted process
//! makes about its own confinement; the real-Lean cases build their own P1 fixtures with
//! `PARALEAN_BIN` and show legitimate checks pass and a hostile package is contained.

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use paralean_control::checker::{self, CheckerConfig, NoVerdict};
use tokio::sync::watch;

fn require_lean() {
    let output = std::process::Command::new("lean").arg("--print-prefix").output()
        .expect("Lean must be installed for sandbox security tests");
    assert!(output.status.success(), "set ELAN_TOOLCHAIN to the installed pinned Lean toolchain: {}",
        String::from_utf8_lossy(&output.stderr));
}

/// Appended to every mock checker: in the `source-check` phase of a split check (W2-13) it
/// also prints the (empty) evidence, so the same body runs in both sandboxed phases.
const EVIDENCE_FOOTER: &str = "\nimport sys as _sys, json as _json\nif len(_sys.argv) > 1 and _sys.argv[1] == 'source-check':\n    print('EVIDENCE ' + _json.dumps({'groups': []}), flush=True)\n";

fn script(root: &Path, name: &str, body: &str) -> PathBuf {
    let p = root.join(name);
    std::fs::write(&p, format!("{body}{EVIDENCE_FOOTER}")).unwrap();
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o700)).unwrap();
    p
}

fn tmp(tag: &str) -> PathBuf {
    // Outside /tmp (the sandbox's own tmpfs), so a host path the checker should not be able
    // to create is not hidden by it whatever TMPDIR is.
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("paralean-sandbox-{tag}-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    root
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sandbox_configuration_enforces_kernel_limits() {
    require_lean();
    let root = tmp("config");
    let s = script(&root, "configuration.py", r#"#!/usr/bin/env python3
import json, os, resource
expected = [(resource.RLIMIT_FSIZE, 128 << 20),
            (resource.RLIMIT_NOFILE, 256), (resource.RLIMIT_CORE, 0),
            (resource.RLIMIT_NPROC, 64), (resource.RLIMIT_CPU, 12)]
import sys
# The trusted kernel-check phase (W2-13) gets what remains of the job's deadline.
if sys.argv[1:2] == ['kernel-check']:
    cpu = resource.getrlimit(resource.RLIMIT_CPU)
    expected = [e for e in expected if e[0] != resource.RLIMIT_CPU]
    errors = [] if cpu[0] == cpu[1] and 0 < cpu[0] <= 12 else ['RLIMIT_CPU']
else:
    errors = []
errors += [str(key) for key, value in expected if resource.getrlimit(key) != (value, value)]
# RLIMIT_AS is a 16 GiB backstop, not the job's memory limit (the cgroup is).
if resource.getrlimit(resource.RLIMIT_AS) != (16 << 30, 16 << 30): errors.append('RLIMIT_AS')
if any(k in os.environ for k in ['PARALEAN_KEYS', 'PARALEAN_S3_SECRET_KEY', 'PARALEAN_FDB_CLUSTER', 'PARALEAN_GARAGE_ADMIN_TOKEN']):
    errors.append('credential environment')
print('CHECK ' + json.dumps({'ok': not errors, 'diags': errors}), flush=True)
"#);
    let cfg = CheckerConfig { default_memory_mb: 256, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 256, cancel).await.unwrap();
    assert!(out.ok, "sandbox configuration: {:?}", out.diags);
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_cannot_read_secrets_write_outside_or_use_network() {
    require_lean();
    let root = tmp("escape");
    let store = root.join("store");
    std::fs::create_dir_all(&store).unwrap();
    let secret = root.join("validator.key");
    let outside = root.join("outside");
    std::fs::write(&secret, b"secret validator key").unwrap();
    let source = format!(r#"#!/usr/bin/env python3
import json, socket, os
blocked = []
try:
    open({secret:?}).read()
    blocked.append('read escaped')
except OSError:
    pass
try:
    open({outside:?}, 'w').write('escaped')
    blocked.append('write escaped')
except OSError:
    pass
try:
    socket.socket()
    blocked.append('socket escaped')
except OSError:
    pass
try:
    os.setsid()
    blocked.append('setsid escaped')
except OSError:
    pass
scratch = '/work' if os.path.isdir('/work') else {store:?}
open(os.path.join(scratch, 'legitimate'), 'w').write('okay')
print('CHECK ' + json.dumps({{'ok': not blocked, 'diags': blocked}}), flush=True)
"#, secret = secret.display().to_string(), outside = outside.display().to_string(), store = store.display().to_string());
    let s = script(&root, "malicious.py", &source);
    let cfg = CheckerConfig { default_memory_mb: 256, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &store, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 256, cancel).await.unwrap();
    assert!(out.ok, "sandbox escaped: {:?}", out.diags);
    assert!(!store.join("legitimate").exists(), "sandbox writes must stay in private tmpfs");
    assert!(!outside.exists());
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_cpu_budget_kills_busy_loop() {
    require_lean();
    let root = tmp("cpu");
    let s = script(&root, "busy.py", "#!/usr/bin/env python3\nimport time, json\nstart=time.monotonic()\nwhile time.monotonic()-start < 1: pass\nprint('CHECK ' + json.dumps({'ok': True}), flush=True)\n");
    let cfg = CheckerConfig { default_memory_mb: 256, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_millis(300), 256, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Timeout)), "busy checker: {result:?}");
    std::fs::remove_dir_all(&root).unwrap();
}

/// The disk limit is the /work tmpfs size (ENOSPC) and RLIMIT_FSIZE, not a host-directory
/// scan: the host input store is read-only and never grows.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_disk_budget_is_tmpfs_enospc_and_rlimit_fsize() {
    require_lean();
    let root = tmp("disk");
    let s = script(&root, "disk.py", r#"#!/usr/bin/env python3
import json, os, signal, resource, errno
scratch = '/work' if os.path.isdir('/work') else os.getcwd()
diags = []
# 1) filling the tmpfs past its --size cap must raise ENOSPC. Each file is well under
#    RLIMIT_FSIZE so it is the tmpfs cap, not the per-file cap, that stops us.
signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
enospc = False
for i in range(32):
    try:
        with open(os.path.join(scratch, 'fill%d' % i), 'wb') as f:
            for _ in range(32): f.write(b'x' * (1 << 20))
            f.flush(); os.fsync(f.fileno())
    except OSError as e:
        enospc = e.errno == errno.ENOSPC
        break
if not enospc: diags.append('tmpfs did not ENOSPC')
for i in range(32):
    try: os.unlink(os.path.join(scratch, 'fill%d' % i))
    except OSError: pass
# 2) a single file past RLIMIT_FSIZE must be refused (SIGXFSZ ignored -> EFBIG), before the
#    tmpfs fills, so the per-file cap is what stops it.
soft, _ = resource.getrlimit(resource.RLIMIT_FSIZE)
if soft >= (1 << 40): diags.append('RLIMIT_FSIZE unset')
try:
    with open(os.path.join(scratch, 'big'), 'wb') as f:
        while True: f.write(b'x' * (1 << 20))
    diags.append('RLIMIT_FSIZE not enforced')
except OSError as e:
    if e.errno != errno.EFBIG: diags.append('fsize errno %d' % e.errno)
    elif os.path.getsize(os.path.join(scratch, 'big')) > soft: diags.append('fsize cap overshot')
try: os.unlink(os.path.join(scratch, 'big'))
except OSError: pass
print('CHECK ' + json.dumps({'ok': not diags, 'diags': diags}), flush=True)
"#);
    let cfg = CheckerConfig { default_memory_mb: 512, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(20), 512, cancel).await;
    std::fs::remove_dir_all(&root).unwrap();
    match result {
        Ok(o) => assert!(o.ok, "disk limits not enforced: {:?}", o.diags),
        other => panic!("disk budget: {other:?}"),
    }
}

/// The cgroup is a hard memory limit: a fast allocator that overshoots the job's limit and
/// exits between RSS polls (printing a forged acceptance) is still stopped, because the
/// scope is OOM-killed mid-burst and that maps to `NoVerdict::Memory`. This is exactly the
/// overshoot the 50 ms RSS poll alone cannot catch.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_memory_cgroup_hard_limit_kills_fast_burst() {
    require_lean();
    let root = tmp("memory-burst");
    // memset ~96 MiB (> the 64 MiB limit) as one fast burst, then exit at once with a forged
    // CHECK. The whole process lives well under a poll interval's worth of resident memory.
    let s = script(&root, "burst.py", "#!/usr/bin/env python3\nimport json, ctypes, mmap\nn = 96 << 20\nbuf = mmap.mmap(-1, n)\nctypes.memset((ctypes.c_char * n).from_buffer(buf), 1, n)\nprint('CHECK ' + json.dumps({'ok': True}), flush=True)\n");
    let cfg = CheckerConfig { default_memory_mb: 64, ..CheckerConfig::sandboxed(s, "test") };
    // Every burst must be stopped. The cgroup's hard limit usually acts first, but the
    // 50 ms resident-set poll sums the group's RSS (shared pages included), so it can see
    // the limit crossed first. Without the cgroup no kill is the cgroup's, so requiring at
    // least one cgroup kill tells the layers apart whatever the host load.
    let mut by_cgroup = 0;
    for attempt in 0..10 {
        let (_tx, cancel) = watch::channel(false);
        let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 64, cancel).await;
        match result {
            Err(NoVerdict::Memory { cgroup, .. }) => by_cgroup += usize::from(cgroup),
            other => panic!("fast burst {attempt} escaped the memory limit: {other:?}"),
        }
    }
    assert!(by_cgroup > 0, "no fast burst was stopped by the cgroup's hard limit");
    std::fs::remove_dir_all(&root).unwrap();
}

/// The RSS poll is the second layer, for hosts without cgroups: with the cgroup disabled, a
/// sustained over-limit resident set is still caught and mapped to `NoVerdict::Memory`.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_memory_rss_poll_catches_sustained_hog_without_cgroup() {
    require_lean();
    let root = tmp("memory-rss");
    let s = script(&root, "hog.py", "#!/usr/bin/env python3\nx = bytearray(256 << 20)\nfor i in range(0, len(x), 4096): x[i] = 1\nimport time\nwhile True: time.sleep(1)\n");
    let cfg = CheckerConfig { default_memory_mb: 64, cgroup: false, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 64, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Memory { .. })), "RSS poll missed a sustained hog: {result:?}");
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_process_count_is_hard_limited() {
    require_lean();
    let root = tmp("fork");
    // 75 is between RLIMIT_NPROC (64) and the scope's TasksMax (96), so prlimit is what must
    // stop the fork bomb; its removal lets all 75 start.
    let s = script(&root, "fork.py", "#!/usr/bin/env python3\nimport json, subprocess\nchildren=[]\nblocked=False\nfor _ in range(75):\n    try: children.append(subprocess.Popen(['/bin/sleep','3']))\n    except OSError:\n        blocked=True\n        break\nprint('CHECK ' + json.dumps({'ok': blocked}), flush=True)\n");
    let cfg = CheckerConfig { default_memory_mb: 512, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 512, cancel).await;
    assert!(matches!(&result, Ok(o) if o.ok), "fork bomb escaped: {result:?}");
    std::fs::remove_dir_all(&root).unwrap();
}

/// io_uring is a well-known seccomp-bypass surface (async file and socket ops that skip the
/// syscalls the filter denies); `io_uring_setup` must be refused with EPERM.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_io_uring_is_blocked() {
    require_lean();
    let root = tmp("io-uring");
    let s = script(&root, "iouring.py", r#"#!/usr/bin/env python3
import ctypes, json, os
libc = ctypes.CDLL(None, use_errno=True)
params = (ctypes.c_byte * 120)()
ctypes.set_errno(0)
r = libc.syscall(425, 1, ctypes.byref(params))  # io_uring_setup(entries=1, params)
e = ctypes.get_errno()
if r >= 0:
    try: os.close(r)
    except OSError: pass
blocked = r < 0 and e == 1  # EPERM from the seccomp filter
print('CHECK ' + json.dumps({'ok': blocked, 'diags': [] if blocked else ['io_uring reachable r=%d errno=%d' % (r, e)]}), flush=True)
"#);
    let cfg = CheckerConfig { default_memory_mb: 256, ..CheckerConfig::sandboxed(s, "test") };
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 256, cancel).await.unwrap();
    assert!(out.ok, "io_uring not blocked: {:?}", out.diags);
    std::fs::remove_dir_all(&root).unwrap();
}

/// A missing Bubblewrap is a sandbox setup failure that yields no verdict; there is never
/// an unsandboxed run of untrusted code.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sandbox_fails_closed_when_bwrap_is_missing() {
    require_lean();
    let root = tmp("fail-closed");
    let marker = root.join("ran");
    let s = script(&root, "witness.py", &format!("#!/usr/bin/env python3\nimport json\nopen({:?}, 'w').write('ran')\nprint('CHECK ' + json.dumps({{'ok': True}}), flush=True)\n", marker.display().to_string()));
    let mut cfg = CheckerConfig { default_memory_mb: 256, ..CheckerConfig::sandboxed(s, "test") };
    cfg.bwrap = PathBuf::from("/nonexistent/bwrap");
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 256, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Crashed(_))), "missing bwrap must fail closed: {result:?}");
    assert!(!marker.exists(), "the checker must not have run outside the sandbox");
    std::fs::remove_dir_all(&root).unwrap();
}

/// Production configuration enables both sandbox layers and is never silently unsandboxed.
#[test]
fn production_config_enables_the_sandbox() {
    if std::env::var_os("PARALEAN_BIN").is_none() { eprintln!("skip: PARALEAN_BIN not set"); return; }
    let cfg = CheckerConfig::from_env().unwrap();
    assert!(cfg.sandbox, "production config must sandbox");
    assert!(cfg.cgroup, "production config must use the cgroup layer unless PARALEAN_CHECKER_CGROUP=off");
    assert_eq!(cfg.bwrap, PathBuf::from("/usr/bin/bwrap"));
}

// ---- Real Lean checks under the sandbox (build their own P1 fixtures) ----

/// Capture `files` (relative to `corpus/fixtures`) into a fresh store, with `extra_env`
/// overriding the capture process environment (e.g. unsetting PARALEAN_MATHLIB). Returns
/// the store path and, for the group declaring `want_member`, its (gid, declId).
fn capture(tag: &str, files: &[&str], want_member: &str, extra_env: &[(&str, Option<&str>)]) -> (PathBuf, String, String) {
    let bin = std::env::var("PARALEAN_BIN").unwrap();
    let repo = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../..").canonicalize().unwrap();
    let root = tmp(tag);
    let store = root.join("store");
    for f in files {
        let mut cmd = std::process::Command::new(&bin);
        cmd.args(["capture", "--store"]).arg(&store)
            .args(["--ws", "A", "--root"]).arg(repo.join("corpus/fixtures")).arg(f);
        for (k, v) in extra_env { match v { Some(v) => { cmd.env(k, v); }, None => { cmd.env_remove(k); } } }
        let out = cmd.output().unwrap();
        assert!(out.status.success(), "capture {f}: {}", String::from_utf8_lossy(&out.stderr));
    }
    let (mut gid, mut decl) = (None, None);
    for e in std::fs::read_dir(store.join("meta")).unwrap() {
        let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(e.unwrap().path()).unwrap()).unwrap();
        let declares = meta["members"].as_array().map(|ms| ms.iter().any(|m| {
            m.get("name").and_then(|n| n.as_array()).map(|parts|
                parts.iter().filter_map(|p| p.as_str()).collect::<Vec<_>>().join(".") == want_member).unwrap_or(false)
        })).unwrap_or(false);
        if declares {
            gid = Some(meta["gid"].as_str().unwrap().to_string());
            decl = Some(meta["declId"].as_str().unwrap().to_string());
        }
    }
    (store, gid.expect("gid for member"), decl.expect("decl for member"))
}

/// All the group IDs of a store, as the checker is given them.
fn all_gids(store: &Path) -> Vec<String> {
    std::fs::read_dir(store.join("meta")).unwrap().map(|e|
        e.unwrap().file_name().to_str().unwrap().trim_end_matches(".json").to_string()).collect()
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn real_plain_theorem_passes_inside_and_outside_the_sandbox() {
    if std::env::var_os("PARALEAN_BIN").is_none() { eprintln!("skip: PARALEAN_BIN not set"); return; }
    require_lean();
    let (store, _gid, decl) = capture("plain", &["Fixtures/F01Theorem.lean"], "F01.two_eq", &[]);
    let gids = all_gids(&store);
    let cfg = CheckerConfig::from_env().unwrap();
    assert!(cfg.sandbox);
    for isolated in [false, true] {
        let mut c = cfg.clone();
        c.sandbox = isolated;
        let (_tx, cancel) = watch::channel(false);
        let out = checker::run(&c, &store, &gids, &decl, &[], Duration::from_secs(60), 2048, cancel).await.unwrap();
        assert!(out.ok, "plain theorem rejected (sandbox={isolated}): {:?}", out.diags);
    }
    std::fs::remove_dir_all(store.parent().unwrap()).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn real_initializer_is_refused_before_materialization() {
    if std::env::var_os("PARALEAN_BIN").is_none() { eprintln!("skip: PARALEAN_BIN not set"); return; }
    require_lean();
    // The export package the initializer group materializes has no Mathlib dependency.
    let (store, _gid, decl) = capture("init", &["Fixtures/F13InitDecl.lean", "Fixtures/F13InitUse.lean"],
        "f13Counter", &[("PARALEAN_MATHLIB", None)]);
    let gids = all_gids(&store);
    // Capture materializes on the host as a cache; remove it so a host directory after the
    // check can only come from the check itself.
    let _ = std::fs::remove_dir_all(store.join("materialized"));
    let mut cfg = CheckerConfig::from_env().unwrap();
    cfg.env.retain(|(k, _)| k != "PARALEAN_MATHLIB");
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &store, &gids, &decl, &[], Duration::from_secs(120), 2048, cancel).await.unwrap();
    // Initializers run arbitrary IO on every importer, so published capsules may not have
    // them (W2 A-28): the check refuses before materializing anything.
    assert!(!out.ok && out.diags.iter().any(|d| d.contains("initializer effects")), "initializer: {:?}", out.diags);
    assert!(!store.join("materialized").exists(), "a refused check materialized on the host");
    std::fs::remove_dir_all(store.parent().unwrap()).unwrap();
}

/// A package whose `run_tac` native tactic tries to read a key, write outside scratch and
/// reach a host TCP listener. Two layers stop it. The publication gate refuses the capsule
/// in `check-group`, so the tactic never runs there. And when the same source is
/// elaborated by real Lean inside the sandbox (as code the gate cannot see would be), the
/// tactic runs and every host effect fails, while its theorem still checks.
#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn native_lean_tactic_cannot_reach_host() {
    if std::env::var_os("PARALEAN_BIN").is_none() { eprintln!("skip: PARALEAN_BIN not set"); return; }
    require_lean();
    let bin = std::env::var("PARALEAN_BIN").unwrap();
    let root = tmp("native-attack");
    let store = root.join("store");
    // A host TCP listener the tactic will try to reach.
    let reserve = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let port = reserve.local_addr().unwrap().port();
    drop(reserve);
    let source = include_str!("fixtures/Attack.lean.in")
        .replace("__ROOT__", &root.display().to_string())
        .replace("__PORT__", &port.to_string());
    std::fs::write(root.join("Attack.lean"), &source).unwrap();
    // Capture runs the tactic on the host; the targets must not exist yet, or capture itself
    // would see them and reject. They are created only for the checks below.
    let capture = std::process::Command::new(&bin).current_dir(&root)
        .args(["capture", "--store"]).arg(&store)
        .args(["--ws", "A", "--root"]).arg(&root).arg("Attack.lean")
        .output().unwrap();
    assert!(capture.status.success(), "capture: {}", String::from_utf8_lossy(&capture.stderr));
    let meta_path = std::fs::read_dir(store.join("meta")).unwrap().next().unwrap().unwrap().path();
    let meta: serde_json::Value = serde_json::from_slice(&std::fs::read(meta_path).unwrap()).unwrap();
    let gid = meta["gid"].as_str().unwrap().to_string();
    let decl = meta["declId"].as_str().unwrap().to_string();
    std::fs::create_dir(root.join("protected")).unwrap();
    std::fs::write(root.join("secret"), "validator key").unwrap();
    let listener = std::net::TcpListener::bind(("127.0.0.1", port)).unwrap();
    listener.set_nonblocking(true).unwrap();
    let cfg = CheckerConfig::from_env().unwrap();
    assert!(cfg.sandbox);
    // Layer 1: the published-capsule check refuses run_tac before elaborating it.
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &store, &[gid], &decl, &[], Duration::from_secs(60), 2048, cancel).await.unwrap();
    assert!(!out.ok && out.diags.iter().any(|d| d.contains("capsule gate")), "gate: {:?}", out.diags);
    // Layer 2: real Lean elaborates the attack inside the same sandbox profile.
    let direct = root.join("direct");
    std::fs::create_dir(&direct).unwrap();
    std::fs::write(direct.join("Attack.lean"), &source).unwrap();
    let wrapper = root.join("lean-attack.sh");
    std::fs::write(&wrapper, r#"#!/bin/sh
# Elaborate the attack in the checker's store directory with the toolchain's own lean,
# in both phases of the split check (W2-13); the frontend phase also prints evidence.
phase="$1"
[ "$phase" = source-check ] && echo 'EVIDENCE {"groups":[]}'
while [ $# -gt 0 ]; do [ "$1" = --store ] && store="$2"; shift; done
cd "$store" || exit 1
if lean Attack.lean > lean.out 2>&1 && [ -f attack-ran ]; then
  echo 'CHECK {"ok": true}'
else
  python3 -c 'import json; print("CHECK " + json.dumps({"ok": False, "diags": [open("lean.out").read()[-500:]]}))'
fi
"#).unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o700)).unwrap();
    let mut lean_cfg = cfg.clone();
    lean_cfg.bin = wrapper;
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&lean_cfg, &direct, &["attack".into()], "attack", &[], Duration::from_secs(60), 2048, cancel).await.unwrap();
    assert!(out.ok, "native tactic escaped the sandbox or did not run: {:?}", out.diags);
    assert!(!root.join("protected/outside").exists());
    assert!(listener.accept().is_err(), "native tactic reached host network");
    std::fs::remove_dir_all(&root).unwrap();
}
