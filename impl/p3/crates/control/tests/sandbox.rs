//! Execute a stand-in checker inside the same OS sandbox as Lean. Its attempted
//! side effects are observations made by the untrusted process itself.

use std::os::unix::fs::PermissionsExt;
use std::time::Duration;

use paralean_control::checker::{self, CheckerConfig, NoVerdict};
use tokio::sync::watch;

fn require_lean() {
    let output = std::process::Command::new("lean").arg("--print-prefix").output()
        .expect("Lean must be installed for sandbox security tests");
    assert!(output.status.success(), "set ELAN_TOOLCHAIN to the installed pinned Lean toolchain: {}",
        String::from_utf8_lossy(&output.stderr));
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn sandbox_configuration_enforces_kernel_limits() {
    require_lean();
    let root = std::env::temp_dir().join(format!("paralean-sandbox-config-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    let script = root.join("configuration.py");
    std::fs::write(&script, r#"#!/usr/bin/env python3
import json, os, resource
expected = [(resource.RLIMIT_AS, 16 << 30), (resource.RLIMIT_FSIZE, 512 << 20),
            (resource.RLIMIT_NOFILE, 256), (resource.RLIMIT_CORE, 0),
            (resource.RLIMIT_NPROC, 64), (resource.RLIMIT_CPU, 12)]
errors = [str(key) for key, value in expected if resource.getrlimit(key) != (value, value)]
if any(k in os.environ for k in ['PARALEAN_KEYS', 'PARALEAN_S3_SECRET_KEY', 'PARALEAN_FDB_CLUSTER']):
    errors.append('credential environment')
print('CHECK ' + json.dumps({'ok': not errors, 'diags': errors}), flush=True)
"#).unwrap();
    std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o700)).unwrap();
    let cfg = CheckerConfig { bin: script, mode: "stock".into(), lean_githash: "test".into(),
        env: vec![], default_memory_mb: 256, sandbox: true };
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 256, cancel).await.unwrap();
    assert!(out.ok, "sandbox configuration: {:?}", out.diags);
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_cannot_read_secrets_write_outside_or_use_network() {
    require_lean();
    let root = std::env::temp_dir().join(format!("paralean-sandbox-{}-{}", std::process::id(), rand::random::<u64>()));
    let store = root.join("store");
    std::fs::create_dir_all(&store).unwrap();
    let secret = root.join("validator.key");
    let outside = root.join("outside");
    std::fs::write(&secret, b"secret validator key").unwrap();
    let script = root.join("malicious.py");
    let source = format!(r#"#!/usr/bin/env python3
import json, socket
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
import os
try:
    os.setsid()
    blocked.append('setsid escaped')
except OSError:
    pass
scratch = '/work' if os.path.isdir('/work') else {store:?}
open(os.path.join(scratch, 'legitimate'), 'w').write('okay')
print('CHECK ' + json.dumps({{'ok': not blocked, 'diags': blocked}}), flush=True)
"#, secret = secret.display().to_string(), outside = outside.display().to_string(), store = store.display().to_string());
    std::fs::write(&script, source).unwrap();
    let mut perms = std::fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o700);
    std::fs::set_permissions(&script, perms).unwrap();
    let cfg = CheckerConfig { bin: script, mode: "stock".into(), lean_githash: "test".into(),
        env: vec![], default_memory_mb: 256, sandbox: true };
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
    let root = std::env::temp_dir().join(format!("paralean-sandbox-cpu-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    let script = root.join("busy.py");
    std::fs::write(&script, "#!/usr/bin/env python3\nimport time, json\nstart=time.monotonic()\nwhile time.monotonic()-start < 1: pass\nprint('CHECK ' + json.dumps({'ok': True}), flush=True)\n").unwrap();
    let mut perms = std::fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o700); std::fs::set_permissions(&script, perms).unwrap();
    let cfg = CheckerConfig { bin: script, mode: "stock".into(), lean_githash: "test".into(),
        env: vec![], default_memory_mb: 256, sandbox: true };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_millis(300), 256, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Timeout)), "busy checker: {result:?}");
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_disk_budget_rejects_even_successful_exit() {
    require_lean();
    let root = std::env::temp_dir().join(format!("paralean-sandbox-disk-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    let script = root.join("disk.py");
    let source = format!("#!/usr/bin/env python3\nimport json, os\nscratch = '/work' if os.path.isdir('/work') else {root:?}\ntry:\n    with open(os.path.join(scratch, 'large'), 'wb') as f:\n        for _ in range(300): f.write(b'x' * (1 << 20))\n    ok = True\nexcept OSError:\n    ok = False\nprint('CHECK ' + json.dumps({{'ok': ok}}), flush=True)\n", root = root.display().to_string());
    std::fs::write(&script, source).unwrap();
    let mut perms = std::fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o700); std::fs::set_permissions(&script, perms).unwrap();
    let cfg = CheckerConfig { bin: script, mode: "stock".into(), lean_githash: "test".into(),
        env: vec![], default_memory_mb: 256, sandbox: true };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(10), 256, cancel).await;
    std::fs::remove_dir_all(&root).unwrap();
    assert!(matches!(&result, Ok(o) if !o.ok) || matches!(&result, Err(NoVerdict::Disk)), "oversized scratch: {result:?}");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_memory_budget_kills_allocation() {
    require_lean();
    let root = std::env::temp_dir().join(format!("paralean-sandbox-memory-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    let script = root.join("memory.py");
    std::fs::write(&script, "#!/usr/bin/env python3\nimport time\nx = bytearray(128 << 20)\nwhile True: time.sleep(1)\n").unwrap();
    let mut perms = std::fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o700); std::fs::set_permissions(&script, perms).unwrap();
    let cfg = CheckerConfig { bin: script, mode: "stock".into(), lean_githash: "test".into(),
        env: vec![], default_memory_mb: 64, sandbox: true };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(5), 64, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Memory { .. })), "oversized memory: {result:?}");
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn checker_process_count_is_hard_limited() {
    require_lean();
    let root = std::env::temp_dir().join(format!("paralean-sandbox-fork-{}-{}", std::process::id(), rand::random::<u64>()));
    std::fs::create_dir_all(&root).unwrap();
    let script = root.join("fork.py");
    std::fs::write(&script, "#!/usr/bin/env python3\nimport json, subprocess\nchildren=[]\nblocked=False\nfor _ in range(80):\n    try: children.append(subprocess.Popen(['/bin/sleep','1']))\n    except OSError:\n        blocked=True\n        break\nprint('CHECK ' + json.dumps({'ok': blocked}), flush=True)\n").unwrap();
    let mut perms = std::fs::metadata(&script).unwrap().permissions();
    perms.set_mode(0o700); std::fs::set_permissions(&script, perms).unwrap();
    let cfg = CheckerConfig { bin: script, mode: "stock".into(), lean_githash: "test".into(),
        env: vec![], default_memory_mb: 512, sandbox: true };
    let (_tx, cancel) = watch::channel(false);
    let result = checker::run(&cfg, &root, &["fixture".into()], "fixture", &[], Duration::from_secs(5), 512, cancel).await;
    assert!(matches!(&result, Ok(o) if o.ok), "fork bomb escaped: {result:?}");
    std::fs::remove_dir_all(&root).unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
#[ignore = "requires PARALEAN_W2_REAL_* private P1 fixture"]
async fn real_lean_check_passes_inside_sandbox_when_fixture_is_available() {
    let store = std::env::var("PARALEAN_W2_REAL_STORE").expect("PARALEAN_W2_REAL_STORE");
    let gid = std::env::var("PARALEAN_W2_REAL_GID").expect("PARALEAN_W2_REAL_GID");
    let decl = std::env::var("PARALEAN_W2_REAL_DECL").expect("PARALEAN_W2_REAL_DECL");
    let cfg = CheckerConfig::from_env().unwrap();
    assert!(cfg.sandbox);
    let mut timings = [Vec::new(), Vec::new()];
    for (index, isolated) in [false, true].into_iter().enumerate() {
        let mut run_cfg = cfg.clone();
        run_cfg.sandbox = isolated;
        for _ in 0..5 {
            let (_tx, cancel) = watch::channel(false);
            let start = std::time::Instant::now();
            let out = checker::run(&run_cfg, std::path::Path::new(&store), std::slice::from_ref(&gid), &decl, &[],
                Duration::from_secs(30), 1024, cancel).await.unwrap();
            assert!(out.ok, "real Lean rejected: {:?}", out.diags);
            timings[index].push(start.elapsed().as_millis());
        }
        timings[index].sort_unstable();
    }
    eprintln!("real Lean check p50: direct={}ms sandbox={}ms", timings[0][2], timings[1][2]);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
#[ignore = "requires PARALEAN_W2_INIT_* private initializer fixture"]
async fn real_initializer_materializes_in_private_scratch_when_fixture_is_available() {
    let store = std::env::var("PARALEAN_W2_INIT_STORE").expect("PARALEAN_W2_INIT_STORE");
    let gid = std::env::var("PARALEAN_W2_INIT_GID").expect("PARALEAN_W2_INIT_GID");
    let decl = std::env::var("PARALEAN_W2_INIT_DECL").expect("PARALEAN_W2_INIT_DECL");
    let cfg = CheckerConfig::from_env().unwrap();
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, std::path::Path::new(&store), &[gid], &decl, &[],
        Duration::from_secs(45), 2048, cancel).await.unwrap();
    assert!(out.ok, "initializer check: {:?}", out.diags);
    assert!(!std::path::Path::new(&store).join("materialized").exists(),
        "materialization must remain inside the sandbox tmpfs");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
#[ignore = "requires PARALEAN_BIN and PARALEAN_LIB for a real P1 capture"]
async fn native_lean_tactic_cannot_reach_host_when_fixture_is_available() {
    let root = std::env::temp_dir().join(format!("paralean-native-attack-{}-{}", std::process::id(), rand::random::<u64>()));
    let store = root.join("store");
    std::fs::create_dir_all(&root).unwrap();
    let reserve = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let port = reserve.local_addr().unwrap().port();
    drop(reserve);
    let source = include_str!("fixtures/Attack.lean.in")
        .replace("__ROOT__", &root.display().to_string())
        .replace("__PORT__", &port.to_string());
    std::fs::write(root.join("Attack.lean"), source).unwrap();
    let cfg = CheckerConfig::from_env().unwrap();
    let capture = std::process::Command::new(&cfg.bin)
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
    let (_tx, cancel) = watch::channel(false);
    let out = checker::run(&cfg, &store, &[gid], &decl, &[],
        Duration::from_secs(30), 2048, cancel).await.unwrap();
    assert!(out.ok, "native tactic escaped sandbox: {:?}", out.diags);
    assert!(!root.join("protected/outside").exists());
    assert!(listener.accept().is_err(), "native tactic reached host network");
    std::fs::remove_dir_all(&root).unwrap();
}
