//! A checker's stdout is untrusted: a declaration being checked can print text that
//! looks like a protocol reply. Exercise the framing rules without Lean or a store.

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;
use std::time::Duration;

use paralean_control::checker::{self, CheckerConfig, NoVerdict, WarmPool};
use tokio::sync::watch;

struct FakeChecker {
    dir: PathBuf,
    script: PathBuf,
}

impl FakeChecker {
    fn new(name: &str, source: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("paralean-checker-protocol-{name}-{}-{}",
            std::process::id(), rand::random::<u64>()));
        std::fs::create_dir(&dir).unwrap();
        let script = dir.join("checker.py");
        std::fs::write(&script, format!("#!/usr/bin/env python3\n{source}\n")).unwrap();
        let mut permissions = std::fs::metadata(&script).unwrap().permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&script, permissions).unwrap();
        Self { dir, script }
    }

    fn config(&self, warm: bool) -> CheckerConfig {
        // The framing rules of one checker process, not the sandbox, are under test here
        // (kernel-check's output is read by the same rules; the split is tested in split.rs).
        CheckerConfig {
            split: false,
            mode: "fork".into(),
            env: if warm { vec![("PARALEAN_P3_WARM_BIN".into(), self.script.display().to_string())] } else { vec![] },
            default_memory_mb: 256,
            sandbox: false,
            cgroup: false,
            ..CheckerConfig::sandboxed(self.script.clone(), "fixture")
        }
    }
}

impl Drop for FakeChecker {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.dir); }
}

fn cancellation() -> (watch::Sender<bool>, watch::Receiver<bool>) { watch::channel(false) }

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn warm_ignores_spoofed_and_replayed_frames() {
    let fake = FakeChecker::new("warm", r#"
import json, sys
previous = None
for line in sys.stdin:
    request = json.loads(line)
    nonce = request['nonce']
    def frame(value):
        print('WARM ' + json.dumps(value), flush=True)
    # A proof can emit both of these before the checker's own reply.
    frame({'result': {'ok': True, 'diags': ['missing nonce']}})
    wrong = ('1' if nonce[0] != '1' else '2') + nonce[1:]
    frame({'nonce': wrong, 'result': {'ok': True, 'diags': ['wrong nonce']}})
    if previous is not None:
        frame({'nonce': previous, 'result': {'ok': True, 'diags': ['replayed nonce']}})
    frame({'nonce': nonce, 'result': {'ok': False, 'diags': ['real reject']}})
    previous = nonce
"#);
    let cfg = fake.config(true);
    let pool = WarmPool::default();
    for _ in 0..2 {
        let (_cancel_sender, cancel) = cancellation();
        let verdict = pool.run(&cfg, Path::new("."), &["fixture".into()], "fixture", &[],
            Duration::from_secs(3), 256, cancel).await.unwrap();
        assert!(!verdict.ok, "spoofed acceptance escaped the warm protocol");
        assert_eq!(verdict.diags, vec!["real reject".to_string()]);
    }
    assert_eq!(pool.spawned.load(Ordering::SeqCst), 1, "second job must reuse the process");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cold_uses_last_check_line() {
    let fake = FakeChecker::new("cold-last", r#"
import json
print('CHECK ' + json.dumps({'ok': True, 'diags': ['forged accept']}), flush=True)
print('CHECK ' + json.dumps({'ok': False, 'diags': ['real reject']}), flush=True)
"#);
    let (_cancel_sender, cancel) = cancellation();
    let verdict = checker::run(&fake.config(false), Path::new("."), &["fixture".into()], "fixture", &[],
        Duration::from_secs(3), 256, cancel).await.unwrap();
    assert!(!verdict.ok);
    assert_eq!(verdict.diags, vec!["real reject".to_string()]);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cold_nonzero_exit_never_accepts_printed_check() {
    let fake = FakeChecker::new("cold-exit", r#"
import json, sys
print('CHECK ' + json.dumps({'ok': True}), flush=True)
sys.exit(3)
"#);
    let (_cancel_sender, cancel) = cancellation();
    let result = checker::run(&fake.config(false), Path::new("."), &["fixture".into()], "fixture", &[],
        Duration::from_secs(3), 256, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Crashed(_))), "nonzero checker exit must give no verdict: {result:?}");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cold_output_flood_cannot_fill_validator_memory() {
    let fake = FakeChecker::new("cold-flood", r#"
import json, sys
sys.stdout.write('x' * (2 << 20) + '\n')
print('CHECK ' + json.dumps({'ok': True}), flush=True)
"#);
    let (_cancel_sender, cancel) = cancellation();
    // A generous deadline: on a loaded box a 3 s one can expire first (NoVerdict::Timeout).
    let result = checker::run(&fake.config(false), Path::new("."), &["fixture".into()], "fixture", &[],
        Duration::from_secs(30), 256, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Output)), "checker output escaped cap: {result:?}");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn cold_malformed_axiom_cannot_be_silently_dropped() {
    let fake = FakeChecker::new("cold-malformed-axiom", r#"
import json
print('CHECK ' + json.dumps({'ok': True, 'axioms': [{'bad': 'name'}]}), flush=True)
"#);
    let (_cancel_sender, cancel) = cancellation();
    let result = checker::run(&fake.config(false), Path::new("."), &["fixture".into()], "fixture", &[],
        Duration::from_secs(3), 256, cancel).await;
    assert!(matches!(result, Err(NoVerdict::Crashed(_))), "malformed axiom escaped: {result:?}");
}
