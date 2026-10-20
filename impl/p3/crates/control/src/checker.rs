//! The Lean side of a validator: impl/p1's `paralean check-group`, run as a subprocess with
//! a deadline, a memory limit and cancellation.
//!
//! The memory limit is a resident-set watchdog over the checker's process group, not
//! `RLIMIT_AS`: Lean reserves far more address space than it uses (a check of a fixture
//! group peaks at 0.5 GB resident but cannot even create its threads under a 4 GB
//! address-space limit). Exceeding the limit, passing the deadline, crashing or being
//! cancelled all kill the process group and give no verdict.

use std::path::{Path, PathBuf};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::process::Stdio;
use std::time::{Duration, Instant};

use paralean_store::receipt::CheckerVersion;
use paralean_store::Name;
use serde::Deserialize;
use tokio::io::AsyncReadExt;
use tokio::process::Command;
use tokio::sync::watch;

use crate::p1::name_of;

/// How to run the checker.
#[derive(Clone, Debug)]
pub struct CheckerConfig {
    /// impl/p1's `paralean` binary (or a fork build of it).
    pub bin: PathBuf,
    /// `stock` or `fork`.
    pub mode: String,
    /// `lean --githash` of the toolchain the binary loads.
    pub lean_githash: String,
    /// Extra environment for the checker (e.g. `LEAN_NUM_THREADS`).
    pub env: Vec<(String, String)>,
    /// Memory limit when the job names none, in MiB.
    pub default_memory_mb: u64,
    /// Run the checker in a restricted Bubblewrap mount and network namespace.
    pub sandbox: bool,
}

impl CheckerConfig {
    /// From `PARALEAN_BIN` (impl/p1/scripts/env.sh), `lean --githash` on `PATH` and
    /// `PARALEAN_LEAN` (`fork` selects fork mode).
    pub fn from_env() -> Result<CheckerConfig, String> {
        let bin = PathBuf::from(std::env::var("PARALEAN_BIN").map_err(|_| "PARALEAN_BIN not set (source impl/p3/scripts/env.sh)")?);
        let mode = if std::env::var("PARALEAN_LEAN").as_deref() == Ok("fork") { "fork" } else { "stock" };
        Ok(CheckerConfig {
            bin,
            mode: mode.into(),
            lean_githash: lean_githash()?,
            env: {
                let mut env = vec![("LEAN_NUM_THREADS".into(), "2".into())];
                if let Ok(bin) = std::env::var("PARALEAN_P3_WARM_BIN") {
                    env.push(("PARALEAN_P3_WARM_BIN".into(), bin));
                }
                env
            },
            default_memory_mb: 4096,
            sandbox: true,
        })
    }

    /// The checker version this configuration produces (its ID goes into receipts).
    pub fn version(&self) -> Result<CheckerVersion, String> {
        let mut bytes = std::fs::read(&self.bin).map_err(|e| format!("{}: {e}", self.bin.display()))?;
        if let Some(bin) = self.warm_bin() {
            bytes.extend_from_slice(b"\0paralean-warm-checker-v1\0");
            bytes.extend(std::fs::read(bin).map_err(|e| format!("{bin}: {e}"))?);
        }
        Ok(CheckerVersion {
            lean_githash: self.lean_githash.clone(),
            checker_sha256: paralean_store::id::sha256(&bytes).to_vec(),
            mode: self.mode.clone(),
        })
    }

    pub fn warm_bin(&self) -> Option<&str> {
        self.env.iter().find(|(k, _)| k == "PARALEAN_P3_WARM_BIN").map(|(_, v)| v.as_str())
    }
}

/// Construct a process with an empty mount tree. Only the toolchain, checker,
/// declared Lean imports, system runtime and this job's scratch store are visible.
/// The caller supplies checker arguments after this function returns.
fn checker_command(cfg: &CheckerConfig, store: &Path, bin: &Path) -> Result<(Command, Option<OwnedFd>), NoVerdict> {
    if !sandbox_active(cfg) { return Ok((Command::new(bin), None)); }
    let store = store.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox scratch: {e}")))?;
    if !store.is_dir() { return Err(NoVerdict::Crashed("sandbox scratch is not a directory".into())); }
    let bin = bin.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox checker: {e}")))?;
    let prefix = std::env::var("PARALEAN_SYSROOT").ok().map(PathBuf::from).unwrap_or_else(|| {
        std::process::Command::new("lean").arg("--print-prefix").output()
            .ok().map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim())).unwrap_or_default()
    });
    let prefix = prefix.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox Lean sysroot: {e}")))?;
    if !prefix.join("bin/lean").is_file() || !prefix.join("bin/lake").is_file() {
        return Err(NoVerdict::Crashed("sandbox Lean sysroot has no lean/lake".into()));
    }
    let mut cmd = Command::new("/usr/bin/bwrap");
    cmd.args(["--unshare-user", "--unshare-pid", "--unshare-net", "--unshare-ipc", "--unshare-uts",
        "--cap-drop", "ALL",
        "--disable-userns", "--die-with-parent", "--clearenv", "--proc", "/proc", "--dev", "/dev",
        "--size", "268435456", "--tmpfs", "/tmp"]);
    let seccomp = if cfg!(feature = "mutate-no-checker-seccomp") { None } else { Some(seccomp_filter()?) };
    if let Some(fd) = &seccomp { cmd.arg("--seccomp").arg(fd.as_raw_fd().to_string()); }
    for path in ["/usr", "/bin", "/lib", "/lib64"] {
        if Path::new(path).exists() { cmd.args(["--ro-bind", path, path]); }
    }
    if Path::new("/etc/ld.so.cache").is_file() { cmd.args(["--ro-bind", "/etc/ld.so.cache", "/etc/ld.so.cache"]); }
    // Copy the small, verified input store into a size-capped private tmpfs.
    // Native initializers may write under /work, but never into host scratch.
    cmd.args(["--ro-bind", store.to_str().unwrap(), "/input",
        "--size", if cfg!(feature = "mutate-no-checker-disk-limit") { "1073741824" } else { "268435456" }, "--tmpfs", "/work"]);
    let mut mounts = vec![prefix.clone()];
    mounts.push(bin.clone());
    for key in ["PARALEAN_LIB", "PARALEAN_MATHLIB"] {
        if let Ok(value) = std::env::var(key) {
            if Path::new(&value).exists() { mounts.push(PathBuf::from(value)); }
        }
    }
    if let Ok(value) = std::env::var("LEAN_PATH") {
        mounts.extend(std::env::split_paths(&value));
    }
    for path in mounts {
        let path = path.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox mount {}: {e}", path.display())))?;
        if !path.is_absolute() { return Err(NoVerdict::Crashed("sandbox mount is relative".into())); }
        cmd.arg("--ro-bind").arg(&path).arg(&path);
    }
    let path = format!("{}/bin:/usr/bin:/bin", prefix.display());
    cmd.args(["--setenv", "PATH", &path, "--setenv", "HOME", "/tmp", "--setenv", "TMPDIR", "/tmp",
        "--setenv", "PARALEAN_SYSROOT", prefix.to_str().unwrap(), "--setenv", "PARALEAN_LAKE", prefix.join("bin/lake").to_str().unwrap()]);
    // Add environment only from the checker's declared Lean inputs. Never pass
    // the validator's S3 credentials, FDB cluster, token or signing key.
    for key in ["PARALEAN_LIB", "PARALEAN_MATHLIB", "LEAN_PATH", "LEAN_PARALEAN", "PARALEAN_FORK_HOOKS"] {
        if let Ok(value) = std::env::var(key) {
            if !matches!(key, "PARALEAN_LIB" | "PARALEAN_MATHLIB") || Path::new(&value).exists() {
                cmd.args(["--setenv", key, &value]);
            }
        }
    }
    for (key, value) in &cfg.env {
        if key == "LEAN_NUM_THREADS" { cmd.args(["--setenv", key, value]); }
    }
    cmd.args(["--chdir", "/work", "--", "/bin/sh", "-c",
        if cfg!(feature = "mutate-no-checker-process-limit") {
            "cp -R /input/. /work/ && exec \"$@\""
        } else {
            "cp -R /input/. /work/ && exec /usr/bin/prlimit --nproc=64:64 -- \"$@\""
        }, "sandbox-checker"]);
    cmd.arg(bin);
    Ok((cmd, seccomp))
}

#[cfg(target_arch = "x86_64")]
fn seccomp_filter() -> Result<OwnedFd, NoVerdict> {
    use libc::sock_filter as F;
    let stmt = |code, k| F { code, jt: 0, jf: 0, k };
    let jump = |k| F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 0, jf: 1, k };
    let deny = stmt((libc::BPF_RET | libc::BPF_K) as u16, libc::SECCOMP_RET_ERRNO | libc::EPERM as u32);
    let mut rules = vec![
        stmt((libc::BPF_LD | libc::BPF_W | libc::BPF_ABS) as u16, 4),
        F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 1, jf: 0, k: 0xc000003e },
        stmt((libc::BPF_RET | libc::BPF_K) as u16, libc::SECCOMP_RET_KILL_PROCESS),
        stmt((libc::BPF_LD | libc::BPF_W | libc::BPF_ABS) as u16, 0),
        F { code: (libc::BPF_JMP | libc::BPF_JSET | libc::BPF_K) as u16, jt: 0, jf: 1, k: 0x40000000 },
        deny,
    ];
    for syscall in [libc::SYS_socket, libc::SYS_connect, libc::SYS_bind, libc::SYS_listen,
        libc::SYS_accept, libc::SYS_accept4, libc::SYS_sendto, libc::SYS_mount,
        libc::SYS_umount2, libc::SYS_pivot_root, libc::SYS_ptrace, libc::SYS_process_vm_readv,
        libc::SYS_process_vm_writev, libc::SYS_bpf, libc::SYS_perf_event_open,
        libc::SYS_keyctl, libc::SYS_add_key, libc::SYS_request_key, libc::SYS_setns,
        libc::SYS_unshare, libc::SYS_open_by_handle_at, libc::SYS_setsid,
        libc::SYS_setpgid, libc::SYS_pidfd_open, libc::SYS_pidfd_getfd,
        libc::SYS_pidfd_send_signal] {
        rules.push(jump(syscall as u32));
        rules.push(deny);
    }
    rules.push(stmt((libc::BPF_RET | libc::BPF_K) as u16, libc::SECCOMP_RET_ALLOW));
    let name = b"paralean-seccomp\0";
    let fd = unsafe { libc::memfd_create(name.as_ptr().cast(), 0) };
    if fd < 0 { return Err(NoVerdict::Crashed(format!("seccomp memfd: {}", std::io::Error::last_os_error()))); }
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    let bytes = unsafe { std::slice::from_raw_parts(rules.as_ptr().cast::<u8>(), rules.len() * std::mem::size_of::<F>()) };
    let written = unsafe { libc::write(fd.as_raw_fd(), bytes.as_ptr().cast(), bytes.len()) };
    if written != bytes.len() as isize || unsafe { libc::lseek(fd.as_raw_fd(), 0, libc::SEEK_SET) } != 0 {
        return Err(NoVerdict::Crashed(format!("seccomp filter write: {}", std::io::Error::last_os_error())));
    }
    Ok(fd)
}

#[cfg(not(target_arch = "x86_64"))]
fn seccomp_filter() -> Result<OwnedFd, NoVerdict> {
    Err(NoVerdict::Crashed("sandbox seccomp supports x86_64 only".into()))
}

fn sandbox_active(cfg: &CheckerConfig) -> bool {
    cfg.sandbox && !cfg!(feature = "mutate-no-checker-sandbox")
}

fn limit_child(cmd: &mut Command, deadline: Duration, seccomp_fd: Option<i32>) {
    let cpu = deadline.as_secs().saturating_add(2).max(2);
    unsafe {
        cmd.pre_exec(move || {
            for (resource, value) in [
                (libc::RLIMIT_CPU, if cfg!(feature = "mutate-no-checker-cpu-limit") { libc::RLIM_INFINITY } else { cpu }),
                (libc::RLIMIT_FSIZE, 512 * 1024 * 1024),
                (libc::RLIMIT_NOFILE, 256),
                (libc::RLIMIT_CORE, 0),
                (libc::RLIMIT_AS, 16 * 1024 * 1024 * 1024),
            ] {
                let lim = libc::rlimit { rlim_cur: value, rlim_max: value };
                if libc::setrlimit(resource, &lim) != 0 { return Err(std::io::Error::last_os_error()); }
            }
            if let Some(fd) = seccomp_fd {
                // Native store clients may own descriptors without CLOEXEC.
                // Existing sockets must not cross into the checker namespace.
                if libc::syscall(libc::SYS_close_range, 3u32, u32::MAX, libc::CLOSE_RANGE_CLOEXEC) != 0 {
                    return Err(std::io::Error::last_os_error());
                }
                if libc::fcntl(fd, libc::F_SETFD, 0) < 0 { return Err(std::io::Error::last_os_error()); }
            }
            Ok(())
        });
    }
}

/// The base a validator checks against: `H("v0/base", PCE(string githash))`. (§2's full
/// base manifest also pins Mathlib; P3's fixtures use Lean core only.)
pub fn base_id(lean_githash: &str) -> paralean_store::Id {
    let mut e = paralean_store::pce::Enc::new();
    e.string(lean_githash);
    paralean_store::Domain::Base.hash(&e.out)
}

pub fn lean_githash() -> Result<String, String> {
    let out = std::process::Command::new("lean").arg("--githash").output().map_err(|e| format!("lean --githash: {e}"))?;
    Ok(String::from_utf8_lossy(&out.stdout).trim().to_string())
}

/// What `check-group` reported.
#[derive(Clone, Debug)]
pub struct CheckOutcome {
    pub ok: bool,
    pub axioms: Vec<Name>,
    pub public_names: Vec<Name>,
    pub target_ok: Option<bool>,
    pub diags: Vec<String>,
    pub closure: Vec<String>,
}

#[derive(Deserialize)]
pub(crate) struct Raw {
    ok: bool,
    #[serde(default)]
    axioms: Vec<serde_json::Value>,
    #[serde(default, rename = "publicNames")]
    public_names: Vec<serde_json::Value>,
    #[serde(default, rename = "targetOk")]
    target_ok: Option<bool>,
    #[serde(default)]
    diags: Vec<String>,
    #[serde(default)]
    closure: Vec<String>,
}

impl Raw {
    fn outcome(self) -> Result<CheckOutcome, NoVerdict> {
        let names = |items: &[serde_json::Value]| -> Result<Vec<Name>, NoVerdict> {
            if cfg!(feature = "mutate-drop-invalid-axiom") {
                return Ok(items.iter().filter_map(name_of).collect());
            }
            items.iter().map(|value| name_of(value).ok_or_else(||
                NoVerdict::Crashed("checker returned an invalid name".into()))).collect()
        };
        Ok(CheckOutcome {
            ok: self.ok,
            axioms: names(&self.axioms)?,
            public_names: names(&self.public_names)?,
            target_ok: self.target_ok,
            diags: self.diags,
            closure: self.closure,
        })
    }
}

/// A bounded validator's idle checker processes. Active processes are owned by one job;
/// dropping an active future kills its process. Only a successful framed reply returns a
/// process to this pool. The validator's admission semaphore bounds the total processes.
#[derive(Default)]
pub struct WarmPool {
    idle: std::sync::Mutex<Vec<WarmProcess>>,
    pub spawned: std::sync::atomic::AtomicU64,
    pub peak_rss_kb: std::sync::atomic::AtomicU64,
}

struct WarmProcess {
    child: tokio::process::Child,
    input: tokio::process::ChildStdin,
    output: tokio::io::BufReader<tokio::process::ChildStdout>,
    pgid: i32,
}

impl Drop for WarmProcess {
    fn drop(&mut self) {
        kill_group(self.pgid);
    }
}

impl WarmPool {
    #[allow(clippy::too_many_arguments)]
    pub async fn run(
        &self, cfg: &CheckerConfig, store: &Path, gids: &[String], decl: &str,
        targets: &[TargetArg], deadline: Duration, memory_mb: u64,
        mut cancel: watch::Receiver<bool>,
    ) -> Result<CheckOutcome, NoVerdict> {
        use tokio::io::{AsyncBufReadExt, AsyncWriteExt};
        if *cancel.borrow() { return Err(NoVerdict::Cancelled); }
        let idle = self.idle.lock().unwrap().pop();
        let mut proc = match idle {
            Some(p) => p,
            None => {
                let bin = cfg.warm_bin().ok_or_else(|| NoVerdict::Crashed("no warm checker configured".into()))?;
                let (mut command, _seccomp) = checker_command(cfg, store, Path::new(bin))?;
                command.envs(cfg.env.iter().cloned())
                    .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null())
                    .process_group(0).kill_on_drop(true);
                limit_child(&mut command, deadline, _seccomp.as_ref().map(AsRawFd::as_raw_fd));
                let mut child = command.spawn()
                    .map_err(|e| NoVerdict::Crashed(format!("spawn {bin}: {e}")))?;
                let pgid = child.id().unwrap_or(0) as i32;
                self.spawned.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                WarmProcess { input: child.stdin.take().unwrap(),
                    output: tokio::io::BufReader::new(child.stdout.take().unwrap()), child, pgid }
            }
        };
        // stdout also contains output from checked Lean commands. Bind the transport
        // frame to this request instead of treating arbitrary `WARM` output as a verdict.
        let nonce = hex::encode(rand::random::<[u8; 32]>());
        let request = serde_json::json!({
            "nonce": nonce,
            "store": if sandbox_active(cfg) { Path::new("/work") } else { store }, "gids": gids, "decl": decl,
            "targets": targets.iter().map(|t| serde_json::json!({
                "name": t.name.to_string(), "statement": t.statement,
            })).collect::<Vec<_>>(),
        });
        let mut bytes = serde_json::to_vec(&request).map_err(|e| NoVerdict::Crashed(e.to_string()))?;
        bytes.push(b'\n');
        let pgid = proc.pgid;
        let initial_bytes = if sandbox_active(cfg) { scratch_bytes(store) } else { 0 };
        let result = {
        let operation = async {
            proc.input.write_all(&bytes).await.map_err(|e| NoVerdict::Crashed(e.to_string()))?;
            proc.input.flush().await.map_err(|e| NoVerdict::Crashed(e.to_string()))?;
            let mut total = 0;
            loop {
                let mut line = String::new();
                // Limit even a single malicious output line, not only complete frames.
                let n = (&mut proc.output).take(16 << 20).read_line(&mut line).await
                    .map_err(|e| NoVerdict::Crashed(e.to_string()))?;
                total += n;
                if n == 0 || total >= 16 << 20 {
                    return Err(NoVerdict::Crashed("warm checker closed or exceeded output limit".into()));
                }
                let Some(line) = line.strip_prefix("WARM ") else { continue };
                let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
                if v.get("nonce").and_then(|n| n.as_str()) != Some(nonce.as_str()) { continue; }
                if let Some(error) = v.get("error") {
                    return Err(NoVerdict::Crashed(error.to_string()));
                }
                let raw: Raw = serde_json::from_value(v["result"].clone()).map_err(|e| NoVerdict::Crashed(e.to_string()))?;
                return raw.outcome();
            }
        };
        let mut tick = tokio::time::interval(Duration::from_millis(50));
        let start = Instant::now();
        tokio::pin!(operation);
        loop {
            tokio::select! {
                r = &mut operation => break r,
                _ = tick.tick() => {
                    if !cfg!(feature = "mutate-no-checker-cpu-limit") && start.elapsed() >= deadline { break Err(NoVerdict::Timeout); }
                    let rss = group_rss_kb(pgid);
                    self.peak_rss_kb.fetch_max(rss, std::sync::atomic::Ordering::Relaxed);
                    if !cfg!(feature = "mutate-no-checker-memory-limit") && rss > memory_mb.max(1).saturating_mul(1024) {
                        break Err(NoVerdict::Memory { limit_mb: memory_mb, peak_mb: rss / 1024 });
                    }
                    if sandbox_active(cfg) && scratch_bytes(store).saturating_sub(initial_bytes) > 256 << 20 {
                        break Err(NoVerdict::Disk);
                    }
                },
                r = cancel.changed() => if r.is_err() || *cancel.borrow() { break Err(NoVerdict::Cancelled); }
            }
        }
        };
        let result = if sandbox_active(cfg) && scratch_bytes(store).saturating_sub(initial_bytes) > 256 << 20 {
            Err(NoVerdict::Disk)
        } else { result };
        if result.is_ok() && !sandbox_active(cfg) {
            self.idle.lock().unwrap().push(proc);
        } else {
            kill_group(pgid);
            let _ = proc.child.wait().await;
        }
        result
    }
}

/// Why there is no verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NoVerdict {
    Timeout,
    Memory { limit_mb: u64, peak_mb: u64 },
    Cancelled,
    Disk,
    Output,
    Crashed(String),
}

impl std::fmt::Display for NoVerdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NoVerdict::Timeout => write!(f, "deadline passed"),
            NoVerdict::Memory { limit_mb, peak_mb } => write!(f, "memory limit {limit_mb} MiB exceeded ({peak_mb} MiB resident)"),
            NoVerdict::Cancelled => write!(f, "cancelled"),
            NoVerdict::Disk => write!(f, "checker scratch disk limit exceeded"),
            NoVerdict::Output => write!(f, "checker output limit exceeded"),
            NoVerdict::Crashed(s) => write!(f, "checker crashed: {s}"),
        }
    }
}

/// One target the check must find declared, with an optional statement hash (hex).
pub struct TargetArg {
    pub name: Name,
    pub statement: String,
}

/// Run `check-group` on `store` for group `decl`.
pub async fn run(
    cfg: &CheckerConfig,
    store: &Path,
    gids: &[String],
    decl: &str,
    targets: &[TargetArg],
    deadline: Duration,
    memory_mb: u64,
    mut cancel: watch::Receiver<bool>,
) -> Result<CheckOutcome, NoVerdict> {
    let targets_arg: Vec<String> = targets.iter().map(|t| format!("{}={}", t.name, t.statement)).collect();
    let (mut cmd, _seccomp) = checker_command(cfg, store, &cfg.bin)?;
    cmd.arg("check-group").arg("--store").arg(if sandbox_active(cfg) { Path::new("/work") } else { store }).arg("--gids").arg(gids.join(",")).arg("--decl").arg(decl);
    if !targets_arg.is_empty() {
        cmd.arg("--targets").arg(targets_arg.join(","));
    }
    cmd.envs(cfg.env.iter().cloned())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0)
        .kill_on_drop(true);
    limit_child(&mut cmd, deadline, _seccomp.as_ref().map(AsRawFd::as_raw_fd));
    let mut child = cmd.spawn().map_err(|e| NoVerdict::Crashed(format!("spawn {}: {e}", cfg.bin.display())))?;
    let pgid = child.id().unwrap_or(0) as i32;
    let mut stdout = child.stdout.take().expect("piped");
    let mut stderr = child.stderr.take().expect("piped");
    let mut out_task = tokio::spawn(async move {
        let mut bytes = Vec::new();
        let cap = if cfg!(feature = "mutate-unbounded-checker-output") { u64::MAX } else { (1 << 20) + 1 };
        let _ = (&mut stdout).take(cap).read_to_end(&mut bytes).await;
        bytes
    });
    let mut err_task = tokio::spawn(async move {
        let mut bytes = Vec::new();
        let cap = if cfg!(feature = "mutate-unbounded-checker-output") { u64::MAX } else { (1 << 20) + 1 };
        let _ = (&mut stderr).take(cap).read_to_end(&mut bytes).await;
        bytes
    });
    let limit_kb = memory_mb.max(1).saturating_mul(1024);
    let initial_bytes = if sandbox_active(cfg) { scratch_bytes(store) } else { 0 };
    let start = Instant::now();
    let mut peak_kb = 0u64;
    let mut tick = tokio::time::interval(Duration::from_millis(50));
    let mut captured_out = None;
    let mut captured_err = None;
    let fail = loop {
        tokio::select! {
            st = child.wait() => {
                let st = st.map_err(|e| NoVerdict::Crashed(e.to_string()))?;
                let out = match captured_out { Some(bytes) => bytes, None => out_task.await.unwrap_or_default() };
                let err = match captured_err { Some(bytes) => bytes, None => err_task.await.unwrap_or_default() };
                if !cfg!(feature = "mutate-unbounded-checker-output") && (out.len() > 1 << 20 || err.len() > 1 << 20) { return Err(NoVerdict::Output); }
                let out = String::from_utf8_lossy(&out);
                let err = String::from_utf8_lossy(&err);
                if sandbox_active(cfg) && scratch_bytes(store).saturating_sub(initial_bytes) > 256 << 20 {
                    return Err(NoVerdict::Disk);
                }
                let Some(line) = out.lines().rev().find_map(|l| l.strip_prefix("CHECK ")) else {
                    return Err(NoVerdict::Crashed(format!("{st}: {}", err.lines().last().unwrap_or(""))));
                };
                let raw: Raw = serde_json::from_str(line).map_err(|e| NoVerdict::Crashed(format!("bad CHECK line: {e}")))?;
                if raw.ok && !st.success() {
                    return Err(NoVerdict::Crashed(format!("checker reported acceptance but exited {st}")));
                }
                return raw.outcome();
            }
            bytes = &mut out_task, if captured_out.is_none() => {
                let bytes = bytes.unwrap_or_default();
                if !cfg!(feature = "mutate-unbounded-checker-output") && bytes.len() > 1 << 20 { break NoVerdict::Output; }
                captured_out = Some(bytes);
            }
            bytes = &mut err_task, if captured_err.is_none() => {
                let bytes = bytes.unwrap_or_default();
                if !cfg!(feature = "mutate-unbounded-checker-output") && bytes.len() > 1 << 20 { break NoVerdict::Output; }
                captured_err = Some(bytes);
            }
            _ = tick.tick() => {
                if !cfg!(feature = "mutate-no-checker-cpu-limit") && start.elapsed() >= deadline {
                    break NoVerdict::Timeout;
                }
                let rss = group_rss_kb(pgid);
                peak_kb = peak_kb.max(rss);
                if !cfg!(feature = "mutate-no-checker-memory-limit") && rss > limit_kb {
                    break NoVerdict::Memory { limit_mb: memory_mb, peak_mb: rss / 1024 };
                }
                if sandbox_active(cfg) && scratch_bytes(store).saturating_sub(initial_bytes) > 256 << 20 {
                    break NoVerdict::Disk;
                }
            }
            r = cancel.changed() => {
                if r.is_err() || *cancel.borrow() {
                    break NoVerdict::Cancelled;
                }
            }
        }
    };
    kill_group(pgid);
    let _ = child.wait().await;
    Err(fail)
}

fn scratch_bytes(path: &Path) -> u64 {
    let mut total: u64 = 0;
    let mut dirs = vec![path.to_path_buf()];
    while let Some(dir) = dirs.pop() {
        let Ok(entries) = std::fs::read_dir(dir) else { continue };
        for entry in entries.flatten() {
            let Ok(meta) = entry.path().symlink_metadata() else { continue };
            if meta.is_dir() { dirs.push(entry.path()); }
            else { total = total.saturating_add(meta.len()); }
        }
    }
    total
}

fn kill_group(pgid: i32) {
    if pgid > 0 {
        unsafe {
            libc::kill(-pgid, libc::SIGKILL);
        }
    }
}

/// Resident set of every process in process group `pgid`, in KiB (Linux `/proc`).
pub fn group_rss_kb(pgid: i32) -> u64 {
    let page_kb = (unsafe { libc::sysconf(libc::_SC_PAGESIZE) } as u64 / 1024).max(1);
    let mut total = 0;
    let Ok(dir) = std::fs::read_dir("/proc") else { return 0 };
    for e in dir.flatten() {
        let name = e.file_name();
        let Some(pid) = name.to_str().and_then(|s| s.parse::<i32>().ok()) else { continue };
        let Ok(stat) = std::fs::read_to_string(format!("/proc/{pid}/stat")) else { continue };
        // Fields after the parenthesised command: state ppid pgrp ...
        let Some(rest) = stat.rsplit_once(')').map(|(_, r)| r) else { continue };
        let f: Vec<&str> = rest.split_whitespace().collect();
        if f.get(2).and_then(|s| s.parse::<i32>().ok()) != Some(pgid) {
            continue;
        }
        if let Ok(statm) = std::fs::read_to_string(format!("/proc/{pid}/statm")) {
            if let Some(rss) = statm.split_whitespace().nth(1).and_then(|s| s.parse::<u64>().ok()) {
                total += rss * page_kb;
            }
        }
    }
    total
}
