//! The Lean side of a validator: impl/p1's `paralean check-group`, run as a subprocess with
//! a deadline, a memory limit and cancellation.
//!
//! In production (`CheckerConfig::from_env`) every checker runs in a rootless Bubblewrap
//! sandbox inside a transient systemd scope (see docs/w2-sandbox-notes.md):
//!
//! - memory: the scope's `MemoryMax` (the job's limit, no swap, `OOMPolicy=kill`) is the
//!   hard limit; an OOM kill gives `NoVerdict::Memory`. A resident-set poll over the
//!   checker's process group every 50 ms is a second, soft layer, and the only one when
//!   cgroups are explicitly disabled (`PARALEAN_CHECKER_CGROUP=off`). `RLIMIT_AS` is not
//!   the job limit: Lean reserves far more address space than it uses.
//! - processes: the scope's `TasksMax` and, inside the sandbox, `RLIMIT_NPROC`.
//! - disk: size-capped private tmpfs mounts on /work and /tmp (ENOSPC) and `RLIMIT_FSIZE`
//!   per file. Nothing outside the sandbox is writable, so nothing outside is measured.
//! - CPU: `RLIMIT_CPU` and the job deadline.
//!
//! Exceeding a limit, passing the deadline, crashing, being cancelled or failing to set
//! up any part of the sandbox gives no verdict; there is no unsandboxed fallback.

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

/// Size of each private tmpfs (/work, /tmp) in the sandbox, in bytes.
pub const SCRATCH_BYTES: u64 = 256 << 20;
/// `RLIMIT_FSIZE`: the largest file a sandboxed checker may write, in bytes.
pub const MAX_FILE_BYTES: u64 = 128 << 20;
/// `RLIMIT_NPROC` inside the sandbox (processes and threads of the sandbox's user).
pub const MAX_PROCS: u64 = 64;
/// Default `TasksMax` of the checker's scope (processes and threads, including Bubblewrap).
pub const DEFAULT_MAX_TASKS: u64 = 96;
/// Captured checker stdout and stderr, each.
pub const MAX_OUTPUT_BYTES: usize = 1 << 20;

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
    /// Run the checker in a restricted Bubblewrap user, mount, PID, IPC, UTS and network
    /// namespace. Production configuration always sets it.
    pub sandbox: bool,
    /// With `sandbox`: also run it in a transient systemd user scope with hard memory and
    /// task limits. Required (fail closed) unless explicitly disabled.
    pub cgroup: bool,
    /// The scope's `TasksMax`.
    pub max_tasks: u64,
    /// The Bubblewrap binary.
    pub bwrap: PathBuf,
    /// `systemd-run`, which creates the scope.
    pub systemd_run: PathBuf,
}

impl CheckerConfig {
    /// From `PARALEAN_BIN` (impl/p1/scripts/env.sh), `lean --githash` on `PATH` and
    /// `PARALEAN_LEAN` (`fork` selects fork mode). The sandbox is always on.
    /// `PARALEAN_CHECKER_CGROUP=off` is the explicit opt-out of the cgroup layer for hosts
    /// without delegated cgroup v2 controllers; any value other than `on`/`off` is an error.
    pub fn from_env() -> Result<CheckerConfig, String> {
        let bin = PathBuf::from(std::env::var("PARALEAN_BIN").map_err(|_| "PARALEAN_BIN not set (source impl/p3/scripts/env.sh)")?);
        let mode = if std::env::var("PARALEAN_LEAN").as_deref() == Ok("fork") { "fork" } else { "stock" };
        let cgroup = match std::env::var("PARALEAN_CHECKER_CGROUP").as_deref() {
            Err(_) | Ok("on") => true,
            Ok("off") => false,
            Ok(other) => return Err(format!("PARALEAN_CHECKER_CGROUP must be on or off, not {other:?}")),
        };
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
            sandbox: !cfg!(feature = "mutate-checker-config-unsandboxed"),
            cgroup,
            max_tasks: DEFAULT_MAX_TASKS,
            bwrap: PathBuf::from("/usr/bin/bwrap"),
            systemd_run: PathBuf::from("/usr/bin/systemd-run"),
        })
    }

    /// A sandboxed configuration for `bin` with the production limits (tests, tools).
    pub fn sandboxed(bin: PathBuf, lean_githash: &str) -> CheckerConfig {
        CheckerConfig {
            bin, mode: "stock".into(), lean_githash: lean_githash.into(), env: vec![],
            default_memory_mb: 4096, sandbox: true, cgroup: true, max_tasks: DEFAULT_MAX_TASKS,
            bwrap: PathBuf::from("/usr/bin/bwrap"), systemd_run: PathBuf::from("/usr/bin/systemd-run"),
        }
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

/// A prepared checker process: the command, the seccomp program it must inherit and the
/// transient scope it runs in.
struct Launch {
    cmd: Command,
    seccomp: Option<OwnedFd>,
    scope: Option<String>,
}

/// Runs in the new scope before Bubblewrap: refuse to start the checker unless the scope's
/// memory, swap and task limits are the requested ones. systemd silently ignores limits
/// whose controller is not delegated; this makes that a setup failure, not an unlimited run.
const SCOPE_PREAMBLE: &str = r#"p=; while IFS= read -r l; do case $l in 0::*) p=${l#0::};; esac; done < /proc/self/cgroup
d=/sys/fs/cgroup$p; m=; s=; t=
read -r m < "$d/memory.max" && read -r s < "$d/memory.swap.max" && read -r t < "$d/pids.max" || { echo "paralean-scope: cannot read cgroup limits of $d" >&2; exit 125; }
[ "$m" = "$1" ] && [ "$s" = 0 ] && [ "$t" = "$2" ] || { echo "paralean-scope: cgroup limits not applied ($m $s $t)" >&2; exit 125; }
shift 2; exec "$@""#;

/// Construct a process with an empty mount tree. Only the toolchain, checker,
/// declared Lean imports, system runtime and this job's input store are visible.
/// The caller supplies checker arguments after this function returns.
fn checker_command(cfg: &CheckerConfig, store: &Path, bin: &Path, memory_mb: u64) -> Result<Launch, NoVerdict> {
    if !sandbox_active(cfg) { return Ok(Launch { cmd: Command::new(bin), seccomp: None, scope: None }); }
    if cfg!(feature = "mutate-checker-fallback-unsandboxed") && !cfg.bwrap.is_file() {
        return Ok(Launch { cmd: Command::new(bin), seccomp: None, scope: None });
    }
    let store = store.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox input store: {e}")))?;
    if !store.is_dir() { return Err(NoVerdict::Crashed("sandbox input store is not a directory".into())); }
    let bin = bin.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox checker: {e}")))?;
    let prefix = std::env::var("PARALEAN_SYSROOT").ok().map(PathBuf::from).unwrap_or_else(|| {
        std::process::Command::new("lean").arg("--print-prefix").output()
            .ok().map(|o| PathBuf::from(String::from_utf8_lossy(&o.stdout).trim())).unwrap_or_default()
    });
    let prefix = prefix.canonicalize().map_err(|e| NoVerdict::Crashed(format!("sandbox Lean sysroot: {e}")))?;
    if !prefix.join("bin/lean").is_file() || !prefix.join("bin/lake").is_file() {
        return Err(NoVerdict::Crashed("sandbox Lean sysroot has no lean/lake".into()));
    }
    let scope = sandbox_scope(cfg).then(|| format!("paralean-checker-{}", hex::encode(rand::random::<[u8; 8]>())));
    let mut cmd = match &scope {
        Some(unit) => {
            let memory = memory_mb.max(1).saturating_mul(1 << 20);
            let mut cmd = Command::new(&cfg.systemd_run);
            cmd.args(["--user", "--scope", "--quiet", "--unit", unit])
                .arg("-p").arg(format!("MemoryMax={memory}"))
                .args(["-p", "MemorySwapMax=0", "-p", "OOMPolicy=kill"])
                .arg("-p").arg(format!("TasksMax={}", cfg.max_tasks))
                .args(["--", "/bin/sh", "-c", SCOPE_PREAMBLE, "paralean-scope"])
                .arg(memory.to_string()).arg(cfg.max_tasks.to_string())
                .arg(&cfg.bwrap);
            if std::env::var_os("XDG_RUNTIME_DIR").is_none() {
                cmd.env("XDG_RUNTIME_DIR", format!("/run/user/{}", unsafe { libc::getuid() }));
            }
            cmd
        }
        None => Command::new(&cfg.bwrap),
    };
    let scratch = if cfg!(feature = "mutate-no-checker-disk-limit") { 1u64 << 30 } else { SCRATCH_BYTES }.to_string();
    cmd.args(["--unshare-user", "--unshare-pid", "--unshare-net", "--unshare-ipc", "--unshare-uts",
        "--cap-drop", "ALL",
        "--disable-userns", "--die-with-parent", "--clearenv", "--proc", "/proc", "--dev", "/dev",
        "--size", &scratch, "--tmpfs", "/tmp"]);
    let seccomp = if cfg!(feature = "mutate-no-checker-seccomp") { None } else { Some(seccomp_filter()?) };
    if let Some(fd) = &seccomp { cmd.arg("--seccomp").arg(fd.as_raw_fd().to_string()); }
    for path in ["/usr", "/bin", "/lib", "/lib64"] {
        if Path::new(path).exists() { cmd.args(["--ro-bind", path, path]); }
    }
    if Path::new("/etc/ld.so.cache").is_file() { cmd.args(["--ro-bind", "/etc/ld.so.cache", "/etc/ld.so.cache"]); }
    // The verified input store is read-only; the checker works on a copy in a size-capped
    // private tmpfs. Native initializers may write under /work, never into host files.
    cmd.args(["--ro-bind", store.to_str().unwrap(), "/input", "--size", &scratch, "--tmpfs", "/work"]);
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
    // The sandbox root is bwrap's own tmpfs, which holds the directories it creates for
    // the bind targets above (such as the checker's own directory). Make it read-only, so
    // the only writable places are the size-capped /tmp and /work (W2-55).
    if !cfg!(feature = "mutate-writable-sandbox-root") { cmd.args(["--remount-ro", "/"]); }
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
    let nproc = format!("cp -R /input/. /work/ && exec /usr/bin/prlimit --nproc={MAX_PROCS}:{MAX_PROCS} -- \"$@\"");
    cmd.args(["--chdir", "/work", "--", "/bin/sh", "-c",
        if cfg!(feature = "mutate-no-checker-process-limit") { "cp -R /input/. /work/ && exec \"$@\"" } else { &nproc },
        "sandbox-checker"]);
    cmd.arg(bin);
    Ok(Launch { cmd, seccomp, scope })
}

/// The seccomp program (x86_64 only; other architectures fail closed). Denied with EPERM:
/// sockets and network calls, mounts (old and new API), namespaces, tracing and
/// cross-process memory access, BPF/perf, kernel keyrings, file handles, session/process
/// group changes (the validator kills the checker by process group), pidfds, io_uring,
/// userfaultfd, module/kexec/reboot/swap/accounting/quota/port-I/O and `syslog`, and the
/// terminal-injection ioctls TIOCSTI and TIOCLINUX. Non-x86_64 syscall ABIs kill the process.
/// `clone`/`clone3` are allowed (threads need them); new namespaces are prevented by
/// `--cap-drop ALL` and `--disable-userns` instead, since `clone3` flags are behind a
/// pointer a filter cannot read.
#[cfg(target_arch = "x86_64")]
fn seccomp_filter() -> Result<OwnedFd, NoVerdict> {
    use libc::sock_filter as F;
    let stmt = |code, k| F { code, jt: 0, jf: 0, k };
    let jump = |k| F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 0, jf: 1, k };
    let deny = stmt((libc::BPF_RET | libc::BPF_K) as u16, libc::SECCOMP_RET_ERRNO | libc::EPERM as u32);
    let allow = stmt((libc::BPF_RET | libc::BPF_K) as u16, libc::SECCOMP_RET_ALLOW);
    let load = |offset| stmt((libc::BPF_LD | libc::BPF_W | libc::BPF_ABS) as u16, offset);
    let mut rules = vec![
        load(4),
        F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 1, jf: 0, k: 0xc000003e },
        stmt((libc::BPF_RET | libc::BPF_K) as u16, libc::SECCOMP_RET_KILL_PROCESS),
        load(0),
        F { code: (libc::BPF_JMP | libc::BPF_JSET | libc::BPF_K) as u16, jt: 0, jf: 1, k: 0x40000000 },
        deny,
    ];
    let mut denied = vec![libc::SYS_socket, libc::SYS_socketpair, libc::SYS_connect, libc::SYS_bind, libc::SYS_listen,
        libc::SYS_accept, libc::SYS_accept4, libc::SYS_sendto, libc::SYS_mount,
        libc::SYS_umount2, libc::SYS_pivot_root, libc::SYS_chroot, libc::SYS_ptrace, libc::SYS_process_vm_readv,
        libc::SYS_process_vm_writev, libc::SYS_bpf, libc::SYS_perf_event_open,
        libc::SYS_keyctl, libc::SYS_add_key, libc::SYS_request_key, libc::SYS_setns,
        libc::SYS_unshare, libc::SYS_open_by_handle_at, libc::SYS_name_to_handle_at, libc::SYS_setsid,
        libc::SYS_setpgid, libc::SYS_pidfd_open, libc::SYS_pidfd_getfd,
        libc::SYS_pidfd_send_signal, libc::SYS_open_tree, libc::SYS_move_mount, libc::SYS_fsopen,
        libc::SYS_fsconfig, libc::SYS_fsmount, libc::SYS_fspick, libc::SYS_mount_setattr,
        libc::SYS_userfaultfd, libc::SYS_init_module, libc::SYS_finit_module, libc::SYS_delete_module,
        libc::SYS_kexec_load, libc::SYS_kexec_file_load, libc::SYS_reboot, libc::SYS_swapon,
        libc::SYS_swapoff, libc::SYS_acct, libc::SYS_quotactl, libc::SYS_iopl, libc::SYS_ioperm,
        libc::SYS_syslog];
    if !cfg!(feature = "mutate-checker-seccomp-allows-io-uring") {
        denied.extend([libc::SYS_io_uring_setup, libc::SYS_io_uring_enter, libc::SYS_io_uring_register]);
    }
    for syscall in denied {
        rules.push(jump(syscall as u32));
        rules.push(deny);
    }
    // ioctl(fd, TIOCSTI | TIOCLINUX, ...): compare the low word of the request argument.
    rules.push(F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 0, jf: 4, k: libc::SYS_ioctl as u32 });
    rules.push(load(24));
    rules.push(F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 1, jf: 0, k: libc::TIOCSTI as u32 });
    rules.push(F { code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16, jt: 0, jf: 1, k: libc::TIOCLINUX as u32 });
    rules.push(deny);
    rules.push(allow);
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

fn sandbox_scope(cfg: &CheckerConfig) -> bool {
    sandbox_active(cfg) && cfg.cgroup && !cfg!(feature = "mutate-no-checker-cgroup")
}

/// After a checker ended without a verdict: whether its scope was OOM-killed. Also clears
/// the failed unit so systemd does not keep it. systemd finalises the scope's `Result`
/// slightly after the child dies, so this polls briefly for a definite outcome.
fn scope_oom_killed(unit: &str) -> bool {
    let unit = format!("{unit}.scope");
    // `Result` is only final once the scope has deactivated, so gate on `ActiveState`.
    let query = || -> (String, String) {
        let out = std::process::Command::new("systemctl").args(["--user", "show", "-p", "ActiveState", "-p", "Result", &unit])
            .stdin(Stdio::null()).stderr(Stdio::null()).output()
            .map(|o| String::from_utf8_lossy(&o.stdout).into_owned()).unwrap_or_default();
        let field = |k: &str| out.lines().find_map(|l| l.strip_prefix(k)).unwrap_or("").to_string();
        (field("ActiveState="), field("Result="))
    };
    let mut result = String::new();
    for _ in 0..80 {
        let (state, r) = query();
        result = r;
        // A missing or deactivated unit has a final Result; active/deactivating does not.
        if state.is_empty() || state == "inactive" || state == "failed" { break; }
        std::thread::sleep(Duration::from_millis(25));
    }
    if !result.is_empty() && result != "success" {
        let _ = std::process::Command::new("systemctl").args(["--user", "reset-failed", &unit])
            .stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null()).status();
    }
    result == "oom-kill"
}

fn limit_child(cmd: &mut Command, deadline: Duration, seccomp_fd: Option<i32>) {
    let cpu = deadline.as_secs().saturating_add(2).max(2);
    let fsize = if cfg!(feature = "mutate-no-checker-fsize-limit") { libc::RLIM_INFINITY } else { MAX_FILE_BYTES };
    unsafe {
        cmd.pre_exec(move || {
            for (resource, value) in [
                (libc::RLIMIT_CPU, if cfg!(feature = "mutate-no-checker-cpu-limit") { libc::RLIM_INFINITY } else { cpu }),
                (libc::RLIMIT_FSIZE, fsize),
                (libc::RLIMIT_NOFILE, 256),
                (libc::RLIMIT_CORE, 0),
                // A backstop only; see the module comment.
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
    scope: Option<String>,
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
                let Launch { cmd: mut command, seccomp, scope } = checker_command(cfg, store, Path::new(bin), memory_mb)?;
                command.envs(cfg.env.iter().cloned())
                    .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null())
                    .process_group(0).kill_on_drop(true);
                limit_child(&mut command, deadline, seccomp.as_ref().map(AsRawFd::as_raw_fd));
                let mut child = command.spawn()
                    .map_err(|e| NoVerdict::Crashed(format!("spawn {bin}: {e}")))?;
                drop(seccomp);
                let pgid = child.id().unwrap_or(0) as i32;
                self.spawned.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                WarmProcess { input: child.stdin.take().unwrap(),
                    output: tokio::io::BufReader::new(child.stdout.take().unwrap()), child, pgid, scope }
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
        let mut peak_kb = 0u64;
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
                    peak_kb = peak_kb.max(rss);
                    self.peak_rss_kb.fetch_max(rss, std::sync::atomic::Ordering::Relaxed);
                    if !cfg!(feature = "mutate-no-checker-memory-limit") && rss > memory_mb.max(1).saturating_mul(1024) {
                        break Err(NoVerdict::Memory { limit_mb: memory_mb, peak_mb: rss / 1024, cgroup: false });
                    }
                },
                r = cancel.changed() => if r.is_err() || *cancel.borrow() { break Err(NoVerdict::Cancelled); }
            }
        }
        };
        // A sandboxed process is single-use: once it has run one package's code it must not
        // judge another package. Only unsandboxed (test) processes return to the pool.
        if result.is_ok() && !sandbox_active(cfg) {
            self.idle.lock().unwrap().push(proc);
            return result;
        }
        kill_group(pgid);
        let _ = proc.child.wait().await;
        match proc.scope.take() {
            Some(unit) if scope_oom_killed(&unit) && result.is_err() && !matches!(result, Err(NoVerdict::Cancelled)) =>
                Err(NoVerdict::Memory { limit_mb: memory_mb, peak_mb: peak_kb / 1024, cgroup: true }),
            _ => result,
        }
    }
}

/// Why there is no verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NoVerdict {
    Timeout,
    /// `cgroup`: the scope's hard limit killed it (otherwise the resident-set poll did).
    Memory { limit_mb: u64, peak_mb: u64, cgroup: bool },
    Cancelled,
    Output,
    Crashed(String),
}

impl std::fmt::Display for NoVerdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NoVerdict::Timeout => write!(f, "deadline passed"),
            NoVerdict::Memory { limit_mb, peak_mb, .. } => write!(f, "memory limit {limit_mb} MiB exceeded ({peak_mb} MiB resident)"),
            NoVerdict::Cancelled => write!(f, "cancelled"),
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
    let Launch { mut cmd, seccomp, scope } = checker_command(cfg, store, &cfg.bin, memory_mb)?;
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
    limit_child(&mut cmd, deadline, seccomp.as_ref().map(AsRawFd::as_raw_fd));
    // A missing or failing sandbox is a setup failure; there is no direct fallback.
    let mut child = cmd.spawn().map_err(|e| NoVerdict::Crashed(format!("spawn checker {}: {e}", cfg.bin.display())))?;
    drop(seccomp);
    let pgid = child.id().unwrap_or(0) as i32;
    let mut stdout = child.stdout.take().expect("piped");
    let mut stderr = child.stderr.take().expect("piped");
    let mut out_task = tokio::spawn(async move {
        let mut bytes = Vec::new();
        let cap = if cfg!(feature = "mutate-unbounded-checker-output") { u64::MAX } else { MAX_OUTPUT_BYTES as u64 + 1 };
        let _ = (&mut stdout).take(cap).read_to_end(&mut bytes).await;
        bytes
    });
    let mut err_task = tokio::spawn(async move {
        let mut bytes = Vec::new();
        let cap = if cfg!(feature = "mutate-unbounded-checker-output") { u64::MAX } else { MAX_OUTPUT_BYTES as u64 + 1 };
        let _ = (&mut stderr).take(cap).read_to_end(&mut bytes).await;
        bytes
    });
    let limit_kb = memory_mb.max(1).saturating_mul(1024);
    let start = Instant::now();
    let mut peak_kb = 0u64;
    let mut tick = tokio::time::interval(Duration::from_millis(50));
    let mut captured_out = None;
    let mut captured_err = None;
    let fail = loop {
        tokio::select! {
            st = child.wait() => {
                let st = st.map_err(|e| NoVerdict::Crashed(e.to_string()))?;
                if !st.success() {
                    if let Some(unit) = &scope {
                        // OOMPolicy=kill: an OOM kill takes the whole scope, so a checker
                        // that exited successfully was never OOM-killed.
                        if scope_oom_killed(unit) {
                            kill_group(pgid);
                            return Err(NoVerdict::Memory { limit_mb: memory_mb, peak_mb: peak_kb / 1024, cgroup: true });
                        }
                    }
                }
                let out = match captured_out { Some(bytes) => bytes, None => out_task.await.unwrap_or_default() };
                let err = match captured_err { Some(bytes) => bytes, None => err_task.await.unwrap_or_default() };
                if !cfg!(feature = "mutate-unbounded-checker-output") && (out.len() > MAX_OUTPUT_BYTES || err.len() > MAX_OUTPUT_BYTES) { return Err(NoVerdict::Output); }
                let out = String::from_utf8_lossy(&out);
                let err = String::from_utf8_lossy(&err);
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
                if !cfg!(feature = "mutate-unbounded-checker-output") && bytes.len() > MAX_OUTPUT_BYTES { break NoVerdict::Output; }
                captured_out = Some(bytes);
            }
            bytes = &mut err_task, if captured_err.is_none() => {
                let bytes = bytes.unwrap_or_default();
                if !cfg!(feature = "mutate-unbounded-checker-output") && bytes.len() > MAX_OUTPUT_BYTES { break NoVerdict::Output; }
                captured_err = Some(bytes);
            }
            _ = tick.tick() => {
                if !cfg!(feature = "mutate-no-checker-cpu-limit") && start.elapsed() >= deadline {
                    break NoVerdict::Timeout;
                }
                let rss = group_rss_kb(pgid);
                peak_kb = peak_kb.max(rss);
                if !cfg!(feature = "mutate-no-checker-memory-limit") && rss > limit_kb {
                    break NoVerdict::Memory { limit_mb: memory_mb, peak_mb: rss / 1024, cgroup: false };
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
    // The reason is already known; this clears a failed scope unit.
    if let Some(unit) = &scope { scope_oom_killed(unit); }
    Err(fail)
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
