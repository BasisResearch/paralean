//! The Lean side of a validator: impl/p1's `paralean check-group`, run as a subprocess with
//! a deadline, a memory limit and cancellation.
//!
//! The memory limit is a resident-set watchdog over the checker's process group, not
//! `RLIMIT_AS`: Lean reserves far more address space than it uses (a check of a fixture
//! group peaks at 0.5 GB resident but cannot even create its threads under a 4 GB
//! address-space limit). Exceeding the limit, passing the deadline, crashing or being
//! cancelled all kill the process group and give no verdict.

use std::path::{Path, PathBuf};
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
            env: vec![("LEAN_NUM_THREADS".into(), "2".into())],
            default_memory_mb: 4096,
        })
    }

    /// The checker version this configuration produces (its ID goes into receipts).
    pub fn version(&self) -> Result<CheckerVersion, String> {
        let bytes = std::fs::read(&self.bin).map_err(|e| format!("{}: {e}", self.bin.display()))?;
        Ok(CheckerVersion {
            lean_githash: self.lean_githash.clone(),
            checker_sha256: paralean_store::id::sha256(&bytes).to_vec(),
            mode: self.mode.clone(),
        })
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
struct Raw {
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

/// Why there is no verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NoVerdict {
    Timeout,
    Memory { limit_mb: u64, peak_mb: u64 },
    Cancelled,
    Crashed(String),
}

impl std::fmt::Display for NoVerdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NoVerdict::Timeout => write!(f, "deadline passed"),
            NoVerdict::Memory { limit_mb, peak_mb } => write!(f, "memory limit {limit_mb} MiB exceeded ({peak_mb} MiB resident)"),
            NoVerdict::Cancelled => write!(f, "cancelled"),
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
    let mut cmd = Command::new(&cfg.bin);
    cmd.arg("check-group").arg("--store").arg(store).arg("--gids").arg(gids.join(",")).arg("--decl").arg(decl);
    if !targets_arg.is_empty() {
        cmd.arg("--targets").arg(targets_arg.join(","));
    }
    cmd.envs(cfg.env.iter().cloned())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0)
        .kill_on_drop(true);
    let mut child = cmd.spawn().map_err(|e| NoVerdict::Crashed(format!("spawn {}: {e}", cfg.bin.display())))?;
    let pgid = child.id().unwrap_or(0) as i32;
    let mut stdout = child.stdout.take().expect("piped");
    let mut stderr = child.stderr.take().expect("piped");
    let out_task = tokio::spawn(async move {
        let mut s = String::new();
        let _ = stdout.read_to_string(&mut s).await;
        s
    });
    let err_task = tokio::spawn(async move {
        let mut s = String::new();
        let _ = stderr.read_to_string(&mut s).await;
        s
    });
    let limit_kb = memory_mb.max(1) * 1024;
    let start = Instant::now();
    let mut peak_kb = 0u64;
    let mut tick = tokio::time::interval(Duration::from_millis(50));
    let fail = loop {
        tokio::select! {
            st = child.wait() => {
                let st = st.map_err(|e| NoVerdict::Crashed(e.to_string()))?;
                let out = out_task.await.unwrap_or_default();
                let err = err_task.await.unwrap_or_default();
                let Some(line) = out.lines().find_map(|l| l.strip_prefix("CHECK ")) else {
                    return Err(NoVerdict::Crashed(format!("{st}: {}", err.lines().last().unwrap_or(""))));
                };
                let raw: Raw = serde_json::from_str(line).map_err(|e| NoVerdict::Crashed(format!("bad CHECK line: {e}")))?;
                return Ok(CheckOutcome {
                    ok: raw.ok,
                    axioms: raw.axioms.iter().filter_map(name_of).collect(),
                    public_names: raw.public_names.iter().filter_map(name_of).collect(),
                    target_ok: raw.target_ok,
                    diags: raw.diags,
                    closure: raw.closure,
                });
            }
            _ = tick.tick() => {
                if start.elapsed() >= deadline {
                    break NoVerdict::Timeout;
                }
                let rss = group_rss_kb(pgid);
                peak_kb = peak_kb.max(rss);
                if rss > limit_kb {
                    break NoVerdict::Memory { limit_mb: memory_mb, peak_mb: rss / 1024 };
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
