//! Test harness: a controller and validators in this process, on 127.0.0.1, over a fresh
//! deployment (FDB key root and S3 prefix) of the live cluster of impl/p3/scripts/cluster-up.sh.
//! The validators run impl/p1's real `paralean check-group`, or a wrapper script around it
//! that can instead sleep (timeouts) or allocate (memory limits). Run through
//! impl/p3/scripts/test.sh, which sources scripts/env.sh and builds the P1 stores used here.
#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use paralean_control::checker::{base_id, CheckerConfig};
use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
use paralean_control::validator::{Validator, ValidatorConfig};
use paralean_control::worker::WorkerNode;
use paralean_store::receipt::Policy;
use paralean_store::*;
use paralean_validator_api::rpc;

static COUNTER: AtomicU64 = AtomicU64::new(0);

pub fn repo() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../..").canonicalize().unwrap()
}

/// The P1 store of the core fixtures F01–F13 (impl/p1/scripts/run-core.sh).
pub fn core_store() -> PathBuf {
    let p = std::env::var("PARALEAN_P3_CORE_STORE").map(PathBuf::from).unwrap_or(repo().join(".runs/p1-core/store"));
    assert!(p.join("meta").is_dir(), "no P1 core store at {} (run impl/p3/scripts/test.sh)", p.display());
    p
}

/// A P1 store holding the groups P1 capture rejected for N1–N6 (sorry, a new axiom, a
/// kernel-skipped ill-typed theorem, `native_decide`), moved into the publishable
/// namespace: what a worker that skips validation would try to publish.
pub fn negative_store(into: &Path) -> PathBuf {
    let src = std::env::var("PARALEAN_P3_NEG_RUNS").map(PathBuf::from).unwrap_or(repo().join(".runs/p1-negative"));
    for d in ["objects", "meta", "files"] {
        std::fs::create_dir_all(into.join(d)).unwrap();
    }
    for n in ["N1Sorry", "N2Axiom", "N3SkipKernel", "N6NativeDecide"] {
        let a = src.join(n).join("audit");
        assert!(a.join("meta").is_dir(), "no negative store {} (run impl/p3/scripts/test.sh)", a.display());
        for d in ["objects", "meta"] {
            for e in std::fs::read_dir(a.join(d)).unwrap() {
                let e = e.unwrap();
                std::fs::copy(e.path(), into.join(d).join(e.file_name())).unwrap();
            }
        }
    }
    into.to_path_buf()
}

pub fn deployment(name: &str) -> String {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    format!("p3-{name}-{}-{}-{}", std::process::id(), nanos % 1_000_000_000, COUNTER.fetch_add(1, Ordering::Relaxed))
}

pub fn scratch(name: &str) -> PathBuf {
    let base = std::env::var("TMPDIR").map(PathBuf::from).unwrap_or(std::env::temp_dir());
    let p = base.join(format!("p3test-{}", deployment(name)));
    std::fs::create_dir_all(&p).unwrap();
    p
}

/// A validator's checker: the real P1 binary, or the wrapper in one of its modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Real,
    /// The wrapper, passing through to the real binary.
    Wrapped,
    /// The wrapper, sleeping for a minute.
    Sleep,
    /// The wrapper, allocating and touching 700 MiB.
    Memory,
}

pub struct Opts {
    pub validators: Vec<Mode>,
    pub lease_ms: u64,
    pub max_work_queue: usize,
    pub max_validations: usize,
    pub deadline_ms: u64,
    pub memory_mb: u64,
    pub attempts: usize,
    /// The policy the controller stamps on envelopes.
    pub policy: Policy,
    /// Pinned policies (the controller's is not pinned unless listed).
    pub pinned_policies: Vec<Policy>,
    pub validator_max_running: usize,
    pub validator_max_queued: usize,
}

impl Default for Opts {
    fn default() -> Opts {
        Opts {
            validators: vec![Mode::Real, Mode::Real],
            lease_ms: 2000,
            max_work_queue: 16,
            max_validations: 16,
            deadline_ms: 120_000,
            memory_mb: 4096,
            attempts: 4,
            policy: Policy::v1(),
            pinned_policies: vec![Policy::v1()],
            validator_max_running: 2,
            validator_max_queued: 16,
        }
    }
}

/// A policy stricter than v1: only `propext`.
pub fn strict_policy() -> Policy {
    Policy { allowed_axioms: vec![Name::parse("propext")], check_target_statements: true }
}

pub struct Cluster {
    pub cfg: StoreConfig,
    pub kf: KeyFile,
    pub store: Store,
    pub ctl: Arc<ControlPlane>,
    pub ctl_addr: String,
    pub validators: Vec<Arc<Validator>>,
    pub vaddrs: Vec<String>,
    pub vsigners: Vec<Signer>,
    pub checker: CheckerConfig,
    pub tmp: PathBuf,
    tasks: Vec<tokio::task::JoinHandle<()>>,
    heartbeats: std::sync::Mutex<Vec<tokio::task::JoinHandle<()>>>,
}

impl Drop for Cluster {
    fn drop(&mut self) {
        for t in self.tasks.iter().chain(self.heartbeats.lock().unwrap().iter()) {
            t.abort();
        }
    }
}

fn wrapper(tmp: &Path) -> PathBuf {
    let p = tmp.join("checker-wrapper.sh");
    std::fs::write(
        &p,
        "#!/usr/bin/env bash\n\
         # P3 test checker: the real check-group, or a misbehaving stand-in.\n\
         case \"${PARALEAN_FAKE_CHECKER:-real}\" in\n\
         \x20 sleep) sleep 60 ;;\n\
         \x20 memory) exec python3 -c 'import time; x = b\"x\" * (700 * 2**20); time.sleep(60)' ;;\n\
         \x20 *) exec \"$PARALEAN_REAL_BIN\" \"$@\" ;;\n\
         esac\n",
    )
    .unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o755)).unwrap();
    p
}

pub fn validator_signer(i: usize) -> Signer {
    Signer::derive(&format!("p3-validator-{i}"))
}

impl Cluster {
    pub async fn start(name: &str, o: Opts) -> Cluster {
        let cfg = StoreConfig::from_env(&deployment(name))
            .expect("PARALEAN_* not set: run through impl/p3/scripts/test.sh after scripts/cluster-up.sh");
        let tmp = scratch(name);
        let real = CheckerConfig::from_env().expect("checker config (PARALEAN_BIN)");
        let wrapped = o.validators.iter().any(|m| *m != Mode::Real);
        let mut checker = real.clone();
        if wrapped {
            checker.bin = wrapper(&tmp);
            checker.env.push(("PARALEAN_REAL_BIN".into(), real.bin.display().to_string()));
        }
        let checker_id = checker.version().unwrap().id();
        let mut kf = KeyFile::demo(6);
        kf.validators.clear();
        let vsigners: Vec<Signer> = (0..o.validators.len().max(1)).map(validator_signer).collect();
        for (i, s) in vsigners.iter().enumerate() {
            kf.add_validator(&format!("v{i}"), s);
        }
        kf.policies = o.pinned_policies.iter().map(|p| p.id().hex()).collect();
        kf.checkers = vec![checker_id.hex()];
        let store = Store::open(&cfg, kf.ring(), Faults::none()).unwrap();
        let base = base_id(&real.lean_githash);
        let mut tasks = Vec::new();
        let mut validators = Vec::new();
        let mut vaddrs = Vec::new();
        for (i, mode) in o.validators.iter().enumerate() {
            let mut c = checker.clone();
            let m = match mode {
                Mode::Sleep => "sleep",
                Mode::Memory => "memory",
                _ => "real",
            };
            c.env.push(("PARALEAN_FAKE_CHECKER".into(), m.into()));
            let v = Validator::new(ValidatorConfig {
                store: store.clone(),
                signer: vsigners[i].clone(),
                checker: c,
                base,
                policies: vec![Policy::v1(), strict_policy()],
                max_running: o.validator_max_running,
                max_queued: o.validator_max_queued,
                workdir: tmp.join(format!("validator-{i}")),
            })
            .unwrap();
            let l = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
            vaddrs.push(l.local_addr().unwrap().to_string());
            tasks.push(v.serve(l));
            validators.push(v);
        }
        let ctl = ControlPlane::new(ControllerConfig {
            store: store.clone(),
            authority: kf.authority_signer().unwrap(),
            validators: vaddrs.clone(),
            base,
            policy: o.policy.id(),
            checker: checker_id,
            lease: Duration::from_millis(o.lease_ms),
            max_work_queue: o.max_work_queue,
            max_validations: o.max_validations,
            validation_deadline: Duration::from_millis(o.deadline_ms),
            validation_memory_mb: o.memory_mb,
            validator_attempts: o.attempts,
        });
        let l = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let ctl_addr = l.local_addr().unwrap().to_string();
        tasks.push(ctl.serve(l));
        Cluster { cfg, kf, store, ctl, ctl_addr, validators, vaddrs, vsigners, checker, tmp, tasks, heartbeats: Default::default() }
    }

    pub fn writer(&self, i: usize) -> Writer {
        let (id, s) = self.kf.workspace(&format!("w{i}")).unwrap();
        Writer::new(self.store.clone(), id, s)
    }

    /// A worker over `p1_store`, registered, renewing its lease until the cluster drops.
    pub async fn worker(&self, i: usize, capacity_mb: u64, p1_store: &Path) -> Arc<WorkerNode> {
        let w = self.worker_without_heartbeat(i, capacity_mb, p1_store).await;
        self.heartbeats.lock().unwrap().push(w.spawn_heartbeats(Duration::from_millis(250)));
        w
    }

    /// A registered worker whose lease nobody renews (the caller spawns heartbeats).
    pub async fn worker_without_heartbeat(&self, i: usize, capacity_mb: u64, p1_store: &Path) -> Arc<WorkerNode> {
        let w = WorkerNode::new(self.writer(i), &self.ctl_addr, capacity_mb, p1_store).unwrap();
        assert!(matches!(w.register().await.unwrap(), ControlResponse::Registered { .. }));
        w
    }

    pub async fn call(&self, req: ControlRequest) -> ControlResponse {
        rpc::call(&self.ctl_addr, &req, Duration::from_secs(600)).await.unwrap()
    }

    /// The same deployment seen through another key ring (rotation, retirement).
    pub fn store_with_ring(&self, ring: KeyRing) -> Store {
        Store::open(&self.cfg, ring, Faults::none()).unwrap()
    }

    pub async fn audit_ok(&self) -> audit::AuditReport {
        let r = audit::audit(&self.store).await.expect("audit runs");
        r.assert_ok();
        r
    }

    pub async fn assign(&self, target: &str, worker: WorkspaceId) -> u64 {
        match self.call(ControlRequest::Assign { target: target.into(), worker: worker.hex() }).await {
            ControlResponse::Assigned { epoch } => epoch,
            other => panic!("assign: {other:?}"),
        }
    }
}

pub fn guard<T: std::fmt::Debug>(r: Result<T>) -> GuardFailure {
    match r {
        Err(StoreError::Guard(g)) => g,
        other => panic!("expected a guard failure, got {other:?}"),
    }
}

pub async fn published(store: &Store, g: &Id) -> bool {
    store.marker(g).await.unwrap().is_some()
}
