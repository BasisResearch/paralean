//! The validator service.
//!
//! It takes a controller-signed job envelope, refuses envelopes it cannot honour (wrong
//! signature, checker version, policy or base; its own key revoked; the request cancelled;
//! a dependency not published with a valid receipt), rebuilds a P1 store holding exactly the
//! group and its dependency closure from the P2 payload store (every object re-hashed),
//! runs `paralean check-group` on it, and signs a receipt bound to the envelope. Deadline,
//! memory limit, checker crash, cancellation and unavailable bytes give no receipt.
//!
//! Requests are deduplicated by request ID: a duplicate of a running check waits for the
//! same result, a recent finished check gets the same receipt, and a request ID
//! reused with another envelope is refused while retained. The last 256 completed
//! receipts stay in memory; older retries are checked anew. Inconclusive results are not kept, so a retry
//! checks again. At most `max_running` checks run at once and at most `max_queued` wait;
//! beyond that the answer is `Busy`.

use std::collections::{BTreeMap, HashMap, VecDeque};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use paralean_store::receipt::{target_slot, Policy, SignedJob};
use paralean_store::{Id, Kind, Object, Receipt, ReceiptBody, Signer, Store, Verdict, WorkspaceId};
use paralean_validator_api::{published_receipt, ValidatorRequest, ValidatorResponse};
use tokio::net::TcpListener;
use tokio::sync::{watch, Semaphore};
use tokio::task::JoinHandle;

use crate::checker::{self, CheckerConfig, NoVerdict, TargetArg};
use crate::p1::{self, P1Group};

#[derive(Clone)]
pub struct ValidatorConfig {
    pub store: Store,
    pub signer: Signer,
    pub checker: CheckerConfig,
    /// The base this validator checks against (`base:…`).
    pub base: Id,
    /// Policies this validator enforces, by ID.
    pub policies: Vec<Policy>,
    pub max_running: usize,
    pub max_queued: usize,
    /// Per-job scratch directories go here.
    pub workdir: PathBuf,
}

struct Slot {
    job: Id,
    worker: WorkspaceId,
    request: Vec<u8>,
    result: watch::Receiver<Option<ValidatorResponse>>,
    cancel: watch::Sender<bool>,
}

pub struct Validator {
    cfg: ValidatorConfig,
    checker_id: Id,
    slots: Mutex<HashMap<Vec<u8>, Slot>>,
    completed: Mutex<VecDeque<Vec<u8>>>,
    permits: Semaphore,
    queued: AtomicUsize,
    running: AtomicUsize,
    /// Checks that ran the checker to a verdict (for deduplication tests).
    pub checks_run: AtomicU64,
    pub warm_pool: checker::WarmPool,
}

impl Validator {
    pub fn new(cfg: ValidatorConfig) -> Result<Arc<Validator>, String> {
        let checker_id = cfg.checker.version()?.id();
        prepare_workdir(&cfg.workdir)?;
        Ok(Arc::new(Validator {
            permits: Semaphore::new(cfg.max_running.max(1)),
            cfg,
            checker_id,
            slots: Mutex::new(HashMap::new()),
            completed: Mutex::new(VecDeque::new()),
            queued: AtomicUsize::new(0),
            running: AtomicUsize::new(0),
            checks_run: AtomicU64::new(0),
            warm_pool: checker::WarmPool::default(),
        }))
    }

    pub fn checker_id(&self) -> Id {
        self.checker_id
    }
    pub fn key(&self) -> [u8; 32] {
        self.cfg.signer.public()
    }

    /// Serve on `listener`.
    pub fn serve(self: &Arc<Self>, listener: TcpListener) -> JoinHandle<()> {
        let v = self.clone();
        let ring = self.cfg.store.ring.clone();
        crate::server::serve_authenticated(listener, self.cfg.signer.clone(), move |req: &ValidatorRequest, key: &[u8;32]| {
            if key == &ring.authority { return true; }
            if !ring.job_issuers.contains(key) { return false; }
            let issued = |encoded: &String| {
                hex::decode(encoded).ok().and_then(|b| SignedJob::from_bytes(&b).ok())
                    .map(|j| j.verify(key)).unwrap_or(false)
            };
            match req {
                ValidatorRequest::Validate { job } => issued(job),
                ValidatorRequest::ValidateBatch { jobs } => jobs.iter().all(issued),
                _ => false,
            }
        }, move |req: ValidatorRequest| {
            let v = v.clone();
            async move { v.handle(req).await }
        })
    }

    pub async fn handle(self: &Arc<Self>, req: ValidatorRequest) -> ValidatorResponse {
        match req {
            ValidatorRequest::Validate { job } => {
                let job = match hex::decode(&job).ok().and_then(|b| SignedJob::from_bytes(&b).ok()) {
                    Some(j) => j,
                    None => return refused("undecodable envelope"),
                };
                self.validate(job).await
            }
            ValidatorRequest::ValidateBatch { jobs } => {
                if jobs.is_empty() || jobs.len() > 64 {
                    return refused("batch must contain 1 to 64 jobs");
                }
                let me = self.clone();
                self.detached(async move { me.validate_batch(jobs).await }).await
            }
            ValidatorRequest::Cancel { request, worker } => {
                let Ok(r) = hex::decode(&request) else { return refused("bad request ID") };
                let worker = if worker.is_empty() { None } else {
                    match WorkspaceId::from_hex(&worker) { Some(w) => Some(w), None => return refused("bad worker ID") }
                };
                for s in self.slots.lock().unwrap().values() {
                    if s.request == r && worker.is_none_or(|w| w == s.worker) {
                        let _ = s.cancel.send(true);
                    }
                }
                ValidatorResponse::Cancelled
            }
            ValidatorRequest::Status => ValidatorResponse::Status {
                key: hex::encode(self.key()),
                checker: self.checker_id.hex(),
                running: self.running.load(Ordering::SeqCst),
                queued: self.queued.load(Ordering::SeqCst),
                checks_run: self.checks_run.load(Ordering::SeqCst),
            },
        }
    }

    /// Check one envelope (deduplicated by request ID).
    ///
    /// The check runs in its own task: when the caller's future is dropped (the RPC
    /// server's execution limit, a client that went away) the check still finishes, its
    /// result lands in the request's slot for a retry, and its counters and scratch
    /// directory are released by the check itself.
    pub async fn validate(self: &Arc<Self>, job: SignedJob) -> ValidatorResponse {
        let me = self.clone();
        self.detached(async move { me.validate_with_dependencies(job, &BTreeMap::new()).await }).await
    }

    async fn detached<F>(&self, check: F) -> ValidatorResponse
    where F: std::future::Future<Output = ValidatorResponse> + Send + 'static {
        if cfg!(feature = "mutate-attached-validation") {
            return check.await;
        }
        tokio::spawn(check).await.unwrap_or_else(|e| inconclusive(&format!("check task failed: {e}")))
    }

    /// A dependency-ordered batch: earlier accepted receipts may serve later jobs.
    async fn validate_batch(self: &Arc<Self>, jobs: Vec<String>) -> ValidatorResponse {
        let mut accepted = BTreeMap::new();
        let mut responses = Vec::with_capacity(jobs.len());
        for encoded in jobs {
            let job = match hex::decode(&encoded).ok().and_then(|b| SignedJob::from_bytes(&b).ok()) {
                Some(j) => j,
                None => { responses.push(refused("undecodable envelope")); continue; }
            };
            let response = self.validate_with_dependencies(job.clone(), &accepted).await;
            if let ValidatorResponse::Receipt { receipt } = &response {
                if let Ok(r) = paralean_validator_api::decode_receipt(receipt) {
                    if r.body.verdict == Verdict::Accepted {
                        // Distinct replay capsules can encode the same group.
                        // Dependencies name the capsule, so retain each receipt.
                        accepted.insert(job.body.capsule, (r, job));
                    }
                }
            }
            responses.push(response);
        }
        ValidatorResponse::Batch { responses }
    }

    async fn validate_with_dependencies(
        self: &Arc<Self>, job: SignedJob, accepted: &BTreeMap<Id, (Receipt, SignedJob)>,
    ) -> ValidatorResponse {
        let ring = self.cfg.store.ring.clone();
        let relaxed = cfg!(feature = "mutate-relaxed-envelope-sig");
        let issued = |key: &[u8; 32]| paralean_store::sign::verify_path(relaxed, key, &job.id(), &job.sig);
        let Some(issuer) = std::iter::once(&ring.authority).chain(ring.job_issuers.iter()).find(|k| issued(k)).copied() else {
            return refused("envelope is not signed by the controller");
        };
        let j = &job.body;
        // An issuer-signed envelope that binds targets can never stage (the staging rule and
        // T1 refuse it), so checking it would only spend this validator's capacity.
        if !j.targets.is_empty() && issuer != ring.authority && !cfg!(feature = "mutate-validator-checks-issuer-targets") {
            return refused("a job-issuer envelope cannot bind targets; only the controller's can");
        }
        if j.checker != self.checker_id {
            return refused(&format!("envelope names checker {}, this validator runs {}", j.checker.short(), self.checker_id.short()));
        }
        let Some(policy) = self.cfg.policies.iter().find(|p| p.id() == j.policy).cloned() else {
            return refused(&format!("policy {} is not enforced here", j.policy.short()));
        };
        if j.base != self.cfg.base {
            return refused("envelope names another base");
        }
        // Request IDs belong to the requesting workspace and the envelope's issuer: a slot
        // is (issuer key, workspace, request), so no workspace or issuer can occupy another's.
        let request = slot_key(&issuer, &j.worker, &j.request);
        enum Pre {
            Wait(watch::Receiver<Option<ValidatorResponse>>),
            Run(watch::Sender<Option<ValidatorResponse>>, watch::Receiver<bool>),
            Answer(ValidatorResponse),
        }
        let (tx, cancel_rx) = loop {
            let pre = {
                let mut slots = self.slots.lock().unwrap();
                match slots.get(&request) {
                    Some(s) if s.job != job.id() => Pre::Answer(refused("request ID already used for another envelope")),
                    Some(s) => Pre::Wait(s.result.clone()),
                    None if self.queued.load(Ordering::SeqCst) >= self.cfg.max_queued && self.permits.available_permits() == 0 => {
                        Pre::Answer(ValidatorResponse::Busy)
                    }
                    None => {
                        let (tx, rx) = watch::channel(None);
                        let (ctx, crx) = watch::channel(false);
                        slots.insert(request.clone(), Slot { job: job.id(), worker: j.worker, request: j.request.clone(), result: rx, cancel: ctx });
                        Pre::Run(tx, crx)
                    }
                }
            };
            match pre {
                Pre::Answer(r) => return r,
                Pre::Wait(mut rx) => {
                    let shared = loop {
                        if let Some(r) = rx.borrow().clone() {
                            break r;
                        }
                        if rx.changed().await.is_err() {
                            break ValidatorResponse::Inconclusive { reason: "check abandoned".into() };
                        }
                    };
                    // A standalone retry may have checked this job without the
                    // earlier batch receipts. Reacquire the slot so cancellation
                    // and request deduplication still apply to our own check.
                    if matches!(shared, ValidatorResponse::Refused { .. }) &&
                        j.deps.iter().any(|cap| accepted.contains_key(cap)) {
                        continue;
                    }
                    return shared;
                }
                Pre::Run(tx, crx) => break (tx, crx),
            }
        };
        // Should this future be dropped before an answer, the slot goes with it, so the
        // request ID is not held by a check that no longer runs.
        let slot = SlotGuard { slots: &self.slots, key: Some(request.clone()) };
        let r = self.process(&job, &policy, cancel_rx, accepted).await;
        slot.release();
        if !matches!(r, ValidatorResponse::Receipt { .. }) {
            // Only receipts are kept: a retry of anything else checks again.
            self.slots.lock().unwrap().remove(&request);
        }
        let _ = tx.send(Some(r.clone()));
        if matches!(r, ValidatorResponse::Receipt { .. }) {
            let mut completed = self.completed.lock().unwrap();
            let mut slots = self.slots.lock().unwrap();
            retain_completed(&mut slots, &mut completed, request);
        }
        r
    }

    async fn process(self: &Arc<Self>, job: &SignedJob, policy: &Policy, mut cancel: watch::Receiver<bool>,
        accepted: &BTreeMap<Id, (Receipt, SignedJob)>) -> ValidatorResponse {
        let st = &self.cfg.store;
        let j = &job.body;
        match st.meta.is_revoked(&self.key()).await {
            Ok(false) => {}
            Ok(true) => return refused("this validator's key is revoked"),
            Err(e) => return inconclusive(&format!("store: {e}")),
        }
        match st.meta.is_cancelled(&j.worker, &j.request).await {
            Ok(false) => {}
            Ok(true) => return ValidatorResponse::Cancelled,
            Err(e) => return inconclusive(&format!("store: {e}")),
        }
        // The gauges count down when dropped, also if this future is.
        let queued = Gauge::up(&self.queued);
        let permit = tokio::select! {
            p = self.permits.acquire() => p,
            _ = cancel.changed() => return ValidatorResponse::Cancelled,
        };
        drop(queued);
        let _permit = permit.expect("semaphore open");
        let _running = Gauge::up(&self.running);
        self.check(job, policy, cancel, accepted).await
    }

    /// Fetch the inputs, run the checker and sign.
    async fn check(&self, job: &SignedJob, policy: &Policy, cancel: watch::Receiver<bool>,
        accepted: &BTreeMap<Id, (Receipt, SignedJob)>) -> ValidatorResponse {
        let j = &job.body;
        let groups = match self.fetch_inputs(job, accepted).await {
            Ok(g) => g,
            Err(r) => return r,
        };
        let root = groups.last().expect("fetch_inputs returns the group last").clone();
        let by_gid: BTreeMap<String, P1Group> = groups.iter().map(|g| (g.gid.clone(), g.clone())).collect();
        if by_gid.len() != groups.len() {
            return refused("two capsules of the job name the same package ID");
        }
        if let Err(e) = p1::closure(&by_gid, &root.gid) {
            return refused(&format!("dependency closure incomplete: {e}"));
        }
        // A fresh private directory per check (`write_store` refuses an existing one).
        let dir = self.cfg.workdir.join(format!("job-{}-{:016x}", job.id().hex(), rand::random::<u64>()));
        if let Err(e) = p1::write_store(&dir, &groups) {
            // Never remove a directory this check did not create.
            if e.kind() != std::io::ErrorKind::AlreadyExists { let _ = std::fs::remove_dir_all(&dir); }
            return inconclusive(&format!("scratch store: {e}"));
        }
        let scratch = Scratch(dir.clone());
        let gids: Vec<String> = groups.iter().map(|g| g.gid.clone()).collect();
        // Each target must be declared; its statement is compared when the policy says so.
        let targets: Vec<TargetArg> = j
            .targets
            .iter()
            .map(|t| TargetArg {
                name: t.name.clone(),
                statement: if policy.check_target_statements { hex::encode(&t.statement) } else { String::new() },
            })
            .collect();
        let deadline = Duration::from_millis(if j.deadline_ms == 0 { 600_000 } else { j.deadline_ms.min(600_000) });
        let memory = if j.memory_mb == 0 { self.cfg.checker.default_memory_mb } else { j.memory_mb }.min(16 * 1024);
        // Materialized initializers load process-global code. Keep such jobs in a
        // disposable checker; only immutable pinned base imports persist in the pool.
        let initializer = groups.iter().any(|g| {
            let s = String::from_utf8_lossy(&g.meta_json);
            s.contains("regularInitAttr") || s.contains("builtinInitAttr")
        });
        let out = if self.cfg.checker.warm_bin().is_some() {
            if initializer {
                let disposable = checker::WarmPool::default();
                let out = disposable.run(&self.cfg.checker, &dir, &gids, &root.decl.hex(), &targets, deadline, memory, cancel).await;
                self.warm_pool.spawned.fetch_add(disposable.spawned.load(Ordering::Relaxed), Ordering::Relaxed);
                self.warm_pool.peak_rss_kb.fetch_max(disposable.peak_rss_kb.load(Ordering::Relaxed), Ordering::Relaxed);
                out
            } else {
                self.warm_pool.run(&self.cfg.checker, &dir, &gids, &root.decl.hex(), &targets, deadline, memory, cancel).await
            }
        } else {
            checker::run(&self.cfg.checker, &dir, &gids, &root.decl.hex(), &targets, deadline, memory, cancel).await
        };
        drop(scratch);
        let o = match out {
            Ok(o) => o,
            Err(NoVerdict::Cancelled) => return ValidatorResponse::Cancelled,
            Err(e) => return inconclusive(&e.to_string()),
        };
        self.checks_run.fetch_add(1, Ordering::SeqCst);
        let mut reasons: Vec<String> = Vec::new();
        if !o.ok {
            reasons.push(format!("check failed: {}", o.diags.join(" | ")));
        }
        if !cfg!(feature = "mutate-validator-ignores-axioms") {
            for a in &o.axioms {
                if !policy.allowed_axioms.contains(a) {
                    reasons.push(format!("axiom {a} is not allowed by policy {}", policy.id().short()));
                }
            }
        }
        if !j.targets.is_empty() && o.target_ok != Some(true) {
            reasons.push("a pinned target is not declared with its statement".into());
        }
        let verdict = if reasons.is_empty() {
            Verdict::Accepted
        } else {
            let mut s = reasons.join("; ");
            s.truncate(2000);
            Verdict::Rejected(s)
        };
        let mut axioms = o.axioms.clone();
        axioms.sort_by_key(paralean_store::pce::Pce::to_pce);
        axioms.dedup();
        let receipt = Receipt::sign(
            ReceiptBody {
                group: j.group,
                base: j.base,
                validator_key: self.key(),
                validator_bin: self.checker_id.0.to_vec(),
                policy: j.policy,
                request: Some(job.id().0.to_vec()),
                target: target_slot(&j.targets),
                verdict,
                axioms,
            },
            &self.cfg.signer,
        );
        ValidatorResponse::Receipt { receipt: hex::encode(receipt.to_bytes()) }
    }

    /// The group and its dependencies (dependencies first, the group last), each read from
    /// the payload store and re-hashed. Every dependency must be published with a receipt
    /// that verifies now; the validator never checks against unvalidated groups.
    async fn fetch_inputs(&self, job: &SignedJob, accepted: &BTreeMap<Id, (Receipt, SignedJob)>) -> Result<Vec<P1Group>, ValidatorResponse> {
        let st = &self.cfg.store;
        let j = &job.body;
        let mut out = Vec::new();
        for (i, cap) in j.deps.iter().chain(std::iter::once(&j.capsule)).enumerate() {
            let is_root = i == j.deps.len();
            let meta_json = match st.s3.get(Kind::Capsule, cap).await {
                Ok(Some(pre)) => match Kind::Capsule.domain().strip(&pre) {
                    Ok(b) => b.to_vec(),
                    Err(_) => return Err(inconclusive("capsule bytes undecodable")),
                },
                Ok(None) => return Err(inconclusive(&format!("capsule {} unavailable", cap.short()))),
                Err(e) => return Err(inconclusive(&format!("payload store: {e}"))),
            };
            let decl = match serde_json::from_slice::<serde_json::Value>(&meta_json)
                .ok()
                .and_then(|m| m["declId"].as_str().and_then(Id::from_hex))
            {
                Some(d) => d,
                None => return Err(refused(&format!("capsule {} is not P1 group metadata", cap.short()))),
            };
            if is_root && decl != j.group {
                return Err(refused("the capsule describes another group"));
            }
            let grp = match st.s3.get(Kind::Group, &decl).await {
                Ok(Some(pre)) => match Kind::Group.domain().strip(&pre) {
                    Ok(b) => b.to_vec(),
                    Err(_) => return Err(inconclusive("group bytes undecodable")),
                },
                Ok(None) => return Err(inconclusive(&format!("group {} unavailable", decl.short()))),
                Err(e) => return Err(inconclusive(&format!("payload store: {e}"))),
            };
            let g = P1Group::from_parts(meta_json, grp).map_err(|e| refused(&e))?;
            if !is_root && !cfg!(feature = "mutate-validator-skips-dep-check") {
                if let Some((r, dep_job)) = accepted.get(cap) {
                    if dep_job.body.capsule != *cap ||
                        paralean_store::receipt::check(r, dep_job, &decl,
                            &paralean_store::receipt::prepared_of(dep_job), &st.ring).is_err() ||
                        st.meta.is_revoked(&r.body.validator_key).await.unwrap_or(true) ||
                        st.meta.is_cancelled(&dep_job.body.worker, &dep_job.body.request).await.unwrap_or(true) {
                        return Err(refused("batch dependency receipt does not verify"));
                    }
                } else if let Err(e) = published_receipt(st, &decl).await {
                    return Err(refused(&format!("dependency {} has no valid published or earlier batch receipt: {e:?}", decl.short())));
                }
            }
            out.push(g);
        }
        Ok(out)
    }
}

/// The validator writes scratch stores outside the checker sandbox under `dir`: it must be
/// a real directory (not a symlink) owned by this user and closed to everyone else. A
/// missing one is created 0700; one of ours that is open to others is narrowed to 0700.
/// One owned by someone else (a planted `/tmp/...`) is refused.
pub fn prepare_workdir(dir: &std::path::Path) -> Result<(), String> {
    use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
    let shown = dir.display();
    if !dir.exists() && std::fs::symlink_metadata(dir).is_err() {
        std::fs::DirBuilder::new().recursive(true).mode(0o700).create(dir).map_err(|e| format!("validator workdir {shown}: {e}"))?;
    }
    if cfg!(feature = "mutate-shared-workdir") {
        return Ok(());
    }
    let m = std::fs::symlink_metadata(dir).map_err(|e| format!("validator workdir {shown}: {e}"))?;
    if m.file_type().is_symlink() || !m.is_dir() {
        return Err(format!("validator workdir {shown} is not a directory (a symlink is refused)"));
    }
    // SAFETY: geteuid has no preconditions.
    if m.uid() != unsafe { libc::geteuid() } {
        return Err(format!("validator workdir {shown} is owned by uid {}, not this user", m.uid()));
    }
    if m.mode() & 0o077 != 0 {
        std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o700)).map_err(|e| format!("validator workdir {shown}: {e}"))?;
    }
    Ok(())
}

/// A count held while this value lives (queued or running checks).
struct Gauge<'a>(&'a AtomicUsize);

impl<'a> Gauge<'a> {
    fn up(count: &'a AtomicUsize) -> Gauge<'a> {
        count.fetch_add(1, Ordering::SeqCst);
        Gauge(count)
    }
}

impl Drop for Gauge<'_> {
    fn drop(&mut self) { self.0.fetch_sub(1, Ordering::SeqCst); }
}

/// A check's scratch store, removed when the check ends however it ends.
struct Scratch(PathBuf);

impl Drop for Scratch {
    fn drop(&mut self) { let _ = std::fs::remove_dir_all(&self.0); }
}

/// Removes the slot of a check that stopped before giving an answer.
struct SlotGuard<'a> {
    slots: &'a Mutex<HashMap<Vec<u8>, Slot>>,
    key: Option<Vec<u8>>,
}

impl SlotGuard<'_> {
    fn release(mut self) { self.key = None; }
}

impl Drop for SlotGuard<'_> {
    fn drop(&mut self) {
        if let Some(key) = self.key.take() {
            if let Ok(mut slots) = self.slots.lock() { slots.remove(&key); }
        }
    }
}

/// The deduplication slot of a request: (envelope issuer, requesting workspace, request ID).
fn slot_key(issuer: &[u8; 32], worker: &WorkspaceId, request: &[u8]) -> Vec<u8> {
    if cfg!(feature = "mutate-unscoped-validator-slots") {
        return request.to_vec();
    }
    let mut k = issuer.to_vec();
    k.extend_from_slice(&worker.0);
    k.extend_from_slice(request);
    k
}

fn retain_completed<V>(slots: &mut HashMap<Vec<u8>, V>, completed: &mut VecDeque<Vec<u8>>, request: Vec<u8>) {
    completed.push_back(request);
    if !cfg!(feature = "mutate-unbounded-completed-slots") {
        while completed.len() > 256 {
            if let Some(old) = completed.pop_front() { slots.remove(&old); }
        }
    }
}

#[cfg(test)]
mod completed_tests {
    use super::*;

    #[test]
    fn completed_receipt_cache_is_bounded() {
        let mut slots = HashMap::new();
        let mut order = VecDeque::new();
        for id in 0..300u16 {
            let key = id.to_be_bytes().to_vec();
            slots.insert(key.clone(), id);
            retain_completed(&mut slots, &mut order, key);
        }
        assert_eq!(slots.len(), 256);
        assert_eq!(order.len(), 256);
        assert!(!slots.contains_key(&0u16.to_be_bytes().to_vec()));
        assert!(slots.contains_key(&299u16.to_be_bytes().to_vec()));
    }

    #[test]
    fn validator_workdir_must_be_private_and_ours() {
        use std::os::unix::fs::PermissionsExt;
        let base = std::env::temp_dir().join(format!("validator-workdir-test-{}-{}", std::process::id(), rand::random::<u64>()));
        let mode = |p: &std::path::Path| std::fs::metadata(p).unwrap().permissions().mode() & 0o777;
        // Missing: created private.
        let fresh = base.join("a/b");
        prepare_workdir(&fresh).unwrap();
        assert_eq!(mode(&fresh), 0o700);
        // Ours but open: narrowed.
        let open = base.join("open");
        std::fs::create_dir_all(&open).unwrap();
        std::fs::set_permissions(&open, std::fs::Permissions::from_mode(0o777)).unwrap();
        prepare_workdir(&open).unwrap();
        assert_eq!(mode(&open), 0o700);
        // A symlink (even to a private directory of ours) and a file are refused.
        let link = base.join("link");
        std::os::unix::fs::symlink(&fresh, &link).unwrap();
        assert!(prepare_workdir(&link).is_err(), "symlinked workdir accepted");
        let file = base.join("file");
        std::fs::write(&file, b"").unwrap();
        assert!(prepare_workdir(&file).is_err(), "file accepted as workdir");
        // Someone else's directory (root's, unless the tests run as root).
        if unsafe { libc::geteuid() } != 0 {
            assert!(prepare_workdir(std::path::Path::new("/")).is_err(), "a directory owned by root accepted");
        }
        std::fs::remove_dir_all(&base).unwrap();
    }
}

fn refused(reason: &str) -> ValidatorResponse {
    ValidatorResponse::Refused { reason: reason.into() }
}
fn inconclusive(reason: &str) -> ValidatorResponse {
    ValidatorResponse::Inconclusive { reason: reason.into() }
}
