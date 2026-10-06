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
//! same result, a duplicate of a finished check gets the same receipt, and a request ID
//! reused with another envelope is refused. Inconclusive results are not kept, so a retry
//! checks again. At most `max_running` checks run at once and at most `max_queued` wait;
//! beyond that the answer is `Busy`.

use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use paralean_store::receipt::{target_slot, Policy, SignedJob};
use paralean_store::{Id, Kind, Object, Receipt, ReceiptBody, Signer, Store, Verdict};
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
    result: watch::Receiver<Option<ValidatorResponse>>,
    cancel: watch::Sender<bool>,
}

pub struct Validator {
    cfg: ValidatorConfig,
    checker_id: Id,
    slots: Mutex<HashMap<Vec<u8>, Slot>>,
    permits: Semaphore,
    queued: AtomicUsize,
    running: AtomicUsize,
    /// Checks that ran the checker to a verdict (for deduplication tests).
    pub checks_run: AtomicU64,
}

impl Validator {
    pub fn new(cfg: ValidatorConfig) -> Result<Arc<Validator>, String> {
        let checker_id = cfg.checker.version()?.id();
        std::fs::create_dir_all(&cfg.workdir).map_err(|e| e.to_string())?;
        Ok(Arc::new(Validator {
            permits: Semaphore::new(cfg.max_running.max(1)),
            cfg,
            checker_id,
            slots: Mutex::new(HashMap::new()),
            queued: AtomicUsize::new(0),
            running: AtomicUsize::new(0),
            checks_run: AtomicU64::new(0),
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
        crate::server::serve(listener, move |req: ValidatorRequest| {
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
            ValidatorRequest::Cancel { request } => {
                let Ok(r) = hex::decode(&request) else { return refused("bad request ID") };
                if let Some(s) = self.slots.lock().unwrap().get(&r) {
                    let _ = s.cancel.send(true);
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
    pub async fn validate(self: &Arc<Self>, job: SignedJob) -> ValidatorResponse {
        let ring = self.cfg.store.ring.clone();
        if !job.issued_by(&ring) {
            return refused("envelope is not signed by the controller");
        }
        let j = &job.body;
        if j.checker != self.checker_id {
            return refused(&format!("envelope names checker {}, this validator runs {}", j.checker.short(), self.checker_id.short()));
        }
        let Some(policy) = self.cfg.policies.iter().find(|p| p.id() == j.policy).cloned() else {
            return refused(&format!("policy {} is not enforced here", j.policy.short()));
        };
        if j.base != self.cfg.base {
            return refused("envelope names another base");
        }
        let request = j.request.clone();
        enum Pre {
            Wait(watch::Receiver<Option<ValidatorResponse>>),
            Run(watch::Sender<Option<ValidatorResponse>>, watch::Receiver<bool>),
            Answer(ValidatorResponse),
        }
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
                    slots.insert(request.clone(), Slot { job: job.id(), result: rx, cancel: ctx });
                    Pre::Run(tx, crx)
                }
            }
        };
        let (tx, cancel_rx) = match pre {
            Pre::Answer(r) => return r,
            Pre::Wait(mut rx) => {
                return loop {
                    if let Some(r) = rx.borrow().clone() {
                        break r;
                    }
                    if rx.changed().await.is_err() {
                        break ValidatorResponse::Inconclusive { reason: "check abandoned".into() };
                    }
                }
            }
            Pre::Run(tx, crx) => (tx, crx),
        };
        let r = self.process(&job, &policy, cancel_rx).await;
        let _ = tx.send(Some(r.clone()));
        if !matches!(r, ValidatorResponse::Receipt { .. }) {
            // Only receipts are kept: a retry of anything else checks again.
            self.slots.lock().unwrap().remove(&request);
        }
        r
    }

    async fn process(self: &Arc<Self>, job: &SignedJob, policy: &Policy, mut cancel: watch::Receiver<bool>) -> ValidatorResponse {
        let st = &self.cfg.store;
        let j = &job.body;
        match st.meta.is_revoked(&self.key()).await {
            Ok(false) => {}
            Ok(true) => return refused("this validator's key is revoked"),
            Err(e) => return inconclusive(&format!("store: {e}")),
        }
        match st.meta.is_cancelled(&j.request).await {
            Ok(false) => {}
            Ok(true) => return ValidatorResponse::Cancelled,
            Err(e) => return inconclusive(&format!("store: {e}")),
        }
        self.queued.fetch_add(1, Ordering::SeqCst);
        let permit = tokio::select! {
            p = self.permits.acquire() => p,
            _ = cancel.changed() => {
                self.queued.fetch_sub(1, Ordering::SeqCst);
                return ValidatorResponse::Cancelled;
            }
        };
        self.queued.fetch_sub(1, Ordering::SeqCst);
        let _permit = permit.expect("semaphore open");
        self.running.fetch_add(1, Ordering::SeqCst);
        let r = self.check(job, policy, cancel).await;
        self.running.fetch_sub(1, Ordering::SeqCst);
        r
    }

    /// Fetch the inputs, run the checker and sign.
    async fn check(&self, job: &SignedJob, policy: &Policy, cancel: watch::Receiver<bool>) -> ValidatorResponse {
        let j = &job.body;
        let groups = match self.fetch_inputs(job).await {
            Ok(g) => g,
            Err(r) => return r,
        };
        let root = groups.last().expect("fetch_inputs returns the group last").clone();
        let by_gid: BTreeMap<String, P1Group> = groups.iter().map(|g| (g.gid.clone(), g.clone())).collect();
        if let Err(e) = p1::closure(&by_gid, &root.gid) {
            return refused(&format!("dependency closure incomplete: {e}"));
        }
        let dir = self.cfg.workdir.join(format!("job-{}-{}", job.id().hex(), rand::random::<u32>()));
        if let Err(e) = p1::write_store(&dir, &groups) {
            return inconclusive(&format!("scratch store: {e}"));
        }
        let gids: Vec<String> = groups.iter().map(|g| g.gid.clone()).collect();
        let targets: Vec<TargetArg> =
            j.targets.iter().map(|t| TargetArg { name: t.name.clone(), statement: hex::encode(&t.statement) }).collect();
        let deadline = Duration::from_millis(if j.deadline_ms == 0 { 600_000 } else { j.deadline_ms });
        let memory = if j.memory_mb == 0 { self.cfg.checker.default_memory_mb } else { j.memory_mb };
        let out = checker::run(&self.cfg.checker, &dir, &gids, &root.decl.hex(), &targets, deadline, memory, cancel).await;
        let _ = std::fs::remove_dir_all(&dir);
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
    async fn fetch_inputs(&self, job: &SignedJob) -> Result<Vec<P1Group>, ValidatorResponse> {
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
                if let Err(e) = published_receipt(st, &decl).await {
                    return Err(refused(&format!("dependency {} has no valid published receipt: {e:?}", decl.short())));
                }
            }
            out.push(g);
        }
        Ok(out)
    }
}

fn refused(reason: &str) -> ValidatorResponse {
    ValidatorResponse::Refused { reason: reason.into() }
}
fn inconclusive(reason: &str) -> ValidatorResponse {
    ValidatorResponse::Inconclusive { reason: reason.into() }
}
