//! The controller.
//!
//! It holds the authority key (the fence authority of P2, which also signs job envelopes
//! and validator revocations) and runs two queues.
//!
//! **Target work.** A work job asks for a proof of one target name. `Poll` hands a queued
//! job to a live worker whose free memory covers the job's `memory_mb`, after assigning
//! the target to that worker with T4 (owner := worker, epoch + 1). Workers hold a lease
//! renewed by `Heartbeat`. When a lease expires, every target the worker owned is
//! reassigned at once (T4): to another live worker with room, or to a sentinel workspace
//! no worker holds, so the epoch moves and the stale owner's publication fails T1's epoch
//! fence even if it is still running. Its job goes back to the queue.
//!
//! **Validation.** `Validate` from a worker becomes an immutable envelope: the controller
//! reads each target record and refuses unless the worker is its owner, then stamps the
//! record's epoch, the pinned policy, checker version and base, the deadline and the
//! memory limit, signs it, and records it under `jobreq/<request>` (J1). A retry with the
//! same request gets the same envelope and, once there is one, the same receipt
//! (`jobreceipt/<request>`, J2); concurrent duplicates share one dispatch; a request ID
//! reused for another envelope is refused. Dispatch tries validators in turn; `Busy`,
//! `Inconclusive`, `Refused`, a timeout or an invalid receipt moves on to the next
//! validator, up to `validator_attempts` (at least once each); the answer is `Refused` only
//! if every validator refused. `Cancel` writes `jobcancel/<request>` (J3), stops the dispatch and
//! tells the validators; T1 refuses receipts of cancelled requests.
//!
//! Backpressure: at most `max_work_queue` queued work jobs and `max_validations` validations
//! in flight; beyond that the answer is `Busy` and nothing is recorded.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use paralean_store::receipt::{check_bound, prepared_of, sort_targets, JobEnvelope, SignedJob, TargetBinding};
use paralean_store::{Controller as StoreController, Id, Name, Receipt, Signer, Store, WorkspaceId};
use paralean_validator_api::{decode_receipt, rpc, ValidatorRequest, ValidatorResponse};
use serde::{Deserialize, Serialize};
use tokio::net::TcpListener;
use tokio::sync::watch;
use tokio::task::JoinHandle;

/// The workspace that owns a target whose owner died and that no live worker could take.
pub fn unowned() -> WorkspaceId {
    WorkspaceId::derive("paralean-p3/controller/unowned")
}

#[derive(Clone)]
pub struct ControllerConfig {
    pub store: Store,
    pub authority: Signer,
    pub validators: Vec<String>,
    pub base: Id,
    pub policy: Id,
    pub checker: Id,
    pub lease: Duration,
    pub max_work_queue: usize,
    pub max_validations: usize,
    /// Deadline and memory limit of a validation when the request names none, and caps on
    /// what a request may name.
    pub validation_deadline: Duration,
    pub validation_memory_mb: u64,
    /// Tries per validation across validators before giving up (inconclusive).
    pub validator_attempts: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TargetReq {
    pub name: String,
    /// Pinned statement hash (hex), or empty.
    #[serde(default)]
    pub statement: String,
}

/// Requests to the controller. IDs are hex; request IDs are free-form strings.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum ControlRequest {
    Register { worker: String, capacity_mb: u64 },
    Heartbeat { worker: String },
    SubmitWork { request: String, target: String, memory_mb: u64 },
    Poll { worker: String },
    Finish { worker: String, request: String, ok: bool },
    Validate {
        worker: String,
        request: String,
        group: String,
        capsule: String,
        deps: Vec<String>,
        targets: Vec<TargetReq>,
        #[serde(default)]
        memory_mb: u64,
        #[serde(default)]
        deadline_ms: u64,
    },
    Cancel { request: String },
    Assign { target: String, worker: String },
    Status,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "result", rename_all = "snake_case")]
pub enum ControlResponse {
    Ok,
    Registered { lease_ms: u64 },
    /// The worker is not registered, or its lease expired (it must re-register; its
    /// targets were reassigned).
    Unknown,
    Queued,
    Duplicate { state: String },
    Busy,
    NoWork,
    Work { request: String, target: String, epoch: u64, memory_mb: u64 },
    /// `receipt` and `job` are the signed receipt and envelope bytes (hex).
    Receipt { receipt: String, job: String },
    Refused { reason: String },
    Inconclusive { reason: String },
    Cancelled,
    Assigned { epoch: u64 },
    Status { status: serde_json::Value },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum WorkState {
    Queued,
    Running { worker: WorkspaceId, epoch: u64, delivered: bool },
    Done,
    Failed,
    Cancelled,
}

#[derive(Clone, Debug)]
struct WorkJob {
    target: Name,
    memory_mb: u64,
    state: WorkState,
    attempts: u64,
}

#[derive(Clone, Debug)]
struct WorkerInfo {
    capacity_mb: u64,
    used_mb: u64,
    lease_until: Instant,
    alive: bool,
}

struct Inflight {
    job: Id,
    result: watch::Receiver<Option<ControlResponse>>,
    cancel: watch::Sender<bool>,
}

#[derive(Default)]
struct State {
    workers: BTreeMap<WorkspaceId, WorkerInfo>,
    work: BTreeMap<String, WorkJob>,
    /// Submission order of work jobs.
    order: Vec<String>,
    inflight: HashMap<Vec<u8>, Inflight>,
    next_validator: usize,
}

pub struct ControlPlane {
    pub cfg: ControllerConfig,
    ctl: StoreController,
    state: Mutex<State>,
}

fn ws(s: &str) -> Option<WorkspaceId> {
    WorkspaceId::from_hex(s)
}

impl ControlPlane {
    pub fn new(cfg: ControllerConfig) -> Arc<ControlPlane> {
        let ctl = StoreController::new(cfg.store.clone(), cfg.authority.clone());
        Arc::new(ControlPlane { cfg, ctl, state: Mutex::new(State::default()) })
    }

    /// Serve on `listener` and run the lease monitor.
    pub fn serve(self: &Arc<Self>, listener: TcpListener) -> JoinHandle<()> {
        let me = self.clone();
        let server = crate::server::serve(listener, move |req: ControlRequest| {
            let me = me.clone();
            async move { me.handle(req).await }
        });
        let me = self.clone();
        tokio::spawn(async move {
            let mut tick = tokio::time::interval((me.cfg.lease / 4).max(Duration::from_millis(20)));
            loop {
                tick.tick().await;
                me.expire_leases().await;
                if server.is_finished() {
                    return;
                }
            }
        })
    }

    pub async fn handle(self: &Arc<Self>, req: ControlRequest) -> ControlResponse {
        match req {
            ControlRequest::Register { worker, capacity_mb } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let mut st = self.state.lock().unwrap();
                st.workers.insert(
                    w,
                    WorkerInfo { capacity_mb, used_mb: 0, lease_until: Instant::now() + self.cfg.lease, alive: true },
                );
                ControlResponse::Registered { lease_ms: self.cfg.lease.as_millis() as u64 }
            }
            ControlRequest::Heartbeat { worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let mut st = self.state.lock().unwrap();
                match st.workers.get_mut(&w) {
                    Some(i) if i.alive => {
                        i.lease_until = Instant::now() + self.cfg.lease;
                        ControlResponse::Ok
                    }
                    _ => ControlResponse::Unknown,
                }
            }
            ControlRequest::SubmitWork { request, target, memory_mb } => self.submit_work(request, target, memory_mb),
            ControlRequest::Poll { worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                self.poll(w).await
            }
            ControlRequest::Finish { worker, request, ok } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                self.finish(w, &request, ok)
            }
            ControlRequest::Validate { worker, request, group, capsule, deps, targets, memory_mb, deadline_ms } => {
                self.validate(worker, request, group, capsule, deps, targets, memory_mb, deadline_ms).await
            }
            ControlRequest::Cancel { request } => self.cancel(&request).await,
            ControlRequest::Assign { target, worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let req = format!("assign/{target}/{}/{}", w.hex(), rand::random::<u64>());
                match self.ctl.reassign(&Name::parse(&target), w, req.as_bytes()).await {
                    Ok(epoch) => ControlResponse::Assigned { epoch },
                    Err(e) => ControlResponse::Inconclusive { reason: e.to_string() },
                }
            }
            ControlRequest::Status => self.status(),
        }
    }

    fn status(&self) -> ControlResponse {
        let st = self.state.lock().unwrap();
        let workers: Vec<_> = st
            .workers
            .iter()
            .map(|(w, i)| serde_json::json!({"worker": w.hex(), "alive": i.alive, "capacity_mb": i.capacity_mb, "used_mb": i.used_mb}))
            .collect();
        let work: Vec<_> = st
            .order
            .iter()
            .map(|r| {
                let j = &st.work[r];
                serde_json::json!({"request": r, "target": j.target.to_string(), "state": format!("{:?}", j.state), "attempts": j.attempts})
            })
            .collect();
        ControlResponse::Status {
            status: serde_json::json!({"workers": workers, "work": work, "validations_in_flight": st.inflight.len()}),
        }
    }

    // ------------------------------------------------------------ target work

    fn submit_work(&self, request: String, target: String, memory_mb: u64) -> ControlResponse {
        let mut st = self.state.lock().unwrap();
        if !cfg!(feature = "mutate-no-request-dedup") {
            if let Some(j) = st.work.get(&request) {
                return ControlResponse::Duplicate { state: format!("{:?}", j.state) };
            }
        }
        let queued = st.work.values().filter(|j| j.state == WorkState::Queued).count();
        if queued >= self.cfg.max_work_queue {
            return ControlResponse::Busy;
        }
        if !st.work.contains_key(&request) {
            st.order.push(request.clone());
        }
        st.work.insert(request, WorkJob { target: Name::parse(&target), memory_mb, state: WorkState::Queued, attempts: 0 });
        ControlResponse::Queued
    }

    async fn poll(&self, w: WorkspaceId) -> ControlResponse {
        // A job already assigned to this worker (after a reassignment) comes first.
        let pick = {
            let mut st = self.state.lock().unwrap();
            match st.workers.get(&w) {
                Some(i) if i.alive && i.lease_until > Instant::now() => {}
                _ => return ControlResponse::Unknown,
            }
            let free = {
                let i = &st.workers[&w];
                i.capacity_mb.saturating_sub(i.used_mb)
            };
            let order = st.order.clone();
            let mut pick = None;
            for r in &order {
                let j = st.work.get_mut(r).unwrap();
                if let WorkState::Running { worker, epoch, delivered: false } = j.state {
                    if worker == w {
                        j.state = WorkState::Running { worker, epoch, delivered: true };
                        return ControlResponse::Work { request: r.clone(), target: j.target.to_string(), epoch, memory_mb: j.memory_mb };
                    }
                }
            }
            for r in &order {
                let j = st.work.get_mut(r).unwrap();
                if j.state == WorkState::Queued && j.memory_mb <= free {
                    j.attempts += 1;
                    // Reserve before the store write so a concurrent poll cannot take it.
                    j.state = WorkState::Running { worker: w, epoch: u64::MAX, delivered: true };
                    pick = Some((r.clone(), j.target.clone(), j.memory_mb, j.attempts));
                    break;
                }
            }
            if let Some((_, _, mem, _)) = &pick {
                st.workers.get_mut(&w).unwrap().used_mb += mem;
            }
            pick
        };
        let Some((request, target, memory_mb, attempt)) = pick else { return ControlResponse::NoWork };
        let req = format!("work/{request}/{attempt}");
        match self.ctl.reassign(&target, w, req.as_bytes()).await {
            Ok(epoch) => {
                let mut st = self.state.lock().unwrap();
                if let Some(j) = st.work.get_mut(&request) {
                    if matches!(j.state, WorkState::Running { worker, .. } if worker == w) {
                        j.state = WorkState::Running { worker: w, epoch, delivered: true };
                        return ControlResponse::Work { request, target: target.to_string(), epoch, memory_mb };
                    }
                }
                ControlResponse::NoWork
            }
            Err(e) => {
                let mut st = self.state.lock().unwrap();
                if let Some(j) = st.work.get_mut(&request) {
                    j.state = WorkState::Queued;
                }
                if let Some(i) = st.workers.get_mut(&w) {
                    i.used_mb = i.used_mb.saturating_sub(memory_mb);
                }
                ControlResponse::Inconclusive { reason: e.to_string() }
            }
        }
    }

    fn finish(&self, w: WorkspaceId, request: &str, ok: bool) -> ControlResponse {
        let mut st = self.state.lock().unwrap();
        let Some(j) = st.work.get_mut(request) else { return refused("unknown work request") };
        match j.state {
            WorkState::Running { worker, .. } if worker == w => {
                let mem = j.memory_mb;
                j.state = if ok {
                    WorkState::Done
                } else if j.attempts < 3 {
                    WorkState::Queued
                } else {
                    WorkState::Failed
                };
                if let Some(i) = st.workers.get_mut(&w) {
                    i.used_mb = i.used_mb.saturating_sub(mem);
                }
                ControlResponse::Ok
            }
            _ => refused("the job is not running on this worker"),
        }
    }

    /// Lease monitor: a worker whose lease expired is dead; each target it owned is
    /// reassigned immediately (T4), so its epoch moves even if the worker is still running.
    pub async fn expire_leases(&self) {
        if cfg!(feature = "mutate-no-lease-reassign") {
            return;
        }
        let now = Instant::now();
        let mut moves: Vec<(String, Name, WorkspaceId, u64)> = Vec::new();
        {
            let mut st = self.state.lock().unwrap();
            let dead: Vec<WorkspaceId> =
                st.workers.iter().filter(|(_, i)| i.alive && i.lease_until <= now).map(|(w, _)| *w).collect();
            for d in &dead {
                st.workers.get_mut(d).unwrap().alive = false;
            }
            let order = st.order.clone();
            for r in order {
                let (target, mem, attempts) = {
                    let j = &st.work[&r];
                    match j.state {
                        WorkState::Running { worker, .. } if dead.contains(&worker) => (j.target.clone(), j.memory_mb, j.attempts),
                        _ => continue,
                    }
                };
                // Another live worker with room, else the sentinel.
                let next = st
                    .workers
                    .iter()
                    .find(|(w, i)| i.alive && i.lease_until > now && i.capacity_mb.saturating_sub(i.used_mb) >= mem && !dead.contains(w))
                    .map(|(w, _)| *w);
                let j = st.work.get_mut(&r).unwrap();
                j.attempts = attempts + 1;
                match next {
                    Some(n) => {
                        j.state = WorkState::Running { worker: n, epoch: u64::MAX, delivered: false };
                        st.workers.get_mut(&n).unwrap().used_mb += mem;
                        moves.push((r.clone(), target, n, attempts + 1));
                    }
                    None => {
                        j.state = WorkState::Queued;
                        moves.push((r.clone(), target, unowned(), attempts + 1));
                    }
                }
            }
        }
        for (r, target, to, attempt) in moves {
            let req = format!("lease/{r}/{attempt}");
            let res = self.ctl.reassign(&target, to, req.as_bytes()).await;
            let mut st = self.state.lock().unwrap();
            if let Some(j) = st.work.get_mut(&r) {
                if let (Ok(epoch), WorkState::Running { worker, delivered, .. }) = (&res, j.state.clone()) {
                    if worker == to {
                        j.state = WorkState::Running { worker, epoch: *epoch, delivered };
                    }
                }
            }
        }
    }

    // ------------------------------------------------------------ validation

    #[allow(clippy::too_many_arguments)]
    async fn validate(
        self: &Arc<Self>,
        worker: String,
        request: String,
        group: String,
        capsule: String,
        deps: Vec<String>,
        targets: Vec<TargetReq>,
        memory_mb: u64,
        deadline_ms: u64,
    ) -> ControlResponse {
        let st = &self.cfg.store;
        let Some(w) = ws(&worker) else { return refused("bad worker ID") };
        {
            let s = self.state.lock().unwrap();
            match s.workers.get(&w) {
                Some(i) if i.alive && i.lease_until > Instant::now() => {}
                _ => return refused("worker is not registered or its lease expired"),
            }
        }
        let (Some(group), Some(capsule)) = (Id::from_hex(&group), Id::from_hex(&capsule)) else {
            return refused("bad group or capsule ID");
        };
        let Some(deps) = deps.iter().map(|d| Id::from_hex(d)).collect::<Option<Vec<_>>>() else {
            return refused("bad dependency ID");
        };
        // Bind each target to the epoch of its record, if this worker owns it.
        let mut bindings = Vec::new();
        for t in &targets {
            let name = Name::parse(&t.name);
            let rec = match st.target(&name).await {
                Ok(Some(r)) => r,
                Ok(None) => return refused(&format!("no target record for {name}")),
                Err(e) => return inconclusive(&e.to_string()),
            };
            if rec.owner != w && !cfg!(feature = "mutate-no-dispatch-owner-check") {
                return refused(&format!("worker does not own {name}"));
            }
            let Ok(statement) = hex::decode(&t.statement) else { return refused("bad statement hash") };
            bindings.push(TargetBinding { name, epoch: rec.epoch, statement });
        }
        sort_targets(&mut bindings);
        let cap_ms = self.cfg.validation_deadline.as_millis() as u64;
        let env = JobEnvelope {
            request: request.as_bytes().to_vec(),
            group,
            capsule,
            deps,
            base: self.cfg.base,
            policy: self.cfg.policy,
            checker: self.cfg.checker,
            worker: w,
            targets: bindings,
            deadline_ms: if deadline_ms == 0 { cap_ms } else { deadline_ms.min(cap_ms) },
            memory_mb: if memory_mb == 0 { self.cfg.validation_memory_mb } else { memory_mb.min(self.cfg.validation_memory_mb) },
        };
        let mut job = SignedJob::sign(env, &self.cfg.authority);
        let req = job.body.request.clone();

        // Deduplication: an in-flight duplicate shares the dispatch.
        let mut rx = {
            let s = self.state.lock().unwrap();
            if let Some(f) = s.inflight.get(&req).filter(|_| !cfg!(feature = "mutate-no-request-dedup")) {
                if f.job != job.id() {
                    return refused("request ID already used for another envelope");
                }
                Some(f.result.clone())
            } else {
                if s.inflight.len() >= self.cfg.max_validations {
                    return ControlResponse::Busy;
                }
                None
            }
        };
        if rx.is_none() {
            match st.meta.is_cancelled(&req).await {
                Ok(true) => return ControlResponse::Cancelled,
                Ok(false) => {}
                Err(e) => return inconclusive(&e.to_string()),
            }
            // J1: the envelope recorded for this request, or this one.
            if !cfg!(feature = "mutate-no-request-dedup") {
                match st.meta.issue_job(&job).await {
                    Ok(stored) if stored.body == job.body => job = stored,
                    Ok(_) => return refused("request ID already used for another envelope"),
                    Err(e) => return inconclusive(&e.to_string()),
                }
                // A finished request: the recorded receipt.
                if let Ok(Some(v)) = st.meta.get(st.meta.keys.job_receipt(&req)).await {
                    if let Ok(r) = Receipt::from_bytes(&v) {
                        return ControlResponse::Receipt { receipt: hex::encode(r.to_bytes()), job: hex::encode(job.to_bytes()) };
                    }
                }
            }
            let (tx, nrx) = watch::channel(None);
            let (ctx, crx) = watch::channel(false);
            {
                let mut s = self.state.lock().unwrap();
                if let Some(f) = s.inflight.get(&req).filter(|_| !cfg!(feature = "mutate-no-request-dedup")) {
                    // Lost a race with a concurrent duplicate: share its dispatch.
                    rx = Some(f.result.clone());
                } else {
                    s.inflight.insert(req.clone(), Inflight { job: job.id(), result: nrx.clone(), cancel: ctx });
                    rx = Some(nrx);
                    let me = self.clone();
                    let job = job.clone();
                    let req = req.clone();
                    tokio::spawn(async move {
                        let r = me.dispatch(&job, crx).await;
                        let _ = tx.send(Some(r));
                        me.state.lock().unwrap().inflight.remove(&req);
                    });
                }
            }
        }
        let mut rx = rx.unwrap();
        loop {
            if let Some(r) = rx.borrow().clone() {
                return r;
            }
            if rx.changed().await.is_err() {
                return inconclusive("dispatch abandoned");
            }
        }
    }

    /// Send the envelope to validators until one gives a valid receipt or refuses.
    async fn dispatch(&self, job: &SignedJob, mut cancel: watch::Receiver<bool>) -> ControlResponse {
        let st = &self.cfg.store;
        let n = self.cfg.validators.len();
        if n == 0 {
            return inconclusive("no validators configured");
        }
        let start = {
            let mut s = self.state.lock().unwrap();
            s.next_validator += 1;
            s.next_validator
        };
        let timeout = Duration::from_millis(job.body.deadline_ms) + Duration::from_secs(5);
        let mut last = String::from("no attempt");
        let mut refusals = 0;
        for attempt in 0..self.cfg.validator_attempts.max(n) {
            if *cancel.borrow() {
                return ControlResponse::Cancelled;
            }
            let addr = self.cfg.validators[(start + attempt) % n].clone();
            let call = paralean_validator_api::validate(&addr, job, timeout);
            let resp = tokio::select! {
                r = call => r,
                _ = cancel.changed() => {
                    self.tell_cancel(&job.body.request).await;
                    return ControlResponse::Cancelled;
                }
            };
            match resp {
                Ok(ValidatorResponse::Receipt { receipt }) => {
                    let r = match decode_receipt(&receipt) {
                        Ok(r) => r,
                        Err(e) => {
                            last = format!("{addr}: undecodable receipt: {e}");
                            continue;
                        }
                    };
                    // A receipt must verify and be bound to this envelope (any verdict).
                    let bound = check_bound(&r, job, &job.body.group, &prepared_of(job), &st.ring).is_ok();
                    if !bound {
                        last = format!("{addr}: receipt does not verify or is not bound to the envelope");
                        continue;
                    }
                    let stored = match st.meta.record_receipt(&job.body.request, &r).await {
                        Ok(s) => s,
                        Err(e) => return inconclusive(&e.to_string()),
                    };
                    return ControlResponse::Receipt { receipt: hex::encode(stored.to_bytes()), job: hex::encode(job.to_bytes()) };
                }
                Ok(ValidatorResponse::Refused { reason }) => {
                    // A refusal can be the validator's own (revoked key, other checker):
                    // try the others; refuse only if every validator refuses.
                    last = format!("validator {addr}: {reason}");
                    refusals += 1;
                    if refusals >= n {
                        return refused(&last);
                    }
                    continue;
                }
                Ok(ValidatorResponse::Cancelled) => return ControlResponse::Cancelled,
                Ok(ValidatorResponse::Busy) => last = format!("{addr}: busy"),
                Ok(ValidatorResponse::Inconclusive { reason }) => last = format!("{addr}: {reason}"),
                Ok(other) => last = format!("{addr}: unexpected {other:?}"),
                Err(e) => last = format!("{addr}: {e}"),
            }
            tokio::time::sleep(Duration::from_millis(20 * (attempt as u64 + 1))).await;
        }
        if refusals > 0 {
            return refused(&last);
        }
        inconclusive(&format!("no validator gave a verdict ({last})"))
    }

    async fn tell_cancel(&self, request: &[u8]) {
        for addr in &self.cfg.validators {
            let _: std::io::Result<ValidatorResponse> =
                rpc::call(addr, &ValidatorRequest::Cancel { request: hex::encode(request) }, Duration::from_secs(2)).await;
        }
    }

    async fn cancel(&self, request: &str) -> ControlResponse {
        let req = request.as_bytes().to_vec();
        // J3 first: from here on no T1 accepts a receipt bound to this request.
        if let Err(e) = self.cfg.store.meta.cancel_job(&req).await {
            return inconclusive(&e.to_string());
        }
        {
            let mut s = self.state.lock().unwrap();
            if let Some(f) = s.inflight.get(&req) {
                let _ = f.cancel.send(true);
            }
            if let Some(j) = s.work.get_mut(request) {
                if let WorkState::Running { worker, .. } = j.state {
                    let mem = j.memory_mb;
                    if let Some(i) = s.workers.get_mut(&worker) {
                        i.used_mb = i.used_mb.saturating_sub(mem);
                    }
                }
                if let Some(j) = s.work.get_mut(request) {
                    j.state = WorkState::Cancelled;
                }
            }
        }
        self.tell_cancel(&req).await;
        ControlResponse::Cancelled
    }
}

fn refused(reason: &str) -> ControlResponse {
    ControlResponse::Refused { reason: reason.into() }
}
fn inconclusive(reason: &str) -> ControlResponse {
    ControlResponse::Inconclusive { reason: reason.into() }
}
