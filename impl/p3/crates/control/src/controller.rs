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
//! memory limit, signs it, and records it under `jobreq/<worker>/<request>` (J1). Request
//! IDs are the worker's own namespace: every job record, the in-flight map and the
//! validators' slots are keyed by (worker, request), so one worker cannot squat or cancel
//! another's request ID. A retry with the same request gets the same envelope and, once
//! there is one, the same receipt (`jobreceipt/<worker>/<request>`, J2); concurrent
//! duplicates share one dispatch; a request ID reused for another envelope is refused.
//! Dispatch tries validators in turn; `Busy`, `Inconclusive`, `Refused`, a timeout or an
//! invalid receipt moves on to the next validator, up to `validator_attempts` (at least once
//! each); the answer is `Refused` only if every validator refused. `Cancel` (the authority)
//! writes `jobcancel/<worker>/<request>` (J3) for the named worker, or for every configured
//! workspace when it names none, stops the dispatch and tells the validators; T1 refuses
//! receipts of cancelled requests.
//!
//! Backpressure: at most `max_work_queue` queued work jobs and `max_validations` validations
//! in flight; beyond that the answer is `Busy` and nothing is recorded.

use std::collections::{BTreeMap, HashMap};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use paralean_store::receipt::{check_bound, prepared_of, sort_targets, JobEnvelope, SignedJob, TargetBinding};
use foundationdb::{KeySelector, RangeOption};
use foundationdb::options::StreamingMode;
use paralean_store::{Id, Name, Receipt, Signer, Store, WorkspaceId};
use paralean_validator_api::{decode_receipt, rpc, ValidatorRequest, ValidatorResponse};
use serde::{Deserialize, Serialize};
use tokio::net::TcpListener;
use tokio::sync::watch;
use tokio::task::JoinHandle;
use crate::durable::{now_ms, Durable, GroupRequest};

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
    PollRequest { worker: String, request: String },
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
    /// Cancel `worker`'s request (hex workspace ID), or that request ID of every
    /// configured workspace when `worker` is empty.
    Cancel { request: String, #[serde(default)] worker: String },
    Assign { target: String, worker: String },
    AssignGroup { targets: Vec<String>, worker: String, #[serde(default)] request: String },
    Status,
}

impl rpc::Service for ControlRequest {
    const NAME: &'static str = "paralean/controller";
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
    AssignedGroup { epochs: Vec<u64> },
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
    lease_until: u64,
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
    groups: Vec<StoredGroup>,
    recovery_cursor: Vec<u8>,
    /// A recovery pass over J1 is under way (it starts on takeover and ends at the last page).
    recovering: bool,
    poll_responses: BTreeMap<String, StoredPoll>,
    /// Insertion counter of `poll_responses` (the oldest of a worker's tokens goes first).
    poll_seq: u64,
}

/// Bounds on the controller snapshot, which every operation loads and saves. Request IDs
/// and poll tokens are chosen by clients; finished work and answered poll tokens are
/// dropped oldest first beyond these counts.
pub const MAX_REQUEST_ID: usize = 256;
pub const MAX_POLL_TOKENS_PER_WORKER: usize = 16;
pub const MAX_FINISHED_WORK: usize = 1024;

pub struct ControlPlane {
    pub cfg: ControllerConfig,
    state: Mutex<State>,
    durable: Durable,
    operation: tokio::sync::Mutex<()>,
    seen_term: AtomicU64,
}

struct AbortOnDrop(JoinHandle<()>);

impl Drop for AbortOnDrop {
    fn drop(&mut self) { self.0.abort(); }
}

#[derive(Serialize, Deserialize, Default)]
struct Snapshot {
    workers: BTreeMap<String, StoredWorker>,
    work: BTreeMap<String, StoredWork>,
    order: Vec<String>,
    next_validator: usize,
    #[serde(default)]
    groups: Vec<StoredGroup>,
    #[serde(default)]
    recovery_cursor: Vec<u8>,
    #[serde(default)]
    recovering: bool,
    #[serde(default)]
    poll_responses: BTreeMap<String, StoredPoll>,
    #[serde(default)]
    poll_seq: u64,
}

#[derive(Clone, Serialize, Deserialize)]
struct StoredPoll { worker: String, work: Option<String>, #[serde(default)] seq: u64 }

#[derive(Clone, Serialize, Deserialize)]
struct StoredGroup {
    names: Vec<String>,
    owner: String,
    request: String,
    pending: bool,
}

#[derive(Serialize, Deserialize)]
struct StoredWorker { capacity_mb: u64, used_mb: u64, lease_until: u64, alive: bool }

#[derive(Serialize, Deserialize)]
struct StoredWork { target: String, memory_mb: u64, state: StoredWorkState, attempts: u64 }

#[derive(Serialize, Deserialize)]
enum StoredWorkState {
    Queued,
    Running { worker: String, epoch: u64, delivered: bool },
    Done,
    Failed,
    Cancelled,
}

impl From<&WorkState> for StoredWorkState {
    fn from(value: &WorkState) -> Self {
        match value {
            WorkState::Queued => Self::Queued,
            WorkState::Running { worker, epoch, delivered } => Self::Running { worker: worker.hex(), epoch: *epoch, delivered: *delivered },
            WorkState::Done => Self::Done,
            WorkState::Failed => Self::Failed,
            WorkState::Cancelled => Self::Cancelled,
        }
    }
}

impl StoredWorkState {
    fn restore(self) -> Option<WorkState> {
        Some(match self {
            Self::Queued => WorkState::Queued,
            Self::Running { worker, epoch, delivered } => WorkState::Running { worker: ws(&worker)?, epoch, delivered },
            Self::Done => WorkState::Done,
            Self::Failed => WorkState::Failed,
            Self::Cancelled => WorkState::Cancelled,
        })
    }
}

impl State {
    fn snapshot(&self) -> Snapshot {
        Snapshot {
            workers: self.workers.iter().map(|(id, i)| (id.hex(), StoredWorker { capacity_mb: i.capacity_mb, used_mb: i.used_mb, lease_until: i.lease_until, alive: i.alive })).collect(),
            work: self.work.iter().map(|(r, j)| (r.clone(), StoredWork { target: j.target.to_string(), memory_mb: j.memory_mb, state: StoredWorkState::from(&j.state), attempts: j.attempts })).collect(),
            order: self.order.clone(), next_validator: self.next_validator, groups: self.groups.clone(), recovery_cursor: self.recovery_cursor.clone(), recovering: self.recovering, poll_responses: self.poll_responses.clone(),
            poll_seq: self.poll_seq,
        }
    }
    fn restore(&mut self, s: Snapshot) {
        self.workers = s.workers.into_iter().filter_map(|(id, i)| ws(&id).map(|id| (id, WorkerInfo { capacity_mb: i.capacity_mb, used_mb: i.used_mb, lease_until: i.lease_until, alive: i.alive }))).collect();
        self.work = s.work.into_iter().filter_map(|(r, j)| Some((r, WorkJob { target: Name::parse(&j.target), memory_mb: j.memory_mb, state: j.state.restore()?, attempts: j.attempts }))).collect();
        self.order = s.order;
        self.next_validator = s.next_validator;
        self.groups = s.groups;
        self.recovery_cursor = s.recovery_cursor;
        self.recovering = s.recovering;
        self.poll_responses = s.poll_responses;
        self.poll_seq = s.poll_seq;
    }

    /// Bind a poll token to its answer. A worker keeps its most recent
    /// `MAX_POLL_TOKENS_PER_WORKER` tokens: one poll is outstanding at a time, and a token
    /// only has to outlive the retries of its own call.
    fn remember_poll(&mut self, token: &str, worker: &WorkspaceId, work: Option<String>) {
        self.poll_seq += 1;
        let worker = worker.hex();
        self.poll_responses.insert(token.into(), StoredPoll { worker: worker.clone(), work, seq: self.poll_seq });
        if cfg!(feature = "mutate-unbounded-poll-responses") { return }
        let mut mine: Vec<(u64, String)> = self.poll_responses.iter()
            .filter(|(_, p)| p.worker == worker).map(|(t, p)| (p.seq, t.clone())).collect();
        if mine.len() > MAX_POLL_TOKENS_PER_WORKER {
            mine.sort();
            for (_, t) in &mine[..mine.len() - MAX_POLL_TOKENS_PER_WORKER] {
                self.poll_responses.remove(t);
            }
        }
    }

    /// Drop the oldest finished (done, failed, cancelled) work beyond `MAX_FINISHED_WORK`.
    /// A dropped request ID is no longer a duplicate: submitting it again queues new work.
    fn prune_finished_work(&mut self) {
        if cfg!(feature = "mutate-no-work-gc") { return }
        let finished = |j: &WorkJob| matches!(j.state, WorkState::Done | WorkState::Failed | WorkState::Cancelled);
        let mut excess = self.work.values().filter(|j| finished(j)).count().saturating_sub(MAX_FINISHED_WORK);
        if excess == 0 { return }
        let mut drop = std::collections::BTreeSet::new();
        for r in &self.order {
            if excess == 0 { break }
            if self.work.get(r).is_some_and(finished) {
                drop.insert(r.clone());
                excess -= 1;
            }
        }
        self.order.retain(|r| !drop.contains(r));
        self.work.retain(|r, _| !drop.contains(r));
    }
}

fn ws(s: &str) -> Option<WorkspaceId> {
    WorkspaceId::from_hex(s)
}

/// The client-chosen request ID or poll token of a request, if it has one.
fn request_id(req: &ControlRequest) -> Option<&str> {
    match req {
        ControlRequest::SubmitWork { request, .. }
        | ControlRequest::PollRequest { request, .. }
        | ControlRequest::Finish { request, .. }
        | ControlRequest::Validate { request, .. }
        | ControlRequest::Cancel { request, .. }
        | ControlRequest::AssignGroup { request, .. } => Some(request),
        _ => None,
    }
}

/// The in-flight key of a validation: (requesting workspace, request ID).
fn job_key(worker: &WorkspaceId, request: &[u8]) -> Vec<u8> {
    let mut k = worker.0.to_vec();
    k.extend_from_slice(request);
    k
}

/// Call a controller replica list such as `host-a:9000,host-b:9000`.
/// The signed request is regenerated for each connection's challenge, while its
/// logical request ID stays unchanged across retries and leader failover.
pub async fn call_controller(
    addrs: &str, req: &ControlRequest, signer: &Signer, authority_public: &[u8; 32], total_timeout: Duration,
) -> std::io::Result<ControlResponse> {
    let endpoints: Vec<&str> = addrs.split(',').map(str::trim).filter(|s| !s.is_empty()).collect();
    if endpoints.is_empty() {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, "no controller address"));
    }
    let budget = if matches!(req, ControlRequest::Validate { .. }) { total_timeout } else { total_timeout.min(Duration::from_secs(15)) };
    let deadline = Instant::now() + budget;
    let mut last_error = None;
    let mut follower = None;
    loop {
        for addr in &endpoints {
            let left = deadline.saturating_duration_since(Instant::now());
            if left.is_zero() { break }
            let one = left.min(if matches!(req, ControlRequest::Validate { .. }) { Duration::from_secs(30) } else { Duration::from_secs(3) });
            match rpc::call_authenticated(addr, req, signer, authority_public, one).await {
                Ok(ControlResponse::Inconclusive { reason }) if reason == "not controller leader" => {
                    follower = Some(ControlResponse::Inconclusive { reason });
                }
                Ok(ControlResponse::Status { status }) if status.get("leader") == Some(&serde_json::Value::Bool(false)) => {
                    follower = Some(ControlResponse::Status { status });
                }
                Ok(response) => return Ok(response),
                Err(error) => last_error = Some(error),
            }
        }
        if Instant::now() >= deadline {
            return follower.map(Ok).unwrap_or_else(|| Err(last_error.unwrap_or_else(|| std::io::Error::new(std::io::ErrorKind::TimedOut, "no controller replica available"))));
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}

impl ControlPlane {
    pub fn new(cfg: ControllerConfig) -> Arc<ControlPlane> {
        let durable = Durable::new(cfg.store.clone(), cfg.lease);
        Arc::new(ControlPlane { cfg, state: Mutex::new(State::default()), durable, operation: tokio::sync::Mutex::new(()), seen_term: AtomicU64::new(0) })
    }

    /// Serve on `listener` and run the lease monitor.
    pub fn serve(self: &Arc<Self>, listener: TcpListener) -> JoinHandle<()> {
        let me = self.clone();
        let ring = self.cfg.store.ring.clone();
        let privileged = ring.authority;
        let server = crate::server::serve_authenticated(listener, self.cfg.authority.clone(), privileged, move |req: &ControlRequest, public| {
            match req {
                ControlRequest::Register { worker, .. }
                | ControlRequest::Heartbeat { worker }
                | ControlRequest::Poll { worker }
                | ControlRequest::PollRequest { worker, .. }
                | ControlRequest::Finish { worker, .. }
                | ControlRequest::Validate { worker, .. } => ws(worker).and_then(|w| ring.writer(&w).copied()).is_some_and(|key| &key == public),
                _ => &ring.authority == public,
            }
        }, move |req: ControlRequest| {
            let me = me.clone();
            async move { me.handle(req).await }
        });
        let server = AbortOnDrop(server);
        let me = self.clone();
        tokio::spawn(async move {
            let mut tick = tokio::time::interval((me.cfg.lease / 4).max(Duration::from_millis(20)));
            loop {
                tick.tick().await;
                me.expire_leases().await;
                if server.0.is_finished() {
                    return;
                }
            }
        })
    }

    pub async fn handle(self: &Arc<Self>, req: ControlRequest) -> ControlResponse {
        // A long validation may outlive a worker heartbeat. J1/J2 persist its
        // envelope and receipt independently; the controller snapshot is only read.
        if matches!(req, ControlRequest::Validate { .. }) {
            {
                let _guard = self.operation.lock().await;
                let Ok(Some(lease)) = self.durable.acquire_or_renew().await else { return inconclusive("not controller leader") };
                if let Err(e) = self.load_state().await { return inconclusive(&e) }
                let takeover = self.on_leadership(lease.term);
                if takeover { self.recover_pending().await }
                if let Err(e) = self.save_state(lease.term).await { return inconclusive(&e) }
            }
            return self.handle_inner(req).await;
        }
        let _guard = self.operation.lock().await;
        let lease = match self.durable.acquire_or_renew().await {
            Ok(Some(l)) => l,
            Ok(None) => {
                if matches!(req, ControlRequest::Status) {
                    return ControlResponse::Status { status: serde_json::json!({"leader": false}) };
                }
                return inconclusive("not controller leader");
            }
            Err(e) => return inconclusive(&e),
        };
        if let Err(e) = self.load_state().await { return inconclusive(&e) }
        let takeover = self.on_leadership(lease.term);
        if takeover {
            self.recover_pending().await;
        }
        let resp = self.handle_inner(req).await;
        if let Err(e) = self.save_state(lease.term).await { return inconclusive(&e) }
        resp
    }

    async fn load_state(&self) -> Result<(), String> {
        let bytes = self.durable.load().await?;
        let snap = bytes.map(|b| serde_json::from_slice(&b).map_err(|e| e.to_string())).transpose()?.unwrap_or_default();
        self.state.lock().unwrap().restore(snap);
        Ok(())
    }

    async fn save_state(&self, term: u64) -> Result<(), String> {
        let bytes = {
            let mut st = self.state.lock().unwrap();
            st.prune_finished_work();
            serde_json::to_vec(&st.snapshot()).map_err(|e| e.to_string())?
        };
        self.durable.save(&bytes, term).await
    }

    /// True on the first operation of a new term: this replica just took the lease. A
    /// takeover starts one recovery pass over J1 (`recover_pending`).
    fn on_leadership(&self, term: u64) -> bool {
        let takeover = self.seen_term.swap(term, Ordering::SeqCst) != term;
        if takeover {
            let mut state = self.state.lock().unwrap();
            state.recovering = true;
            state.recovery_cursor.clear();
        }
        takeover
    }

    /// One page of the recovery pass a takeover started: re-dispatch envelopes (J1) with
    /// no receipt (J2) and no cancellation (J3), whose client may be gone with the old
    /// leader. The pass ends after the last page; each envelope is recovered at most
    /// `validator_attempts` times over all takeovers (a durable count), so an envelope
    /// no validator can decide is not re-dispatched forever.
    async fn recover_pending(self: &Arc<Self>) {
        let every_tick = cfg!(feature = "mutate-recover-every-tick");
        let (cursor, recovering) = {
            let state = self.state.lock().unwrap();
            (state.recovery_cursor.clone(), state.recovering)
        };
        if !recovering && !every_tick { return }
        let Ok(Some(lease)) = self.durable.current().await else { return };
        let sub = self.cfg.store.meta.keys.sub("jobreq");
        let (begin, end) = sub.range();
        let start = if cursor.is_empty() { KeySelector::first_greater_or_equal(begin) } else { KeySelector::first_greater_than(cursor.clone()) };
        let opt = RangeOption {
            limit: Some(128), mode: StreamingMode::WantAll,
            ..RangeOption::from((start, KeySelector::first_greater_or_equal(end)))
        };
        let Ok(trx) = self.cfg.store.meta.db.create_trx() else { return };
        let Ok(page) = trx.get_range(&opt, 1, false).await else { return };
        let jobs: Vec<(Vec<u8>, Vec<u8>)> = page.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect();
        {
            let mut state = self.state.lock().unwrap();
            state.recovery_cursor = if page.more() { jobs.last().map(|(key, _)| key.clone()).unwrap_or_default() } else { Vec::new() };
            state.recovering = page.more();
        }
        let mut previous = cursor;
        for (key, bytes) in jobs {
            let resume_here = previous.clone();
            previous = key;
            let Ok(job) = SignedJob::from_bytes(&bytes) else { continue };
            if !job.verify(&self.cfg.authority.public()) { continue }
            let worker = job.body.worker;
            let req = job_key(&worker, &job.body.request);
            if self.cfg.store.meta.get(self.cfg.store.meta.keys.job_receipt(&worker, &job.body.request)).await.ok().flatten().is_some() { continue }
            if self.cfg.store.meta.is_cancelled(&worker, &job.body.request).await.unwrap_or(true) { continue }
            {
                let mut state = self.state.lock().unwrap();
                if state.inflight.contains_key(&req) { continue }
                if state.inflight.len() >= self.cfg.max_validations {
                    // Full: resume at this envelope on a later tick.
                    state.recovery_cursor = resume_here;
                    state.recovering = true;
                    break;
                }
            }
            if !every_tick {
                let limit = self.cfg.validator_attempts.max(1) as u64;
                match self.durable.count_recovery(&worker, &job.body.request, limit, lease.term).await {
                    Ok(true) => {}
                    Ok(false) => continue,
                    Err(_) => return,
                }
            }
            let (tx, rx) = watch::channel(None);
            let (ctx, crx) = watch::channel(false);
            {
                let mut state = self.state.lock().unwrap();
                if state.inflight.contains_key(&req) { continue }
                state.inflight.insert(req.clone(), Inflight { job: job.id(), result: rx, cancel: ctx });
            }
            let me = self.clone();
            tokio::spawn(async move {
                let result = me.dispatch(&job, crx).await;
                let _ = tx.send(Some(result));
                me.state.lock().unwrap().inflight.remove(&req);
            });
        }
    }

    async fn handle_inner(self: &Arc<Self>, req: ControlRequest) -> ControlResponse {
        if let Some(id) = request_id(&req) {
            if id.len() > MAX_REQUEST_ID && !cfg!(feature = "mutate-unbounded-poll-responses") {
                return refused(&format!("request ID longer than {MAX_REQUEST_ID} bytes"));
            }
        }
        match req {
            ControlRequest::Register { worker, capacity_mb } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let mut st = self.state.lock().unwrap();
                let used_mb = st.work.values().filter_map(|j| match j.state {
                    WorkState::Running { worker, .. } if worker == w => Some(j.memory_mb),
                    _ => None,
                }).sum();
                st.workers.insert(
                    w,
                    WorkerInfo { capacity_mb, used_mb, lease_until: now_ms() + self.cfg.lease.as_millis() as u64, alive: true },
                );
                ControlResponse::Registered { lease_ms: self.cfg.lease.as_millis() as u64 }
            }
            ControlRequest::Heartbeat { worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let mut st = self.state.lock().unwrap();
                match st.workers.get_mut(&w) {
                    Some(i) if i.alive => {
                        i.lease_until = now_ms() + self.cfg.lease.as_millis() as u64;
                        ControlResponse::Ok
                    }
                    _ => ControlResponse::Unknown,
                }
            }
            ControlRequest::SubmitWork { request, target, memory_mb } => self.submit_work(request, target, memory_mb),
            ControlRequest::Poll { worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                self.poll(w, None).await
            }
            ControlRequest::PollRequest { worker, request } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                if request.is_empty() { return refused("empty poll request ID") }
                self.poll(w, Some(&request)).await
            }
            ControlRequest::Finish { worker, request, ok } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                self.finish(w, &request, ok)
            }
            ControlRequest::Validate { worker, request, group, capsule, deps, targets, memory_mb, deadline_ms } => {
                self.validate(worker, request, group, capsule, deps, targets, memory_mb, deadline_ms).await
            }
            ControlRequest::Cancel { request, worker } => {
                let worker = if worker.is_empty() { None } else {
                    match ws(&worker) { Some(w) => Some(w), None => return refused("bad worker ID") }
                };
                self.cancel(&request, worker).await
            }
            ControlRequest::Assign { target, worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let target = Name::parse(&target);
                if target.to_string().is_empty() { return refused("empty target name") }
                if self.state.lock().unwrap().groups.iter().any(|g| g.names.contains(&target.to_string())) {
                    return refused("target belongs to an assigned group; use assign_group");
                }
                if self.state.lock().unwrap().work.values().any(|j| j.target == target &&
                    matches!(j.state, WorkState::Queued | WorkState::Running { .. })) {
                    return refused("target has queued or running work; finish that work before assign");
                }
                let req = format!("assign/{target}/{}/{}", w.hex(), rand::random::<u64>());
                let term = match self.durable.current().await { Ok(Some(l)) => l.term, _ => return inconclusive("not controller leader") };
                match self.durable.assign_group(&[target], w, req.as_bytes(), term).await.map(|v| v[0]) {
                    Ok(epoch) => ControlResponse::Assigned { epoch },
                    Err(e) => ControlResponse::Inconclusive { reason: e.to_string() },
                }
            }
            ControlRequest::AssignGroup { targets, worker, request } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                if targets.is_empty() { return refused("empty target group") }
                let names: Vec<Name> = targets.iter().map(|s| Name::parse(s)).collect();
                if names.iter().any(|n| n.to_string().is_empty()) { return refused("empty target name") }
                let mut target_set: Vec<String> = names.iter().map(ToString::to_string).collect();
                target_set.sort();
                target_set.dedup();
                if target_set.len() != targets.len() { return refused("duplicate target name") }
                {
                    let st = self.state.lock().unwrap();
                    if st.groups.iter().any(|g| g.names.iter().any(|n| target_set.contains(n)) && g.names != target_set) {
                        return refused("target belongs to another jointly assigned group");
                    }
                    if st.work.values().any(|j| target_set.contains(&j.target.to_string()) &&
                        matches!(j.state, WorkState::Queued | WorkState::Running { .. })) {
                        return refused("target has queued or running work; finish that work before assign_group");
                    }
                }
                let req = if request.is_empty() { format!("assign-group/{worker}/{}", rand::random::<u64>()) } else { request };
                let used_before = match self.durable.group_request(&req).await {
                    Ok(v) => v.is_some(),
                    Err(e) => return inconclusive(&e),
                };
                let was_assigned = match self.cfg.store.meta.get(self.cfg.store.meta.keys.assign_request(&names[0], req.as_bytes())).await {
                    Ok(v) => v.is_some(),
                    Err(e) => return inconclusive(&e.to_string()),
                };
                if (used_before || was_assigned) && self.state.lock().unwrap().groups.iter().any(|g| g.names == target_set && g.request != req) {
                    return refused("assignment request was superseded by a later handover");
                }
                let term = match self.durable.current().await { Ok(Some(l)) => l.term, _ => return inconclusive("not controller leader") };
                let descriptor = GroupRequest { request: req.clone(), names: target_set.clone(), owner: worker.clone() };
                if let Err(e) = self.durable.reserve_group_request(&descriptor, term).await { return refused(&e) }
                {
                    let mut st = self.state.lock().unwrap();
                    if let Some(g) = st.groups.iter_mut().find(|g| g.names == target_set) {
                        g.owner = worker.clone();
                        g.request = req.clone();
                        g.pending = true;
                    } else {
                        st.groups.push(StoredGroup { names: target_set, owner: worker.clone(), request: req.clone(), pending: true });
                    }
                }
                if let Err(e) = self.save_state(term).await { return inconclusive(&e) }
                match self.durable.assign_group(&names, w, req.as_bytes(), term).await {
                    Ok(epochs) => {
                        if let Some(g) = self.state.lock().unwrap().groups.iter_mut().find(|g| g.request == req) { g.pending = false }
                        ControlResponse::AssignedGroup { epochs }
                    }
                    Err(e) => inconclusive(&e),
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
            status: serde_json::json!({"leader": true, "term": self.seen_term.load(Ordering::SeqCst), "workers": workers, "work": work, "validations_in_flight": st.inflight.len()}),
        }
    }

    // ------------------------------------------------------------ target work

    fn submit_work(&self, request: String, target: String, memory_mb: u64) -> ControlResponse {
        let mut st = self.state.lock().unwrap();
        let name = Name::parse(&target);
        if name.to_string().is_empty() { return refused("empty target name") }
        if !cfg!(feature = "mutate-no-request-dedup") {
            if let Some(j) = st.work.get(&request) {
                if j.target != name || j.memory_mb != memory_mb {
                    return refused("request ID already used for different work");
                }
                return ControlResponse::Duplicate { state: format!("{:?}", j.state) };
            }
        }
        if st.groups.iter().any(|g| g.names.contains(&name.to_string())) {
            return refused("target belongs to an assigned group; use the group workflow");
        }
        let queued = st.work.values().filter(|j| j.state == WorkState::Queued).count();
        if queued >= self.cfg.max_work_queue {
            return ControlResponse::Busy;
        }
        if !st.work.contains_key(&request) {
            st.order.push(request.clone());
        }
        st.work.insert(request, WorkJob { target: name, memory_mb, state: WorkState::Queued, attempts: 0 });
        ControlResponse::Queued
    }

    async fn poll(&self, w: WorkspaceId, token: Option<&str>) -> ControlResponse {
        // A job already assigned to this worker (after a reassignment) comes first.
        let pick = {
            let mut st = self.state.lock().unwrap();
            match st.workers.get(&w) {
                Some(i) if i.alive && i.lease_until > now_ms() => {}
                _ => return ControlResponse::Unknown,
            }
            if let Some(token) = token {
                if let Some(p) = st.poll_responses.get(token) {
                    if p.worker != w.hex() { return refused("poll request ID belongs to another worker") }
                    if let Some(work) = &p.work {
                        if let Some(j) = st.work.get(work) {
                            if let WorkState::Running { worker, epoch, .. } = j.state {
                                if worker == w && epoch != u64::MAX {
                                    return ControlResponse::Work { request: work.clone(), target: j.target.to_string(), epoch, memory_mb: j.memory_mb };
                                }
                            }
                        }
                    }
                    // A token is permanently bound to its first work. Once that
                    // work finishes or moves, a delayed retry cannot take a new job.
                    return ControlResponse::NoWork;
                }
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
                        if epoch != u64::MAX {
                            j.state = WorkState::Running { worker, epoch, delivered: true };
                            let response = ControlResponse::Work { request: r.clone(), target: j.target.to_string(), epoch, memory_mb: j.memory_mb };
                            if let Some(token) = token { st.remember_poll(token, &w, Some(r.clone())); }
                            return response;
                        }
                        pick = Some((r.clone(), j.target.clone(), j.memory_mb, j.attempts));
                        break;
                    }
                }
            }
            for r in &order {
                if pick.is_some() { break }
                let j = st.work.get_mut(r).unwrap();
                if j.state == WorkState::Queued && j.memory_mb <= free {
                    j.attempts += 1;
                    // Durable intent binds the chosen worker and attempt before T4.
                    j.state = WorkState::Running { worker: w, epoch: u64::MAX, delivered: false };
                    let mem = j.memory_mb;
                    pick = Some((r.clone(), j.target.clone(), mem, j.attempts));
                    st.workers.get_mut(&w).unwrap().used_mb += mem;
                    break;
                }
            }
            pick
        };
        let Some((request, target, memory_mb, attempt)) = pick else {
            if let Some(token) = token {
                self.state.lock().unwrap().remember_poll(token, &w, None);
            }
            return ControlResponse::NoWork
        };
        let req = format!("work/{request}/{attempt}");
        let term = match self.durable.current().await { Ok(Some(l)) => l.term, _ => return inconclusive("not controller leader") };
        if let Err(e) = self.save_state(term).await { return inconclusive(&e) }
        match self.durable.assign_group(&[target.clone()], w, req.as_bytes(), term).await.map(|v| v[0]) {
            Ok(epoch) => {
                let assigned = {
                    let mut st = self.state.lock().unwrap();
                    if let Some(j) = st.work.get_mut(&request) {
                        if matches!(j.state, WorkState::Running { worker, .. } if worker == w) {
                            j.state = WorkState::Running { worker: w, epoch, delivered: true };
                            true
                        } else { false }
                    } else { false }
                };
                if assigned {
                    if let Some(token) = token {
                        self.state.lock().unwrap().remember_poll(token, &w, Some(request.clone()));
                    }
                    if let Ok(ms) = std::env::var("PARALEAN_TEST_PAUSE_AFTER_ASSIGN_MS").unwrap_or_default().parse::<u64>() {
                        tokio::time::sleep(Duration::from_millis(ms)).await;
                    }
                    return ControlResponse::Work { request, target: target.to_string(), epoch, memory_mb };
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
    pub async fn expire_leases(self: &Arc<Self>) {
        let _guard = self.operation.lock().await;
        let lease = match self.durable.acquire_or_renew().await { Ok(Some(l)) => l, _ => return };
        if self.load_state().await.is_err() { return }
        self.on_leadership(lease.term);
        self.recover_pending().await;
        if self.expire_leases_inner(lease.term).await {
            let _ = self.save_state(lease.term).await;
        }
    }

    async fn expire_leases_inner(&self, term: u64) -> bool {
        if cfg!(feature = "mutate-no-lease-reassign") {
            return true;
        }
        let now = now_ms();
        let mut moves: Vec<(String, Name, WorkspaceId, u64)> = Vec::new();
        let mut group_moves: Vec<(Vec<Name>, WorkspaceId, String)> = Vec::new();
        {
            let mut st = self.state.lock().unwrap();
            let dead: Vec<WorkspaceId> =
                st.workers.iter().filter(|(_, i)| i.alive && i.lease_until <= now).map(|(w, _)| *w).collect();
            for d in &dead {
                st.workers.get_mut(d).unwrap().alive = false;
            }
            // A dead worker's poll tokens answer nothing any more (Poll needs a live lease).
            let dead_hex: Vec<String> = dead.iter().map(WorkspaceId::hex).collect();
            st.poll_responses.retain(|_, p| !dead_hex.contains(&p.worker));
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
                        // Keep the sentinel handover pending until T4 fences the
                        // expired owner. A crash must not restore Queued while the
                        // old owner still holds the prior target epoch.
                        j.state = WorkState::Running { worker: unowned(), epoch: u64::MAX, delivered: false };
                        moves.push((r.clone(), target, unowned(), attempts + 1));
                    }
                }
            }
            // Poll and lease-expiry handovers both persist an epoch=MAX intent
            // before T4. Resume any such intent after a crash, including a
            // sentinel fence for which there is no live worker to poll.
            for r in &st.order {
                if moves.iter().any(|(moved, ..)| moved == r) { continue }
                let j = &st.work[r];
                if let WorkState::Running { worker, epoch: u64::MAX, .. } = j.state {
                    moves.push((r.clone(), j.target.clone(), worker, j.attempts));
                }
            }
            for group in &mut st.groups {
                let owner = ws(&group.owner);
                if owner.is_some_and(|owner| dead.contains(&owner)) {
                    group.request = format!("group-expire/{}", group.request);
                    group.owner = unowned().hex();
                    group.pending = true;
                }
                if group.pending {
                    let Some(owner) = ws(&group.owner) else { continue };
                    group_moves.push((group.names.iter().map(|n| Name::parse(n)).collect(), owner, group.request.clone()));
                }
            }
        }
        // Persist the chosen owner and attempt before any assignment. A new
        // leader can either finish this exact T4 or, if that owner has since
        // expired, start a fresh attempt with a fresh request ID.
        if (!moves.is_empty() || !group_moves.is_empty()) && self.save_state(term).await.is_err() {
            return false;
        }
        for (r, target, to, attempt) in moves {
            let req = format!("work/{r}/{attempt}");
            let res = match self.durable.current().await {
                Ok(Some(lease)) => self.durable.assign_group(&[target.clone()], to, req.as_bytes(), lease.term).await.map(|v| v[0]),
                _ => Err("controller lost lease".into()),
            };
            if res.is_err() { return false }
            {
                let mut st = self.state.lock().unwrap();
                if let Some(j) = st.work.get_mut(&r) {
                    if let (Ok(epoch), WorkState::Running { worker, delivered, .. }) = (&res, j.state.clone()) {
                        if worker == to {
                            j.state = if to == unowned() {
                                WorkState::Queued
                            } else {
                                WorkState::Running { worker, epoch: *epoch, delivered }
                            };
                        }
                    }
                }
            }
            if let Ok(ms) = std::env::var("PARALEAN_TEST_PAUSE_AFTER_EXPIRE_T4_MS").unwrap_or_default().parse::<u64>() {
                tokio::time::sleep(Duration::from_millis(ms)).await;
            }
        }
        for (names, owner, req) in group_moves {
            let res = match self.durable.current().await {
                Ok(Some(lease)) => self.durable.assign_group(&names, owner, req.as_bytes(), lease.term).await,
                _ => Err("controller lost lease".into()),
            };
            if res.is_err() { return false }
            if let Some(group) = self.state.lock().unwrap().groups.iter_mut().find(|g| g.request == req) {
                group.pending = false;
            }
        }
        true
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
                Some(i) if i.alive && i.lease_until > now_ms() => {}
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
            // W2 A-4: a statement the authority pinned for the name replaces the worker's.
            let statement = match st.meta.target_statement(&name).await {
                Ok(pinned) => pinned.unwrap_or(statement),
                Err(e) => return inconclusive(&e.to_string()),
            };
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
        let req = job_key(&w, &job.body.request);
        let request = job.body.request.clone();

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
            match st.meta.is_cancelled(&w, &request).await {
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
                if let Ok(ms) = std::env::var("PARALEAN_TEST_PAUSE_AFTER_J1_MS").unwrap_or_default().parse::<u64>() {
                    tokio::time::sleep(Duration::from_millis(ms)).await;
                }
                // A finished request: the recorded receipt.
                if let Ok(Some(v)) = st.meta.get(st.meta.keys.job_receipt(&w, &request)).await {
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
            let call = paralean_validator_api::validate(&addr, job, &self.cfg.authority, &st.ring.validators, timeout);
            let resp = tokio::select! {
                r = call => r,
                _ = cancel.changed() => {
                    self.tell_cancel(Some(&job.body.worker), &job.body.request).await;
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
                    let term = match self.durable.current().await { Ok(Some(l)) => l.term, _ => return inconclusive("controller lost lease") };
                    let stored = match self.durable.record_receipt(&job.body.worker, &job.body.request, &r, term).await {
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

    async fn tell_cancel(&self, worker: Option<&WorkspaceId>, request: &[u8]) {
        let req = ValidatorRequest::Cancel { request: hex::encode(request), worker: worker.map(WorkspaceId::hex).unwrap_or_default() };
        for addr in &self.cfg.validators {
            let _: std::io::Result<ValidatorResponse> =
                rpc::call_authenticated_any(addr, &req, &self.cfg.authority, &self.cfg.store.ring.validators, Duration::from_secs(2)).await;
        }
    }

    /// Cancel `worker`'s `request`, or that request ID of every configured workspace.
    async fn cancel(&self, request: &str, worker: Option<WorkspaceId>) -> ControlResponse {
        let req = request.as_bytes().to_vec();
        let workers: Vec<WorkspaceId> = match worker {
            Some(w) => vec![w],
            None => {
                let mut all: Vec<WorkspaceId> = self.cfg.store.ring.writers.keys().copied().collect();
                all.extend(self.state.lock().unwrap().workers.keys().copied());
                all.sort();
                all.dedup();
                all
            }
        };
        // J3 first: from here on no T1 accepts a receipt bound to this request.
        for w in &workers {
            if let Err(e) = self.cfg.store.meta.cancel_job(w, &req).await {
                return inconclusive(&e.to_string());
            }
        }
        {
            let mut s = self.state.lock().unwrap();
            for w in &workers {
                if let Some(f) = s.inflight.get(&job_key(w, &req)) {
                    let _ = f.cancel.send(true);
                }
            }
            if let Some(j) = s.work.get_mut(request) {
                let running = match j.state { WorkState::Running { worker, .. } => Some(worker), _ => None };
                if worker.is_none() || running == worker {
                    let mem = j.memory_mb;
                    j.state = WorkState::Cancelled;
                    if let Some(i) = running.and_then(|r| s.workers.get_mut(&r)) {
                        i.used_mb = i.used_mb.saturating_sub(mem);
                    }
                }
            }
        }
        self.tell_cancel(worker.as_ref(), &req).await;
        ControlResponse::Cancelled
    }
}

fn refused(reason: &str) -> ControlResponse {
    ControlResponse::Refused { reason: reason.into() }
}
fn inconclusive(reason: &str) -> ControlResponse {
    ControlResponse::Inconclusive { reason: reason.into() }
}

#[cfg(test)]
mod snapshot_tests {
    use super::*;

    fn snapshot_len(st: &State) -> usize {
        serde_json::to_vec(&st.snapshot()).unwrap().len()
    }

    #[test]
    fn worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot() {
        let mut st = State::default();
        let (a, b) = (WorkspaceId::derive("snapshot-a"), WorkspaceId::derive("snapshot-b"));
        st.remember_poll("b/kept", &b, None);
        // A worker polling with a fresh token each time, many times over.
        for i in 0..5000 {
            st.remember_poll(&format!("a/{i}"), &a, None);
        }
        let mine = st.poll_responses.values().filter(|p| p.worker == a.hex()).count();
        assert_eq!(mine, MAX_POLL_TOKENS_PER_WORKER);
        assert!(st.poll_responses.contains_key("a/4999") && !st.poll_responses.contains_key("a/0"));
        assert!(st.poll_responses.contains_key("b/kept"), "another worker's token was evicted");
        // Finished work beyond the bound goes, oldest first; queued and running work stays.
        for i in 0..3000 {
            let r = format!("w/{i}");
            let state = match i % 3 { 0 => WorkState::Done, 1 => WorkState::Failed, _ => WorkState::Cancelled };
            st.order.push(r.clone());
            st.work.insert(r, WorkJob { target: Name::parse("T.x"), memory_mb: 1, state, attempts: 1 });
        }
        for i in 0..5 {
            let r = format!("live/{i}");
            st.order.insert(0, r.clone());
            st.work.insert(r, WorkJob { target: Name::parse("T.y"), memory_mb: 1, state: WorkState::Queued, attempts: 0 });
        }
        st.prune_finished_work();
        assert_eq!(st.work.len(), MAX_FINISHED_WORK + 5);
        assert_eq!(st.order.len(), st.work.len());
        assert!(st.order.iter().all(|r| st.work.contains_key(r)));
        assert!((0..5).all(|i| st.work.contains_key(&format!("live/{i}"))));
        assert!(st.work.contains_key("w/2999") && !st.work.contains_key("w/0"));
        let bounded = snapshot_len(&st);
        for i in 0..3000 {
            st.remember_poll(&format!("again/{i}"), &a, None);
        }
        st.prune_finished_work();
        assert!(snapshot_len(&st) <= bounded + 4096, "snapshot grew with poll tokens");
    }
}
