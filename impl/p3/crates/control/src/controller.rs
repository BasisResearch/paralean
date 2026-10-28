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
//! fence even if it is still running. Its job remains available for a later
//! registered worker to claim.
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
//! **Batches.** `ValidateBatch` from a registered coordinator validates the publication
//! members of one atomic batch (T12). The controller signs the batch intent, issues each
//! member's envelope as `Validate` does but bound to the intent (`batch`), under the
//! member's workspace and the request ID `batch/<coordinator>/<request>` (J1), and sends the
//! envelopes in order as one `ValidateBatch`, so an earlier member's receipt serves a later
//! member as a dependency. It answers with every member's receipt or none.
//!
//! Backpressure: at most `max_work_queue` queued work jobs and `max_validations` validations
//! in flight; beyond that the answer is `Busy` and nothing is recorded.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

use paralean_store::receipt::{check_bound, prepared_of, sort_targets, JobEnvelope, SignedJob, TargetBinding};
use foundationdb::{KeySelector, RangeOption};
use foundationdb::options::StreamingMode;
use paralean_store::{BatchIntent, BatchMember, Id, Name, Receipt, SignedBatch, Signer, Store, WorkspaceId, MAX_BATCH_MEMBERS};
use paralean_validator_api::{decode_receipt, rpc, ValidatorRequest, ValidatorResponse, MAX_BATCH_JOBS};
use serde::{Deserialize, Serialize};
use tokio::net::TcpListener;
use tokio::sync::watch;
use tokio::task::JoinHandle;
use crate::durable::{Durable, GroupRequest, PollReplay, TerminalState, WorkReplay};
use crate::gc::GcConfig;
use crate::topology::{self, MoveOutcome, MoveRecord, MoveState};

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

/// One member of [`ControlRequest::ValidateBatch`], in commit order.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum BatchMemberReq {
    /// A group `worker` publishes, validated as `Validate` validates it.
    Publish {
        worker: String,
        request: String,
        group: String,
        capsule: String,
        #[serde(default)]
        deps: Vec<String>,
        #[serde(default)]
        targets: Vec<TargetReq>,
    },
    /// A position of the published group `target` that `worker` deletes (`position`: a
    /// marker ID, or empty).
    Tombstone { worker: String, target: String, #[serde(default)] position: String },
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
    /// Validate the publication members of one atomic batch; `coordinator` (a registered
    /// workspace) signs the request.
    ValidateBatch { coordinator: String, request: String, members: Vec<BatchMemberReq> },
    /// Cancel `worker`'s request (hex workspace ID), or that request ID of every
    /// configured workspace when `worker` is empty.
    Cancel { request: String, #[serde(default)] worker: String },
    /// `statement` (hex P1 `typeHash`) pins the statement every proof of the target must
    /// prove (W2 A-4); `statements` pins one per target. Pins are write-once.
    Assign { target: String, worker: String, #[serde(default)] statement: String },
    AssignGroup { targets: Vec<String>, worker: String, #[serde(default)] request: String,
        #[serde(default)] statements: Vec<String> },
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
    /// The signed batch intent and, for its publication members in order, the receipts and
    /// envelopes (hex bytes).
    BatchReceipts { intent: String, receipts: Vec<String>, jobs: Vec<String> },
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
    settled_tick: Option<u64>,
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
    history_work_cursor: usize,
    history_poll_cursor: Option<String>,
    history_next_poll: bool,
    history_compacted_work: u64,
    history_compacted_polls: u64,
    /// Dynamic topology: the bucket of each work request (from its route). Stored with
    /// the work entry; empty in a fixed topology.
    work_buckets: BTreeMap<String, u16>,
}

/// Bounds on the controller snapshot, which every operation loads and saves. Request IDs
/// and poll tokens are chosen by clients; finished work and answered poll tokens are
/// dropped oldest first beyond these counts.
pub const MAX_REQUEST_ID: usize = 256;
pub const MAX_POLL_TOKENS_PER_WORKER: usize = 16;
pub const MAX_FINISHED_WORK: usize = 1024;
/// Replay-row bytes one save may spill (below `Durable`'s 256 KiB history write budget).
const SPILL_BUDGET: usize = 200 * 1024;
/// The largest replay row `Durable` writes (its `MAX_HISTORY_VALUE`).
const SPILL_ROW_LIMIT: usize = 90 * 1024;

pub struct ControlPlane {
    pub cfg: ControllerConfig,
    state: Mutex<State>,
    durable: Durable,
    operation: tokio::sync::Mutex<()>,
    seen_term: AtomicU64,
    gc: GcConfig,
    gc_cursor: Mutex<Option<String>>,
    /// Head generation of the last load or save (dynamic topology: saves compare it).
    loaded_generation: Mutex<Option<u64>>,
    /// Validations in progress per bucket (dynamic topology), from routing to the end of
    /// their dispatch. An export waits until its buckets have none.
    active: Arc<Mutex<HashMap<u16, usize>>>,
    /// Buckets of this shard's active moves, refreshed by every operation.
    moving: Mutex<HashSet<u16>>,
    /// Test hook: a replica that does not run move steps on its own (as if it died
    /// before its next tick). `drive_moves_now` still runs them.
    move_steps_paused: std::sync::atomic::AtomicBool,
}

/// One in-progress validation of a bucket; the count drops when the last clone goes.
pub struct ActiveGuard { map: Arc<Mutex<HashMap<u16, usize>>>, bucket: u16 }

impl ActiveGuard {
    fn enter(map: &Arc<Mutex<HashMap<u16, usize>>>, bucket: u16) -> Arc<ActiveGuard> {
        *map.lock().unwrap().entry(bucket).or_insert(0) += 1;
        Arc::new(ActiveGuard { map: map.clone(), bucket })
    }
}

impl Drop for ActiveGuard {
    fn drop(&mut self) {
        let mut map = self.map.lock().unwrap();
        if let Some(n) = map.get_mut(&self.bucket) {
            *n -= 1;
            if *n == 0 { map.remove(&self.bucket); }
        }
    }
}

/// Where a request goes in a dynamic topology.
enum Route { Local, Mine(u16), Moving, Other }

/// The moved part of a source snapshot (`controller/handoff/<move>`).
#[derive(Serialize, Deserialize, Default)]
struct Handoff {
    work: Vec<(String, StoredWork)>,
    groups: Vec<StoredGroup>,
    workers: BTreeMap<String, StoredWorker>,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct HistoryReport {
    pub stamped_work: usize,
    pub stamped_polls: usize,
    pub compacted_work: usize,
    pub compacted_polls: usize,
}

struct AbortOnDrop(JoinHandle<()>);

fn gc_sweep_due(now: u64, next_eligible: u64) -> bool {
    if cfg!(feature = "mutate-gc-modulo-schedule") {
        now % 8 == 0
    } else {
        now >= next_eligible
    }
}

#[cfg(test)]
mod gc_schedule_tests {
    use super::gc_sweep_due;

    #[test]
    fn gc_schedule_progresses_when_other_replica_takes_every_multiple_of_eight() {
        let mut next_eligible = 0;
        let mut sweeps = Vec::new();
        // A second replica receives every even tick. This leader sees no
        // multiple of eight, but must still make repeated GC progress.
        for now in (1..=33).step_by(2) {
            if gc_sweep_due(now, next_eligible) {
                sweeps.push(now);
                next_eligible = now + 8;
            }
        }
        assert_eq!(sweeps, vec![1, 9, 17, 25, 33]);
    }
}

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
    #[serde(default)]
    history_work_cursor: usize,
    #[serde(default)]
    history_poll_cursor: Option<String>,
    #[serde(default)]
    history_next_poll: bool,
    #[serde(default)]
    history_compacted_work: u64,
    #[serde(default)]
    history_compacted_polls: u64,
}

#[derive(Clone, Serialize, Deserialize)]
struct StoredPoll { worker: String, work: Option<String>, #[serde(default)] seq: u64,
    #[serde(default)] epoch: Option<u64>, #[serde(default)] created_tick: Option<u64> }

#[derive(Clone, Serialize, Deserialize)]
struct StoredGroup {
    names: Vec<String>,
    owner: String,
    request: String,
    pending: bool,
    /// Dynamic topology: the bucket the group's names are claimed for.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    bucket: Option<u16>,
}

#[derive(Clone, Serialize, Deserialize)]
struct StoredWorker { capacity_mb: u64, used_mb: u64, lease_until: u64, alive: bool }

#[derive(Clone, Serialize, Deserialize)]
struct StoredWork { target: String, memory_mb: u64, state: StoredWorkState, attempts: u64,
    #[serde(default)] settled_tick: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")] bucket: Option<u16> }

#[derive(Clone, Serialize, Deserialize)]
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
            work: self.work.iter().map(|(r, j)| (r.clone(), StoredWork { target: j.target.to_string(), memory_mb: j.memory_mb, state: StoredWorkState::from(&j.state), attempts: j.attempts, settled_tick: j.settled_tick,
                bucket: self.work_buckets.get(r).copied() })).collect(),
            order: self.order.clone(), next_validator: self.next_validator, groups: self.groups.clone(), recovery_cursor: self.recovery_cursor.clone(), recovering: self.recovering, poll_responses: self.poll_responses.clone(),
            poll_seq: self.poll_seq,
            history_work_cursor: self.history_work_cursor, history_poll_cursor: self.history_poll_cursor.clone(),
            history_next_poll: self.history_next_poll,
            history_compacted_work: self.history_compacted_work, history_compacted_polls: self.history_compacted_polls,
        }
    }
    fn restore(&mut self, s: Snapshot) {
        self.workers = s.workers.into_iter().filter_map(|(id, i)| ws(&id).map(|id| (id, WorkerInfo { capacity_mb: i.capacity_mb, used_mb: i.used_mb, lease_until: i.lease_until, alive: i.alive }))).collect();
        self.work_buckets = s.work.iter().filter_map(|(r, j)| j.bucket.map(|b| (r.clone(), b))).collect();
        self.work = s.work.into_iter().filter_map(|(r, j)| Some((r, WorkJob { target: Name::parse(&j.target), memory_mb: j.memory_mb, state: j.state.restore()?, attempts: j.attempts, settled_tick: j.settled_tick }))).collect();
        self.order = s.order;
        self.next_validator = s.next_validator;
        self.groups = s.groups;
        self.recovery_cursor = s.recovery_cursor;
        self.recovering = s.recovering;
        self.poll_responses = s.poll_responses;
        self.poll_seq = s.poll_seq;
        self.history_work_cursor = s.history_work_cursor;
        self.history_poll_cursor = s.history_poll_cursor;
        self.history_next_poll = s.history_next_poll;
        self.history_compacted_work = s.history_compacted_work;
        self.history_compacted_polls = s.history_compacted_polls;
    }

    /// Bind a poll token to its answer. `save_state` bounds how many stay in the snapshot.
    fn remember_poll(&mut self, token: &str, worker: &WorkspaceId, work: Option<String>, epoch: Option<u64>, now: u64) {
        self.poll_seq += 1;
        self.poll_responses.insert(token.into(), StoredPoll { worker: worker.hex(), work, seq: self.poll_seq, epoch, created_tick: Some(now) });
    }

    /// W2-33: keep the snapshot every operation loads and saves bounded, whatever request
    /// IDs and poll tokens clients choose. A worker keeps its newest
    /// `MAX_POLL_TOKENS_PER_WORKER` tokens (one poll is outstanding at a time, so a token
    /// only has to outlive the retries of its own call; workers are configured workspaces,
    /// so this bounds all tokens, and a worker that re-registers keeps them); finished
    /// work beyond `MAX_FINISHED_WORK` goes oldest first, once no remaining token names
    /// it. Like W4 history compaction, an entry leaves the snapshot only as an immutable
    /// replay row that `save_with_history` commits with it, so a retry of a dropped token
    /// or a resubmitted request still resolves to its first answer. At most `budget`
    /// bytes of rows move per save; the rest move on later saves.
    fn spill_over_caps(&mut self, budget: usize) -> (Vec<WorkReplay>, Vec<PollReplay>) {
        let (mut work_rows, mut poll_rows, mut bytes) = (Vec::new(), Vec::new(), 0usize);
        // A row over FDB's value limit can never be written (W4 compaction skips it too):
        // it stays in the snapshot rather than failing every save. Otherwise stop at the budget.
        enum Fit { Yes, Skip, Full }
        let mut fits = |size: usize| if size > SPILL_ROW_LIMIT { Fit::Skip }
            else if bytes + size <= budget { bytes += size; Fit::Yes } else { Fit::Full };
        if !cfg!(feature = "mutate-unbounded-poll-responses") {
            let mut by_worker: BTreeMap<String, Vec<(u64, String)>> = BTreeMap::new();
            for (t, p) in &self.poll_responses { by_worker.entry(p.worker.clone()).or_default().push((p.seq, t.clone())); }
            for (_, mut mine) in by_worker {
                mine.sort();
                for (_, token) in &mine[..mine.len().saturating_sub(MAX_POLL_TOKENS_PER_WORKER)] {
                    let p = &self.poll_responses[token];
                    let row = PollReplay { token: token.clone(), worker: p.worker.clone(), work: p.work.clone(), epoch: p.epoch };
                    match fits(serde_json::to_vec(&row).map_or(usize::MAX, |v| v.len())) {
                        Fit::Yes => {}
                        Fit::Skip => continue,
                        Fit::Full => break,
                    }
                    self.poll_responses.remove(token);
                    poll_rows.push(row);
                }
            }
        }
        if !cfg!(feature = "mutate-no-work-gc") {
            let terminal = |j: &WorkJob| match j.state {
                WorkState::Done => Some(TerminalState::Done),
                WorkState::Failed => Some(TerminalState::Failed),
                WorkState::Cancelled => Some(TerminalState::Cancelled),
                _ => None,
            };
            let mut excess = self.work.values().filter(|j| terminal(j).is_some()).count().saturating_sub(MAX_FINISHED_WORK);
            let named: std::collections::BTreeSet<&str> = self.poll_responses.values().filter_map(|p| p.work.as_deref()).collect();
            for r in &self.order {
                if excess == 0 { break }
                let Some(j) = self.work.get(r) else { continue };
                let Some(state) = terminal(j) else { continue };
                if named.contains(r.as_str()) { continue }
                let row = WorkReplay { request: r.clone(), target: j.target.to_string(), memory_mb: j.memory_mb, state };
                match fits(serde_json::to_vec(&row).map_or(usize::MAX, |v| v.len())) {
                    Fit::Yes => {}
                    Fit::Skip => continue,
                    Fit::Full => break,
                }
                work_rows.push(row);
                excess -= 1;
            }
            let moved: std::collections::BTreeSet<&str> = work_rows.iter().map(|r| r.request.as_str()).collect();
            self.order.retain(|r| !moved.contains(r.as_str()));
            self.work.retain(|r, _| !moved.contains(r.as_str()));
        }
        (work_rows, poll_rows)
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
        | ControlRequest::ValidateBatch { request, .. }
        | ControlRequest::Cancel { request, .. }
        | ControlRequest::AssignGroup { request, .. } => Some(request),
        _ => None,
    }
}

/// The target names a validation binds (every publication member's, for a batch).
fn validation_targets(req: &ControlRequest) -> Vec<String> {
    match req {
        ControlRequest::Validate { targets, .. } => targets.iter().map(|t| t.name.clone()).collect(),
        ControlRequest::ValidateBatch { members, .. } => members.iter().flat_map(|m| match m {
            BatchMemberReq::Publish { targets, .. } => targets.iter().map(|t| t.name.clone()).collect(),
            BatchMemberReq::Tombstone { .. } => vec![],
        }).collect(),
        _ => vec![],
    }
}

/// The in-flight key of a validation: (requesting workspace, request ID).
fn job_key(worker: &WorkspaceId, request: &[u8]) -> Vec<u8> {
    let mut k = worker.0.to_vec();
    k.extend_from_slice(request);
    k
}

/// The envelope request ID of a batch member (and the intent's request): in the
/// coordinator's namespace, so a coordinator cannot occupy a member workspace's own IDs.
fn batch_request(coordinator: &WorkspaceId, request: &str) -> Vec<u8> {
    format!("batch/{}/{request}", coordinator.hex()).into_bytes()
}

/// Call a controller replica list such as `host-a:9000,host-b:9000`.
/// The signed request is regenerated for each connection's challenge, while its
/// logical request ID stays unchanged across retries and leader failover.
/// The monitor's scheduling interval: one logical clock advance per replica.
pub fn monitor_interval(lease: Duration) -> Duration {
    (lease / 8).max(Duration::from_millis(20))
}

pub async fn call_controller(
    addrs: &str, req: &ControlRequest, signer: &Signer, authority_public: &[u8; 32], total_timeout: Duration,
) -> std::io::Result<ControlResponse> {
    let endpoints: Vec<&str> = addrs.split(',').map(str::trim).filter(|s| !s.is_empty()).collect();
    if endpoints.is_empty() {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidInput, "no controller address"));
    }
    let validation = matches!(req, ControlRequest::Validate { .. } | ControlRequest::ValidateBatch { .. });
    let budget = if validation { total_timeout } else { total_timeout.min(Duration::from_secs(15)) };
    let deadline = Instant::now() + budget;
    let mut last_error = None;
    let mut follower = None;
    loop {
        for addr in &endpoints {
            let left = deadline.saturating_duration_since(Instant::now());
            if left.is_zero() { break }
            let one = left.min(if validation { Duration::from_secs(30) } else { Duration::from_secs(3) });
            match rpc::call_authenticated(addr, req, signer, authority_public, one).await {
                Ok(ControlResponse::Inconclusive { reason }) if reason == "not controller leader" || reason == "not controller shard"
                    || reason == "bucket moving" => {
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
        Self::new_shard(cfg, 0, 1)
    }

    pub fn new_shard(cfg: ControllerConfig, shard: u32, shards: u32) -> Arc<ControlPlane> {
        Self::new_shard_with_gc(cfg, shard, shards, GcConfig::default())
    }

    pub fn new_shard_with_gc(cfg: ControllerConfig, shard: u32, shards: u32, gc: GcConfig) -> Arc<ControlPlane> {
        let durable = Durable::new_shard(cfg.store.clone(), cfg.lease, shard, shards);
        Self::with_durable(cfg, durable, gc)
    }

    /// A member `shard` of a dynamic topology (`paralean-p3 topology init`).
    pub fn new_dynamic(cfg: ControllerConfig, shard: u32, gc: GcConfig) -> Arc<ControlPlane> {
        let durable = Durable::new_dynamic(cfg.store.clone(), cfg.lease, shard);
        Self::with_durable(cfg, durable, gc)
    }

    fn with_durable(cfg: ControllerConfig, durable: Durable, gc: GcConfig) -> Arc<ControlPlane> {
        Arc::new(ControlPlane { cfg, state: Mutex::new(State::default()), durable, operation: tokio::sync::Mutex::new(()), seen_term: AtomicU64::new(0), gc, gc_cursor: Mutex::new(None),
            loaded_generation: Mutex::new(None), active: Arc::new(Mutex::new(HashMap::new())), moving: Mutex::new(HashSet::new()),
            move_steps_paused: std::sync::atomic::AtomicBool::new(false) })
    }

    /// This replica's durable state (its shard, lease and fenced writes).
    pub fn durable(&self) -> &Durable { &self.durable }

    /// Test hook: stop (or resume) running move steps on ticks and requests.
    pub fn pause_move_steps(&self, paused: bool) { self.move_steps_paused.store(paused, Ordering::SeqCst) }

    /// Validate and initialize the deployment's fixed shard topology before listening.
    pub async fn verify_topology(&self) -> Result<(), String> {
        self.durable.acquire_or_renew().await.map(|_| ())
    }

    /// Pin a current or retired controller snapshot under this replica's lease.
    pub async fn retain_snapshot(&self, hash: &str) -> Result<(), String> {
        let _guard = self.operation.lock().await;
        let lease = self.durable.acquire_or_renew().await?.ok_or("not controller leader")?;
        self.durable.retain_snapshot(hash, lease.term).await
    }

    pub async fn release_snapshot(&self, hash: &str) -> Result<(), String> {
        let _guard = self.operation.lock().await;
        let lease = self.durable.acquire_or_renew().await?.ok_or("not controller leader")?;
        self.durable.release_snapshot(hash, lease.term).await
    }

    /// Move a bounded page of settled history to immutable replay rows. Replay
    /// reads remain active even if GC is disabled after this pass.
    pub async fn compact_history_once(self: &Arc<Self>) -> Result<HistoryReport, String> {
        if !self.gc.enabled && !cfg!(feature = "mutate-history-no-opt-in") { return Err("controller history GC is disabled".into()) }
        if self.gc.grace_ticks == 0 || self.gc.scan_limit == 0 || self.gc.scan_limit > 1024 {
            return Err("controller history GC requires positive grace and a scan limit of 1..=1024".into());
        }
        let _guard = self.operation.lock().await;
        let lease = self.durable.acquire_or_renew().await?.ok_or("not controller leader")?;
        self.load_state().await?;
        self.on_leadership(lease.term);
        let now = self.durable.clock().await?;
        let mut report = HistoryReport::default();
        let mut work_rows = Vec::new();
        let mut poll_rows = Vec::new();
        let mut write_bytes = 0usize;
        let snapshot = {
            let mut st = self.state.lock().unwrap();
            let poll_keys: Vec<String> = st.poll_responses.keys().cloned().collect();
            let order = st.order.clone();
            let (poll_budget, work_budget) = if cfg!(feature = "mutate-history-no-fair-scan") {
                let p = poll_keys.len().min(self.gc.scan_limit);
                (p, self.gc.scan_limit - p)
            } else if poll_keys.is_empty() {
                (0, self.gc.scan_limit)
            } else if order.is_empty() {
                (self.gc.scan_limit, 0)
            } else if self.gc.scan_limit == 1 {
                let poll_turn = st.history_next_poll;
                st.history_next_poll = !poll_turn;
                (usize::from(poll_turn), usize::from(!poll_turn))
            } else {
                let p = (self.gc.scan_limit / 2).min(poll_keys.len());
                let w = (self.gc.scan_limit - p).min(order.len());
                let p = (self.gc.scan_limit - w).min(poll_keys.len());
                (p, w)
            };
            if !poll_keys.is_empty() {
                let start = st.history_poll_cursor.as_ref()
                    .and_then(|cursor| poll_keys.iter().position(|key| key > cursor)).unwrap_or(0);
                for offset in 0..poll_keys.len().min(poll_budget) {
                    let token = &poll_keys[(start + offset) % poll_keys.len()];
                    st.history_poll_cursor = Some(token.clone());
                    let (worker, work, epoch, created_tick) = {
                        let p = st.poll_responses.get_mut(token).unwrap();
                        if p.created_tick.is_none() { p.created_tick = Some(now); report.stamped_polls += 1; }
                        (p.worker.clone(), p.work.clone(), p.epoch, p.created_tick.unwrap())
                    };
                    if !cfg!(feature = "mutate-history-no-grace") &&
                        (now < created_tick || now - created_tick < self.gc.grace_ticks) { continue }
                    if let Some(r) = &work {
                        let Some(j) = st.work.get_mut(r) else { continue };
                        if !matches!(j.state, WorkState::Done | WorkState::Failed | WorkState::Cancelled) { continue }
                        if j.settled_tick.is_none() { j.settled_tick = Some(now); report.stamped_work += 1; }
                        let settled = j.settled_tick.unwrap();
                        if !cfg!(feature = "mutate-history-no-grace") && !cfg!(feature = "mutate-history-no-terminal-grace") &&
                            (now < settled || now - settled < self.gc.grace_ticks) { continue }
                    }
                    let row = PollReplay { token: token.clone(), worker, work, epoch };
                    let size = serde_json::to_vec(&row).map_err(|e| e.to_string())?.len();
                    if size > 90 * 1024 || write_bytes + size > 200 * 1024 { continue }
                    write_bytes += size;
                    poll_rows.push(row);
                }
                for row in &poll_rows { st.poll_responses.remove(&row.token); }
            }
            if !order.is_empty() && work_budget > 0 {
                let start = st.history_work_cursor % order.len();
                let count = order.len().min(work_budget);
                for offset in 0..count {
                    let request = &order[(start + offset) % order.len()];
                    let (target, memory_mb, state, settled_tick) = {
                        let j = st.work.get_mut(request).ok_or("controller work order is corrupt")?;
                        let terminal = match j.state {
                            WorkState::Done => Some(TerminalState::Done),
                            WorkState::Failed => Some(TerminalState::Failed),
                            WorkState::Cancelled => Some(TerminalState::Cancelled),
                            _ if cfg!(feature = "mutate-history-prune-active") => {
                                j.settled_tick = Some(now.saturating_sub(self.gc.grace_ticks));
                                Some(TerminalState::Done)
                            }
                            _ => None,
                        };
                        if terminal.is_some() && j.settled_tick.is_none() {
                            j.settled_tick = Some(now);
                            report.stamped_work += 1;
                        }
                        (j.target.to_string(), j.memory_mb, terminal, j.settled_tick)
                    };
                    let (Some(state), Some(settled_tick)) = (state, settled_tick) else { continue };
                    if !cfg!(feature = "mutate-history-no-grace") &&
                        (now < settled_tick || now - settled_tick < self.gc.grace_ticks) { continue }
                    // All poll tokens for this job must move first. This keeps
                    // every first selection recoverable across an unknown commit.
                    if st.poll_responses.values().any(|p| p.work.as_deref() == Some(request)) { continue }
                    let row = WorkReplay { request: request.clone(), target, memory_mb, state };
                    let size = serde_json::to_vec(&row).map_err(|e| e.to_string())?.len();
                    if size > 90 * 1024 || write_bytes + size > 200 * 1024 { continue }
                    write_bytes += size;
                    work_rows.push(row);
                }
                if work_rows.is_empty() { st.history_work_cursor = (start + count) % order.len(); }
            }
            if !work_rows.is_empty() {
                let removed: std::collections::HashSet<&str> = work_rows.iter().map(|r| r.request.as_str()).collect();
                st.order.retain(|r| !removed.contains(r.as_str()));
                for row in &work_rows { st.work.remove(&row.request); }
                st.history_work_cursor = 0;
            }
            report.compacted_work = work_rows.len();
            report.compacted_polls = poll_rows.len();
            st.history_compacted_work = st.history_compacted_work.saturating_add(report.compacted_work as u64);
            st.history_compacted_polls = st.history_compacted_polls.saturating_add(report.compacted_polls as u64);
            serde_json::to_vec(&st.snapshot()).map_err(|e| e.to_string())?
        };
        if let Err(e) = self.save_bytes(&snapshot, lease.term, &work_rows, &poll_rows).await {
            let _ = self.load_state().await;
            return Err(e);
        }
        if !work_rows.is_empty() || !poll_rows.is_empty() {
            if let Ok(ms) = std::env::var("PARALEAN_TEST_PAUSE_AFTER_HISTORY_COMMIT_MS").unwrap_or_default().parse::<u64>() {
                tokio::time::sleep(Duration::from_millis(ms)).await;
            }
        }
        Ok(report)
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
                | ControlRequest::Validate { worker, .. }
                | ControlRequest::ValidateBatch { coordinator: worker, .. } => ws(worker).and_then(|w| ring.writer(&w).copied()).is_some_and(|key| &key == public),
                _ => &ring.authority == public,
            }
        }, move |req: ControlRequest| {
            let me = me.clone();
            async move { me.handle(req).await }
        });
        let server = AbortOnDrop(server);
        let me = self.clone();
        tokio::spawn(async move {
            let mut tick = tokio::time::interval(monitor_interval(me.cfg.lease));
            tick.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            let mut next_gc_tick = 0;
            loop {
                tick.tick().await;
                let now = me.durable.tick().await.ok();
                me.expire_leases().await;
                if let Some(now) = now.filter(|n| me.gc.enabled && gc_sweep_due(*n, next_gc_tick)) {
                    if let Ok(Some(lease)) = me.durable.current().await {
                        let cursor = me.gc_cursor.lock().unwrap().clone();
                        if let Ok(report) = me.durable.collect_retired_snapshots(lease.term, &me.gc, cursor.as_deref()).await {
                            *me.gc_cursor.lock().unwrap() = report.next_after;
                            next_gc_tick = now.saturating_add(8);
                        }
                    }
                }
                if server.0.is_finished() {
                    return;
                }
            }
        })
    }

    pub async fn handle(self: &Arc<Self>, req: ControlRequest) -> ControlResponse {
        // Before routing: shard lookups and W4's work-shard reservation key on the ID.
        if let Some(id) = request_id(&req) {
            if id.len() > MAX_REQUEST_ID && !cfg!(feature = "mutate-unbounded-poll-responses") {
                return refused(&format!("request ID longer than {MAX_REQUEST_ID} bytes"));
            }
        }
        if self.durable.dynamic { return self.handle_dynamic(req).await }
        match self.request_shard(&req).await {
            Ok(Some(shard)) if shard != self.durable.shard => return inconclusive("not controller shard"),
            Err(e) => return inconclusive(&e),
            _ => {}
        }
        // A long validation may outlive a worker heartbeat. J1/J2 persist its
        // envelope and receipt independently; the controller snapshot is only read.
        if matches!(req, ControlRequest::Validate { .. } | ControlRequest::ValidateBatch { .. }) {
            let term = {
                let _guard = self.operation.lock().await;
                let Ok(Some(lease)) = self.durable.acquire_or_renew().await else { return inconclusive("not controller leader") };
                if let Err(e) = self.load_state().await { return inconclusive(&e) }
                let takeover = self.on_leadership(lease.term);
                if takeover { self.recover_pending(lease.term).await }
                if let Err(e) = self.save_state(lease.term).await { return inconclusive(&e) }
                lease.term
            };
            return self.handle_inner(req, term, None, None).await;
        }
        let _guard = self.operation.lock().await;
        let lease = match self.durable.acquire_or_renew().await {
            Ok(Some(l)) => l,
            Ok(None) => {
                if matches!(req, ControlRequest::Status) {
                    return ControlResponse::Status { status: serde_json::json!({"leader": false, "shard": self.durable.shard, "shards": self.durable.shards}) };
                }
                return inconclusive("not controller leader");
            }
            Err(e) => return inconclusive(&e),
        };
        if let Err(e) = self.load_state().await { return inconclusive(&e) }
        let takeover = self.on_leadership(lease.term);
        if takeover {
            self.recover_pending(lease.term).await;
        }
        if let ControlRequest::SubmitWork { request, target, .. } = &req {
            if let Err(e) = self.durable.reserve_work_shard(request, &Name::parse(target), lease.term).await { return refused(&e) }
        }
        let resp = self.handle_inner(req, lease.term, None, None).await;
        if let Err(e) = self.save_state(lease.term).await { return inconclusive(&e) }
        resp
    }

    /// `handle` in a dynamic topology: requests route by bucket; a bucket with a move in
    /// progress answers the retryable `bucket moving`; pending move steps run first.
    async fn handle_dynamic(self: &Arc<Self>, req: ControlRequest) -> ControlResponse {
        // A request for another shard's bucket goes there before this replica leads.
        if let Ok(Route::Other) = self.route_dynamic(&req).await { return inconclusive("not controller shard") }
        let guard = self.operation.lock().await;
        let lease = match self.durable.acquire_or_renew().await {
            Ok(Some(l)) => l,
            Ok(None) => {
                if matches!(req, ControlRequest::Status) {
                    return ControlResponse::Status { status: serde_json::json!({"leader": false, "shard": self.durable.shard, "dynamic": true}) };
                }
                return inconclusive("not controller leader");
            }
            // A retired shard (or one never added) serves nothing; clients try the others.
            Err(e) if e.contains("retired") || e.contains("not in the topology") => return inconclusive("not controller shard"),
            Err(e) => return inconclusive(&e),
        };
        if let Err(e) = self.begin_locked(lease.term).await { return inconclusive(&e) }
        // Re-route under the operation lock: no export of this shard can interleave now.
        let bucket = match self.route_dynamic(&req).await {
            Ok(Route::Local) => None,
            Ok(Route::Mine(b)) => Some(b),
            Ok(Route::Moving) => return inconclusive("bucket moving"),
            Ok(Route::Other) => return inconclusive("not controller shard"),
            Err(e) => return inconclusive(&e),
        };
        if matches!(req, ControlRequest::Validate { .. }) {
            // Counted before J1 and until its dispatch ends: an export of the bucket waits.
            let active = bucket.map(|b| ActiveGuard::enter(&self.active, b));
            drop(guard);
            return self.handle_inner(req, lease.term, bucket, active).await;
        }
        let mut bucket = bucket;
        if let ControlRequest::SubmitWork { request, target, .. } = &req {
            match self.durable.reserve_work(request, &Name::parse(target), lease.term).await {
                Ok(b) => bucket = b,
                Err(e) if e == "bucket moving" => return inconclusive(&e),
                Err(e) if e.contains("another controller shard") => return inconclusive("not controller shard"),
                Err(e) if e.contains("lost lease") => return inconclusive(&e),
                Err(e) => return refused(&e),
            }
        }
        let resp = self.handle_inner(req, lease.term, bucket, None).await;
        if let Err(e) = self.save_state(lease.term).await { return inconclusive(&e) }
        resp
    }

    /// Under the operation lock and a fresh lease: load, start a takeover's recovery
    /// (persisting it), and run this shard's pending move steps.
    async fn begin_locked(self: &Arc<Self>, term: u64) -> Result<(), String> {
        self.load_state().await?;
        if self.on_leadership(term) {
            self.recover_pending(term).await;
            self.save_state(term).await?;
        }
        self.drive_moves(term, false).await;
        Ok(())
    }

    /// The bucket a request is about, if any.
    async fn request_bucket(&self, req: &ControlRequest) -> Result<Option<u16>, String> {
        let d = &self.durable;
        let names = |targets: &[String]| targets.iter().map(|t| Name::parse(t)).collect::<Vec<_>>();
        Ok(match req {
            ControlRequest::SubmitWork { request, target, .. } => match d.work_bucket(request).await? {
                Some(b) => Some(b),
                None => Some(d.bucket_for_names(&[Name::parse(target)]).await?),
            },
            ControlRequest::Assign { target, .. } => Some(d.bucket_for_names(&[Name::parse(target)]).await?),
            ControlRequest::AssignGroup { targets, .. } if !targets.is_empty() => Some(d.bucket_for_names(&names(targets)).await?),
            ControlRequest::Validate { worker, request, targets, .. } => {
                let Some(w) = ws(worker) else { return Ok(None) };
                if let Some(b) = d.validation_route_bucket(&w, request.as_bytes()).await? { Some(b) }
                else if targets.is_empty() { Some(topology::validation_bucket(&w, request.as_bytes())) }
                else { Some(d.bucket_for_names(&targets.iter().map(|t| Name::parse(&t.name)).collect::<Vec<_>>()).await?) }
            }
            ControlRequest::Finish { request, .. } => d.work_bucket(request).await?,
            ControlRequest::Cancel { request, worker } => {
                if let Some(b) = d.work_bucket(request).await? { return Ok(Some(b)) }
                if !worker.is_empty() {
                    return match ws(worker) { Some(w) => d.validation_route_bucket(&w, request.as_bytes()).await, None => Ok(None) };
                }
                for w in self.cancel_scope(None) {
                    if let Some(b) = d.validation_route_bucket(&w, request.as_bytes()).await? { return Ok(Some(b)) }
                }
                None
            }
            _ => None,
        })
    }

    async fn route_dynamic(&self, req: &ControlRequest) -> Result<Route, String> {
        let Some(bucket) = self.request_bucket(req).await? else { return Ok(Route::Local) };
        let record = topology::read_bucket(&self.cfg.store, bucket).await?;
        if record.shard != self.durable.shard { return Ok(Route::Other) }
        if let Some(id) = record.moving {
            // Between export and import the destination owns the bucket but has not
            // merged its entries: it must not answer for them yet.
            if cfg!(feature = "mutate-shard-dest-serves-moving")
                && topology::read_move(&self.cfg.store, id).await?.is_some_and(|m| m.state == MoveState::Exported) {
                return Ok(Route::Mine(bucket));
            }
            return Ok(Route::Moving);
        }
        Ok(Route::Mine(bucket))
    }

    /// Run this shard's pending move steps: export moves it is the source of, import
    /// moves it is the destination of. Called under the operation lock.
    async fn drive_moves(self: &Arc<Self>, term: u64, explicit: bool) {
        if !self.durable.dynamic { return }
        let Ok(moves) = topology::active_moves(&self.cfg.store).await else { return };
        let shard = self.durable.shard;
        *self.moving.lock().unwrap() = moves.iter().filter(|m| m.from == shard || m.to == shard)
            .flat_map(|m| m.buckets.iter().copied()).collect();
        if !explicit && self.move_steps_paused.load(Ordering::SeqCst) { return }
        for m in moves {
            let result = match m.state {
                MoveState::Prepared if m.from == shard => self.export_locked(&m, term).await,
                MoveState::Exported if m.to == shard => self.import_locked(&m, term).await,
                _ => Ok(false),
            };
            if let Err(e) = result { eprintln!("controller shard {shard}: move {}: {e}", m.id) }
        }
    }

    /// The export step of `m` (source leader, under the operation lock and `term`).
    async fn export_locked(self: &Arc<Self>, m: &MoveRecord, term: u64) -> Result<bool, String> {
        if m.state != MoveState::Prepared || m.from != self.durable.shard { return Ok(false) }
        // Drain: validations of these buckets that started before Begin finish (and
        // record their J2) first. New ones are refused (`bucket moving`, J1's fence).
        if !cfg!(feature = "mutate-shard-no-drain") {
            let active = self.active.lock().unwrap();
            if m.buckets.iter().any(|b| active.get(b).is_some_and(|n| *n > 0)) { return Ok(false) }
        }
        self.fill_missing_buckets().await?;
        let buckets: HashSet<u16> = m.buckets.iter().copied().collect();
        let (source, handoff, polls) = {
            let st = self.state.lock().unwrap();
            let mut snap = st.snapshot();
            let (handoff, polls) = split_for_move(&mut snap, &buckets)?;
            let source = if cfg!(feature = "mutate-shard-export-keeps-source") { st.snapshot() } else { snap };
            let handoff = if cfg!(feature = "mutate-shard-flip-without-handoff") { Handoff::default() } else { handoff };
            let polls = if cfg!(feature = "mutate-shard-no-poll-rows") { Vec::new() } else { polls };
            (serde_json::to_vec(&source).map_err(|e| e.to_string())?, serde_json::to_vec(&handoff).map_err(|e| e.to_string())?, polls)
        };
        let expected = *self.loaded_generation.lock().unwrap();
        if let Ok(ms) = std::env::var("PARALEAN_TEST_PAUSE_BEFORE_EXPORT_MS").unwrap_or_default().parse::<u64>() {
            tokio::time::sleep(Duration::from_millis(ms)).await;
        }
        let outcome = self.durable.export_commit(m.id, term, expected, &source, &handoff, &polls).await;
        let reload = self.load_state().await;
        match outcome? {
            MoveOutcome::Committed => { reload?; Ok(true) }
            MoveOutcome::AlreadyDone => Ok(false),
            MoveOutcome::TooLarge(reason) => {
                eprintln!("controller shard {}: move {} aborted: {reason}", self.durable.shard, m.id);
                self.durable.abort_export(m.id, term, &reason).await.map(|_| false)
            }
        }
    }

    /// Work loaded without a bucket (none in a dynamic deployment's normal operation)
    /// takes its route's; a group, its names'.
    async fn fill_missing_buckets(&self) -> Result<(), String> {
        let (work, groups): (Vec<String>, Vec<Vec<String>>) = {
            let st = self.state.lock().unwrap();
            (st.work.keys().filter(|r| !st.work_buckets.contains_key(*r)).cloned().collect(),
             st.groups.iter().filter(|g| g.bucket.is_none()).map(|g| g.names.clone()).collect())
        };
        for r in work {
            let b = self.durable.work_bucket(&r).await?.ok_or_else(|| format!("work {r} has no route"))?;
            self.state.lock().unwrap().work_buckets.insert(r, b);
        }
        for names in groups {
            let b = self.durable.bucket_for_names(&names.iter().map(|n| Name::parse(n)).collect::<Vec<_>>()).await?;
            if let Some(g) = self.state.lock().unwrap().groups.iter_mut().find(|g| g.names == names) { g.bucket = Some(b) }
        }
        Ok(())
    }

    /// The import step of `m` (destination leader, under the operation lock and `term`).
    async fn import_locked(self: &Arc<Self>, m: &MoveRecord, term: u64) -> Result<bool, String> {
        let unchecked = cfg!(feature = "mutate-shard-import-no-state-check");
        if (m.state != MoveState::Exported && !unchecked) || m.to != self.durable.shard { return Ok(false) }
        let Some((hash, bytes)) = self.durable.read_handoff(m.id).await? else {
            return if unchecked { Ok(false) } else { Err("exported move has no handoff".into()) };
        };
        let handoff: Handoff = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        let now = self.durable.clock().await?;
        let merged = {
            let st = self.state.lock().unwrap();
            let mut snap = st.snapshot();
            merge_handoff(&mut snap, handoff, now)?;
            serde_json::to_vec(&snap).map_err(|e| e.to_string())?
        };
        let expected = *self.loaded_generation.lock().unwrap();
        if let Ok(ms) = std::env::var("PARALEAN_TEST_PAUSE_BEFORE_IMPORT_MS").unwrap_or_default().parse::<u64>() {
            tokio::time::sleep(Duration::from_millis(ms)).await;
        }
        let outcome = self.durable.import_commit(m.id, term, expected, &merged, &hash).await;
        let reload = self.load_state().await;
        match outcome? {
            MoveOutcome::Committed => {
                reload?;
                let mut moving = self.moving.lock().unwrap();
                for b in &m.buckets { moving.remove(b); }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    /// Run this shard's pending move steps now, as the monitor and every request do.
    /// Returns the lease term (tests; operators use `topology move --wait-secs`).
    pub async fn drive_moves_now(self: &Arc<Self>) -> Result<u64, String> {
        let _guard = self.operation.lock().await;
        let lease = self.durable.acquire_or_renew().await?.ok_or("not controller leader")?;
        self.begin_locked(lease.term).await?;
        self.drive_moves(lease.term, true).await;
        Ok(lease.term)
    }

    /// Run the import step of move `id` now, whatever the active-move list says
    /// (idempotence: a finished move imports nothing).
    pub async fn import_move_now(self: &Arc<Self>, id: u64) -> Result<bool, String> {
        let _guard = self.operation.lock().await;
        let lease = self.durable.acquire_or_renew().await?.ok_or("not controller leader")?;
        self.begin_locked(lease.term).await?;
        let m = topology::read_move(&self.cfg.store, id).await?.ok_or("no such move")?;
        self.import_locked(&m, lease.term).await
    }

    async fn request_shard(&self, req: &ControlRequest) -> Result<Option<u32>, String> {
        let target = match req {
            ControlRequest::SubmitWork { target, .. } | ControlRequest::Assign { target, .. } => Some(Name::parse(target)),
            ControlRequest::AssignGroup { targets, .. } => {
                let mut sorted = targets.clone();
                sorted.sort();
                let mut mapped = None;
                for name in &sorted {
                    if let Some(shard) = self.durable.mapped_shard(&Name::parse(name)).await? {
                        if mapped.is_some_and(|n| n != shard) { return Err("group spans existing controller shards".into()) }
                        mapped = Some(shard);
                    }
                }
                if let Some(shard) = mapped { return Ok(Some(shard)) }
                sorted.first().map(|s| Name::parse(s))
            }
            ControlRequest::Validate { .. } | ControlRequest::ValidateBatch { .. } => {
                let mut sorted = validation_targets(req);
                sorted.sort();
                let mut mapped = None;
                for name in &sorted {
                    if let Some(shard) = self.durable.mapped_shard(&Name::parse(name)).await? {
                        if mapped.is_some_and(|n| n != shard) { return Err("validation spans controller shards".into()) }
                        mapped = Some(shard);
                    }
                }
                if let Some(shard) = mapped { return Ok(Some(shard)) }
                sorted.first().map(|s| Name::parse(s))
            }
            _ => None,
        };
        if let Some(target) = target { return self.durable.shard_for_target(&target).await.map(Some) }
        match req {
            ControlRequest::Finish { request, .. } => self.durable.shard_for_work(request).await,
            // Validation routes are per (workspace, request) (W2-32); a bad ID is refused later.
            ControlRequest::Validate { worker, request, .. } => match ws(worker) {
                Some(w) => self.durable.shard_for_validation(&w, request).await,
                None => Ok(None),
            },
            // A target-free batch: its first publication member's route.
            ControlRequest::ValidateBatch { coordinator, members, .. } => {
                let first = members.iter().find_map(|m| match m {
                    BatchMemberReq::Publish { worker, request, .. } => Some((worker, request)),
                    BatchMemberReq::Tombstone { .. } => None,
                });
                match (ws(coordinator), first.and_then(|(w, r)| Some((ws(w)?, r)))) {
                    (Some(c), Some((w, r))) => self.durable.shard_for_validation_bytes(&w, &batch_request(&c, r)).await,
                    _ => Ok(None),
                }
            }
            ControlRequest::Cancel { request, worker } => {
                if let Some(shard) = self.durable.shard_for_work(request).await? { return Ok(Some(shard)) }
                if !worker.is_empty() {
                    return match ws(worker) { Some(w) => self.durable.shard_for_validation(&w, request).await, None => Ok(None) };
                }
                // Every workspace's request with this ID: the first routed one's shard.
                for w in self.cancel_scope(None) {
                    if let Some(shard) = self.durable.shard_for_validation(&w, request).await? { return Ok(Some(shard)) }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    async fn load_state(&self) -> Result<(), String> {
        let loaded = self.durable.load_generation().await?;
        let generation = loaded.as_ref().map(|(_, g)| *g);
        let snap = loaded.map(|(b, _)| serde_json::from_slice(&b).map_err(|e| e.to_string())).transpose()?.unwrap_or_default();
        self.state.lock().unwrap().restore(snap);
        *self.loaded_generation.lock().unwrap() = generation;
        Ok(())
    }

    /// Save a snapshot; in a dynamic topology only over the generation last loaded.
    async fn save_bytes(&self, bytes: &[u8], term: u64, work: &[WorkReplay], polls: &[PollReplay]) -> Result<(), String> {
        if !self.durable.dynamic { return self.durable.save_with_history(bytes, term, work, polls).await }
        let expected = *self.loaded_generation.lock().unwrap();
        let generation = self.durable.save_generation(bytes, term, work, polls, Some(expected)).await?;
        *self.loaded_generation.lock().unwrap() = Some(generation);
        Ok(())
    }

    async fn save_state(&self, term: u64) -> Result<(), String> {
        // Entries over the W2-33 bounds leave the snapshot as replay rows in the same
        // transaction. On failure nothing moved durably; the next operation reloads.
        let (bytes, work, polls) = {
            let mut st = self.state.lock().unwrap();
            let (work, polls) = st.spill_over_caps(SPILL_BUDGET);
            (serde_json::to_vec(&st.snapshot()).map_err(|e| e.to_string())?, work, polls)
        };
        self.save_bytes(&bytes, term, &work, &polls).await
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
    /// leader. The pass reads this shard's validation index and ends after its last page;
    /// each envelope is recovered at most `validator_attempts` times over all takeovers (a
    /// durable count), so an envelope no validator can decide is not re-dispatched forever.
    async fn recover_pending(self: &Arc<Self>, term: u64) {
        let every_tick = cfg!(feature = "mutate-recover-every-tick");
        let (cursor, recovering) = {
            let state = self.state.lock().unwrap();
            (state.recovery_cursor.clone(), state.recovering)
        };
        if !recovering && !every_tick { return }
        let sub = self.durable.validation_jobs_subspace();
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
            // A batch member's dependencies may be earlier members: only its batch's
            // `ValidateBatch`, which the coordinator retries, can check it.
            if job.body.batch.is_some() { continue }
            let worker = job.body.worker;
            let req = job_key(&worker, &job.body.request);
            // The index is shard local, while J1 remains global for T1 deduplication.
            // Verify the authoritative route before starting any recovered dispatch.
            let mut bucket = None;
            if self.durable.dynamic {
                // Dynamic: the route's bucket must be this shard's, with no move in progress.
                let Ok(Some(b)) = self.durable.validation_route_bucket(&worker, &job.body.request).await else { continue };
                if !matches!(topology::read_bucket(&self.cfg.store, b).await, Ok(r) if r.shard == self.durable.shard && r.moving.is_none()) { continue }
                bucket = Some(b);
            } else if !matches!(self.durable.shard_for_validation_bytes(&worker, &job.body.request).await, Ok(Some(s)) if s == self.durable.shard) {
                continue;
            }
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
                match self.durable.count_recovery(&worker, &job.body.request, limit, term).await {
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
            let active = bucket.map(|b| ActiveGuard::enter(&self.active, b));
            let me = self.clone();
            tokio::spawn(async move {
                let _active = active;
                let result = me.dispatch(&job, crx, term).await;
                let _ = tx.send(Some(result));
                me.state.lock().unwrap().inflight.remove(&req);
            });
        }
    }

    async fn handle_inner(self: &Arc<Self>, req: ControlRequest, term: u64, bucket: Option<u16>, active: Option<Arc<ActiveGuard>>) -> ControlResponse {
        match req {
            ControlRequest::Register { worker, capacity_mb } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let now = match self.durable.clock().await { Ok(v) => v, Err(e) => return inconclusive(&e) };
                let mut st = self.state.lock().unwrap();
                let used_mb = st.work.values().filter_map(|j| match j.state {
                    WorkState::Running { worker, .. } if worker == w => Some(j.memory_mb),
                    _ => None,
                }).sum();
                st.workers.insert(
                    w,
                    WorkerInfo { capacity_mb, used_mb, lease_until: now.saturating_add(8), alive: true },
                );
                // A worker lease is eight store increments, and every replica of
                // this shard advances the store clock once per monitor interval.
                // Workers heartbeat at a third of the advertised lease, so
                // advertise one monitor interval: heartbeats then outpace expiry
                // for fewer than 24 concurrently ticking replicas.
                ControlResponse::Registered { lease_ms: monitor_interval(self.cfg.lease).as_millis() as u64 }
            }
            ControlRequest::Heartbeat { worker } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let now = match self.durable.clock().await { Ok(v) => v, Err(e) => return inconclusive(&e) };
                let mut st = self.state.lock().unwrap();
                match st.workers.get_mut(&w) {
                    Some(i) if i.alive => {
                        i.lease_until = now.saturating_add(8);
                        ControlResponse::Ok
                    }
                    _ => ControlResponse::Unknown,
                }
            }
            ControlRequest::SubmitWork { request, target, memory_mb } => {
                if !self.state.lock().unwrap().work.contains_key(&request) && !cfg!(feature = "mutate-history-no-work-replay") {
                    match self.durable.work_replay(&request).await {
                        Ok(Some(replay)) => {
                            if !cfg!(feature = "mutate-history-no-work-identity") &&
                                (replay.target != Name::parse(&target).to_string() || replay.memory_mb != memory_mb) {
                                return refused("request ID already used for different work");
                            }
                            let cancelled = if cfg!(feature = "mutate-history-no-cancel-overlay") { false }
                                else { match self.work_cancelled(&request).await {
                                    Ok(v) => v, Err(e) => return inconclusive(&e.to_string()),
                                } };
                            let state = if cancelled { "Cancelled".into() } else { format!("{:?}", replay.state) };
                            return ControlResponse::Duplicate { state };
                        }
                        Ok(None) => {}
                        Err(e) => return inconclusive(&e),
                    }
                }
                self.submit_work(request, target, memory_mb, bucket)
            }
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
                let now = match self.durable.clock().await { Ok(v) => v, Err(e) => return inconclusive(&e) };
                if !self.state.lock().unwrap().work.contains_key(&request) {
                    match self.durable.work_replay(&request).await {
                        Ok(Some(_)) => return refused("the job is not running on this worker"),
                        Ok(None) => {}
                        Err(e) => return inconclusive(&e),
                    }
                }
                self.finish(w, &request, ok, now)
            }
            ControlRequest::Validate { worker, request, group, capsule, deps, targets, memory_mb, deadline_ms } => {
                self.validate(worker, request, group, capsule, deps, targets, memory_mb, deadline_ms, term, active).await
            }
            ControlRequest::ValidateBatch { coordinator, request, members } => {
                self.validate_batch(coordinator, request, members, term).await
            }
            ControlRequest::Cancel { request, worker } => {
                let worker = if worker.is_empty() { None } else {
                    match ws(&worker) { Some(w) => Some(w), None => return refused("bad worker ID") }
                };
                self.cancel(&request, worker).await
            }
            ControlRequest::Assign { target, worker, statement } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                let target = Name::parse(&target);
                if target.to_string().is_empty() { return refused("empty target name") }
                let statements = if statement.is_empty() { vec![] } else { vec![statement] };
                if let Err(r) = self.pin_statements(std::slice::from_ref(&target), &statements).await { return r }
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
            ControlRequest::AssignGroup { targets, worker, request, statements } => {
                let Some(w) = ws(&worker) else { return refused("bad worker ID") };
                if targets.is_empty() { return refused("empty target group") }
                let names: Vec<Name> = targets.iter().map(|s| Name::parse(s)).collect();
                if names.iter().any(|n| n.to_string().is_empty()) { return refused("empty target name") }
                let mut target_set: Vec<String> = names.iter().map(ToString::to_string).collect();
                target_set.sort();
                target_set.dedup();
                if target_set.len() != targets.len() { return refused("duplicate target name") }
                if let Err(r) = self.pin_statements(&names, &statements).await { return r }
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
                        g.bucket = g.bucket.or(bucket);
                    } else {
                        st.groups.push(StoredGroup { names: target_set, owner: worker.clone(), request: req.clone(), pending: true, bucket });
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

    /// Pin each target's statement before it is assigned (W2 A-4), so the controller stamps
    /// that statement into every job for the name and T1 refuses any other.
    async fn pin_statements(&self, names: &[Name], statements: &[String]) -> Result<(), ControlResponse> {
        if statements.is_empty() { return Ok(()) }
        if statements.len() != names.len() { return Err(refused("give one statement per target")) }
        let ctl = paralean_store::Controller::new(self.cfg.store.clone(), self.cfg.authority.clone());
        for (name, hash) in names.iter().zip(statements) {
            let Ok(bytes) = hex::decode(hash) else { return Err(refused("statement is not hex")) };
            if let Err(e) = ctl.pin_statement(name, &bytes).await {
                return Err(match e {
                    paralean_store::StoreError::Invalid(reason) => refused(&reason),
                    other => inconclusive(&other.to_string()),
                });
            }
        }
        Ok(())
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
            status: if self.durable.dynamic {
                serde_json::json!({"leader": true, "shard": self.durable.shard, "dynamic": true, "term": self.seen_term.load(Ordering::SeqCst), "workers": workers, "work": work, "validations_in_flight": st.inflight.len(),
                    "groups": st.groups.iter().map(|g| g.names.clone()).collect::<Vec<_>>(),
                    "history_compacted_work": st.history_compacted_work, "history_compacted_polls": st.history_compacted_polls})
            } else {
                serde_json::json!({"leader": true, "shard": self.durable.shard, "shards": self.durable.shards, "term": self.seen_term.load(Ordering::SeqCst), "workers": workers, "work": work, "validations_in_flight": st.inflight.len(),
                "history_compacted_work": st.history_compacted_work, "history_compacted_polls": st.history_compacted_polls})
            },
        }
    }

    // ------------------------------------------------------------ target work

    fn submit_work(&self, request: String, target: String, memory_mb: u64, bucket: Option<u16>) -> ControlResponse {
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
        let queued = st.work.values().filter(|j| j.state == WorkState::Queued
            || matches!(j.state, WorkState::Running { worker, .. } if worker == unowned())).count();
        if queued >= self.cfg.max_work_queue {
            return ControlResponse::Busy;
        }
        if !st.work.contains_key(&request) {
            st.order.push(request.clone());
        }
        if let Some(b) = bucket { st.work_buckets.insert(request.clone(), b); }
        st.work.insert(request, WorkJob { target: name, memory_mb, state: WorkState::Queued, attempts: 0, settled_tick: None });
        ControlResponse::Queued
    }

    async fn poll(&self, w: WorkspaceId, token: Option<&str>) -> ControlResponse {
        let now = match self.durable.clock().await { Ok(v) => v, Err(e) => return inconclusive(&e) };
        let dynamic = self.durable.dynamic;
        let archived = if dynamic { None } else if let Some(token) = token.filter(|_| !cfg!(feature = "mutate-history-no-poll-replay")) {
            match self.durable.poll_replay(token).await { Ok(v) => v, Err(e) => return inconclusive(&e) }
        } else { None };
        // Dynamic: a token's rows from every shard (a moved job's token is the source's row).
        let rows = match token.filter(|_| dynamic && !cfg!(feature = "mutate-history-no-poll-replay")) {
            Some(token) => match self.durable.poll_replays(token).await { Ok(v) => v, Err(e) => return inconclusive(&e) },
            None => Vec::new(),
        };
        let moving = if dynamic { self.moving.lock().unwrap().clone() } else { HashSet::new() };
        // A job already assigned to this worker (after a reassignment) comes first.
        let pick = {
            let mut st = self.state.lock().unwrap();
            match st.workers.get(&w) {
                Some(i) if i.alive && i.lease_until > now => {}
                _ => return ControlResponse::Unknown,
            }
            if let Some(p) = &archived {
                if !cfg!(feature = "mutate-history-no-poll-worker") && p.worker != w.hex() {
                    return refused("poll request ID belongs to another worker");
                }
                if let Some(work) = &p.work {
                    if let Some(j) = st.work.get(work) {
                        if let WorkState::Running { worker, epoch, .. } = j.state {
                            if worker == w && p.epoch == Some(epoch) {
                                return ControlResponse::Work { request: work.clone(), target: j.target.to_string(), epoch, memory_mb: j.memory_mb };
                            }
                        }
                    }
                }
                return ControlResponse::NoWork;
            }
            if let Some(token) = token {
                if let Some(p) = st.poll_responses.get(token) {
                    if p.worker != w.hex() { return refused("poll request ID belongs to another worker") }
                    if let Some(work) = &p.work {
                        if let Some(j) = st.work.get(work) {
                            if let WorkState::Running { worker, epoch, .. } = j.state {
                                if worker == w && epoch != u64::MAX &&
                                    (cfg!(feature = "mutate-history-no-poll-epoch") || p.epoch.is_none_or(|first| first == epoch)) {
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
            if !rows.is_empty() {
                if !cfg!(feature = "mutate-history-no-poll-worker") && rows.iter().any(|p| p.worker != w.hex()) {
                    return refused("poll request ID belongs to another worker");
                }
                for p in &rows {
                    let Some(work) = &p.work else { continue };
                    if let Some(j) = st.work.get(work) {
                        if let WorkState::Running { worker, epoch, .. } = j.state {
                            if worker == w && p.epoch == Some(epoch) {
                                return ControlResponse::Work { request: work.clone(), target: j.target.to_string(), epoch, memory_mb: j.memory_mb };
                            }
                        }
                    }
                }
                return ControlResponse::NoWork;
            }
            // Work of a bucket with a move in progress waits for the move (T4 is fenced).
            let blocked: HashSet<String> = st.work_buckets.iter().filter(|(_, b)| moving.contains(b)).map(|(r, _)| r.clone()).collect();
            let free = {
                let i = &st.workers[&w];
                i.capacity_mb.saturating_sub(i.used_mb)
            };
            let order = st.order.clone();
            let mut pick = None;
            for r in &order {
                let j = st.work.get_mut(r).unwrap();
                if let WorkState::Running { worker, epoch, delivered: false } = j.state {
                    if worker == w && !(epoch == u64::MAX && blocked.contains(r)) {
                        if epoch != u64::MAX {
                            j.state = WorkState::Running { worker, epoch, delivered: true };
                            let response = ControlResponse::Work { request: r.clone(), target: j.target.to_string(), epoch, memory_mb: j.memory_mb };
                            if let Some(token) = token { st.remember_poll(token, &w, Some(r.clone()), Some(epoch), now); }
                            return response;
                        }
                        pick = Some((r.clone(), j.target.clone(), j.memory_mb, j.attempts));
                        break;
                    }
                }
            }
            for r in &order {
                if pick.is_some() { break }
                if blocked.contains(r) { continue }
                let j = st.work.get_mut(r).unwrap();
                if (j.state == WorkState::Queued
                    || matches!(j.state, WorkState::Running { worker, epoch, .. }
                        if worker == unowned() && epoch != u64::MAX
                            && !cfg!(feature = "mutate-no-unowned-reassign")))
                    && j.memory_mb <= free {
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
                self.state.lock().unwrap().remember_poll(token, &w, None, None, now);
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
                        self.state.lock().unwrap().remember_poll(token, &w, Some(request.clone()), Some(epoch), now);
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

    fn finish(&self, w: WorkspaceId, request: &str, ok: bool, now: u64) -> ControlResponse {
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
                j.settled_tick = if matches!(j.state, WorkState::Done | WorkState::Failed) { Some(now) } else { None };
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
        if self.durable.dynamic {
            if self.begin_locked(lease.term).await.is_err() { return }
        } else {
            if self.load_state().await.is_err() { return }
            self.on_leadership(lease.term);
            self.recover_pending(lease.term).await;
        }
        if self.expire_leases_inner(lease.term).await {
            let _ = self.save_state(lease.term).await;
        }
        drop(_guard);
        if self.gc.enabled { let _ = self.compact_history_once().await; }
    }

    async fn expire_leases_inner(&self, term: u64) -> bool {
        if cfg!(feature = "mutate-no-lease-reassign") {
            return true;
        }
        let now = match self.durable.clock().await { Ok(v) => v, Err(_) => return false };
        let mut moves: Vec<(String, Name, WorkspaceId, u64)> = Vec::new();
        let mut group_moves: Vec<(Vec<Name>, WorkspaceId, String)> = Vec::new();
        {
            let mut st = self.state.lock().unwrap();
            let dead: Vec<WorkspaceId> =
                st.workers.iter().filter(|(_, i)| i.alive && i.lease_until <= now).map(|(w, _)| *w).collect();
            for d in &dead {
                st.workers.get_mut(d).unwrap().alive = false;
            }
            // A dead worker's poll tokens stay: they leave the snapshot only through
            // `spill_over_caps`, as replay rows (W4 history), never silently.
            let order = st.order.clone();
            for r in order {
                let (target, mem, attempts, already_unowned) = {
                    let j = &st.work[&r];
                    match j.state {
                        WorkState::Running { worker, .. } if dead.contains(&worker) || worker == unowned() =>
                            (j.target.clone(), j.memory_mb, j.attempts, worker == unowned()),
                        _ => continue,
                    }
                };
                // Another live worker with room, else the sentinel.
                let next = st
                    .workers
                    .iter()
                    .find(|(w, i)| i.alive && i.lease_until > now && i.capacity_mb.saturating_sub(i.used_mb) >= mem && !dead.contains(w))
                    .map(|(w, _)| *w);
                if next.is_none() && already_unowned { continue }
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
            let res = self.durable.assign_group(&[target.clone()], to, req.as_bytes(), term).await.map(|v| v[0]);
            // A superseded request is final for this attempt: another
            // assignment owns the target now. Skip it rather than aborting the
            // remaining handovers of this tick; the intent stays durable and
            // is reconsidered with a fresh attempt once its owner expires.
            if res.as_ref().is_err_and(|e| e.contains("superseded")) { continue }
            // Dynamic: a bucket with a move in progress keeps its durable intent, which
            // moves with the job; its next owner resumes it.
            if self.durable.dynamic && res.as_ref().is_err_and(|e| e.contains("bucket")) { continue }
            if res.is_err() { return false }
            {
                let mut st = self.state.lock().unwrap();
                if let Some(j) = st.work.get_mut(&r) {
                    if let (Ok(epoch), WorkState::Running { worker, delivered, .. }) = (&res, j.state.clone()) {
                        if worker == to {
                            j.state = if to == unowned() {
                                // Keep the unowned fence visible in durable state.
                                // A worker registering later can be assigned on the
                                // next monitor tick without waiting for a poll.
                                WorkState::Running { worker: unowned(), epoch: *epoch, delivered: false }
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
            let res = self.durable.assign_group(&names, owner, req.as_bytes(), term).await;
            if self.durable.dynamic && res.as_ref().is_err_and(|e| e.contains("bucket")) { continue }
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
        term: u64,
        active: Option<Arc<ActiveGuard>>,
    ) -> ControlResponse {
        let st = &self.cfg.store;
        let Some(w) = ws(&worker) else { return refused("bad worker ID") };
        if let Err(r) = self.require_live(&w).await { return r }
        let env = match self.envelope(w, request.into_bytes(), &group, &capsule, &deps, &targets, memory_mb, deadline_ms, None).await {
            Ok(env) => env,
            Err(r) => return r,
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
                match self.durable.issue_job(&job, term).await {
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
                    let active = active.clone();
                    tokio::spawn(async move {
                        let _active = active;
                        let r = me.dispatch(&job, crx, term).await;
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

    /// A registered workspace whose lease has not expired.
    async fn require_live(&self, w: &WorkspaceId) -> Result<(), ControlResponse> {
        let now = self.durable.clock().await.map_err(|e| inconclusive(&e))?;
        match self.state.lock().unwrap().workers.get(w) {
            Some(i) if i.alive && i.lease_until > now => Ok(()),
            _ => Err(refused("worker is not registered or its lease expired")),
        }
    }

    /// The envelope of `w`'s validation: each target bound to the epoch of its record, if
    /// `w` owns it, and to its pinned statement; the controller's base, policy, checker and
    /// limits.
    #[allow(clippy::too_many_arguments)]
    async fn envelope(
        &self, w: WorkspaceId, request: Vec<u8>, group: &str, capsule: &str, deps: &[String], targets: &[TargetReq],
        memory_mb: u64, deadline_ms: u64, batch: Option<Id>,
    ) -> Result<JobEnvelope, ControlResponse> {
        let st = &self.cfg.store;
        let (Some(group), Some(capsule)) = (Id::from_hex(group), Id::from_hex(capsule)) else {
            return Err(refused("bad group or capsule ID"));
        };
        let Some(deps) = deps.iter().map(|d| Id::from_hex(d)).collect::<Option<Vec<_>>>() else {
            return Err(refused("bad dependency ID"));
        };
        let mut bindings = Vec::new();
        for t in targets {
            let name = Name::parse(&t.name);
            let rec = match st.target(&name).await {
                Ok(Some(r)) => r,
                Ok(None) => return Err(refused(&format!("no target record for {name}"))),
                Err(e) => return Err(inconclusive(&e.to_string())),
            };
            if rec.owner != w && !cfg!(feature = "mutate-no-dispatch-owner-check") {
                return Err(refused(&format!("worker does not own {name}")));
            }
            let Ok(statement) = hex::decode(&t.statement) else { return Err(refused("bad statement hash")) };
            // W2 A-4: a statement the authority pinned for the name replaces the worker's.
            let statement = match st.meta.target_statement(&name).await {
                Ok(pinned) if !cfg!(feature = "mutate-no-statement-stamp") => pinned.unwrap_or(statement),
                Ok(_) => statement,
                Err(e) => return Err(inconclusive(&e.to_string())),
            };
            bindings.push(TargetBinding { name, epoch: rec.epoch, statement });
        }
        sort_targets(&mut bindings);
        let cap_ms = self.cfg.validation_deadline.as_millis() as u64;
        Ok(JobEnvelope {
            request,
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
            batch,
        })
    }

    /// Validate the publication members of one atomic batch: sign the intent, issue each
    /// member's envelope bound to it (J1), and dispatch them in order as one batch.
    async fn validate_batch(self: &Arc<Self>, coordinator: String, request: String, members: Vec<BatchMemberReq>, term: u64) -> ControlResponse {
        let st = &self.cfg.store;
        let Some(c) = ws(&coordinator) else { return refused("bad coordinator ID") };
        if let Err(r) = self.require_live(&c).await { return r }
        let publications = members.iter().filter(|m| matches!(m, BatchMemberReq::Publish { .. })).count();
        if members.is_empty() || members.len() > MAX_BATCH_MEMBERS || publications > MAX_BATCH_JOBS {
            return refused(&format!("a batch has 1 to {MAX_BATCH_MEMBERS} members, at most {MAX_BATCH_JOBS} of them publications"));
        }
        let mut named = Vec::with_capacity(members.len());
        for m in &members {
            named.push(match m {
                BatchMemberReq::Publish { worker, request, group, .. } => {
                    if request.len() > MAX_REQUEST_ID && !cfg!(feature = "mutate-unbounded-poll-responses") {
                        return refused(&format!("request ID longer than {MAX_REQUEST_ID} bytes"));
                    }
                    let (Some(writer), Some(group)) = (ws(worker), Id::from_hex(group)) else { return refused("bad member worker or group ID") };
                    BatchMember::Publish { group, writer }
                }
                BatchMemberReq::Tombstone { worker, target, position } => {
                    let position = if position.is_empty() { None } else {
                        match Id::from_hex(position) { Some(p) => Some(p), None => return refused("bad tombstone position") }
                    };
                    let (Some(writer), Some(target)) = (ws(worker), Id::from_hex(target)) else { return refused("bad member worker or target ID") };
                    BatchMember::Tombstone { target, position, writer }
                }
            });
        }
        let intent = SignedBatch::sign(BatchIntent { request: batch_request(&c, &request), members: named }, &self.cfg.authority);
        let mut jobs = Vec::with_capacity(publications);
        for m in &members {
            let BatchMemberReq::Publish { worker, request, group, capsule, deps, targets } = m else { continue };
            let w = ws(worker).expect("checked above");
            let env = match self.envelope(w, batch_request(&c, request), group, capsule, deps, targets, 0, 0, Some(intent.id())).await {
                Ok(env) => env,
                Err(r) => return r,
            };
            let job = SignedJob::sign(env, &self.cfg.authority);
            match st.meta.is_cancelled(&w, &job.body.request).await {
                Ok(true) => return ControlResponse::Cancelled,
                Ok(false) => {}
                Err(e) => return inconclusive(&e.to_string()),
            }
            match self.durable.issue_job(&job, term).await {
                Ok(stored) if stored.body == job.body => jobs.push(stored),
                Ok(_) => return refused("request ID already used for another envelope"),
                Err(e) => return inconclusive(&e),
            }
        }
        // A finished batch: the recorded receipts (J2).
        let mut recorded = Vec::new();
        for j in &jobs {
            if let Ok(Some(v)) = st.meta.get(st.meta.keys.job_receipt(&j.body.worker, &j.body.request)).await {
                if let Ok(r) = Receipt::from_bytes(&v) { recorded.push(r) }
            }
        }
        if recorded.len() == jobs.len() {
            return batch_receipts(&intent, &recorded, &jobs);
        }
        // One dispatch per batch: its members' in-flight entries share its answer.
        let keys: Vec<Vec<u8>> = jobs.iter().map(|j| job_key(&j.body.worker, &j.body.request)).collect();
        let mut rx = {
            let mut s = self.state.lock().unwrap();
            let mut shared = None;
            for (k, j) in keys.iter().zip(&jobs) {
                if let Some(f) = s.inflight.get(k) {
                    if f.job != j.id() { return refused("request ID already used for another envelope") }
                    shared = Some(f.result.clone());
                }
            }
            match shared {
                Some(rx) => rx,
                None if s.inflight.len() + keys.len() > self.cfg.max_validations => return ControlResponse::Busy,
                None => {
                    let (tx, rx) = watch::channel(None);
                    let mut cancels = Vec::with_capacity(keys.len());
                    for (k, j) in keys.iter().zip(&jobs) {
                        let (ctx, crx) = watch::channel(false);
                        s.inflight.insert(k.clone(), Inflight { job: j.id(), result: rx.clone(), cancel: ctx });
                        cancels.push(crx);
                    }
                    let me = self.clone();
                    tokio::spawn(async move {
                        let r = match me.dispatch_batch(&jobs, &cancels, term).await {
                            Ok(receipts) => batch_receipts(&intent, &receipts, &jobs),
                            Err(r) => r,
                        };
                        let _ = tx.send(Some(r));
                        let mut s = me.state.lock().unwrap();
                        for k in &keys { s.inflight.remove(k); }
                    });
                    rx
                }
            }
        };
        loop {
            if let Some(r) = rx.borrow().clone() {
                return r;
            }
            if rx.changed().await.is_err() {
                return inconclusive("dispatch abandoned");
            }
        }
    }

    /// Send a batch's envelopes, in order, as one `ValidateBatch` until a validator gives a
    /// bound receipt for every one, retrying as `dispatch` does. Records each receipt (J2).
    async fn dispatch_batch(&self, jobs: &[SignedJob], cancel: &[watch::Receiver<bool>], term: u64) -> Result<Vec<Receipt>, ControlResponse> {
        let st = &self.cfg.store;
        let n = self.cfg.validators.len();
        if n == 0 {
            return Err(inconclusive("no validators configured"));
        }
        let start = {
            let mut s = self.state.lock().unwrap();
            s.next_validator += 1;
            s.next_validator
        };
        let timeout = jobs.iter().map(|j| Duration::from_millis(j.body.deadline_ms)).sum::<Duration>() + Duration::from_secs(5);
        let req = ValidatorRequest::ValidateBatch { jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect() };
        let mut last = String::from("no attempt");
        let mut refusals = 0;
        'attempts: for attempt in 0..self.cfg.validator_attempts.max(n) {
            if cancel.iter().any(|c| *c.borrow()) {
                return Err(ControlResponse::Cancelled);
            }
            let addr = &self.cfg.validators[(start + attempt) % n];
            match rpc::call_authenticated_any(addr, &req, &self.cfg.authority, &st.ring.validators, timeout).await {
                Ok(ValidatorResponse::Batch { responses }) if responses.len() == jobs.len() => {
                    let mut receipts = Vec::with_capacity(jobs.len());
                    for (i, (resp, job)) in responses.into_iter().zip(jobs).enumerate() {
                        match resp {
                            ValidatorResponse::Receipt { receipt } => match decode_receipt(&receipt) {
                                Ok(r) if check_bound(&r, job, &job.body.group, &prepared_of(job), &st.ring).is_ok() => receipts.push(r),
                                _ => {
                                    last = format!("{addr}: member {i}: receipt does not verify or is not bound to the envelope");
                                    continue 'attempts;
                                }
                            },
                            ValidatorResponse::Refused { reason } => {
                                last = format!("validator {addr}: member {i}: {reason}");
                                refusals += 1;
                                if refusals >= n {
                                    return Err(refused(&last));
                                }
                                continue 'attempts;
                            }
                            ValidatorResponse::Cancelled => return Err(ControlResponse::Cancelled),
                            other => {
                                last = format!("{addr}: member {i}: {other:?}");
                                break;
                            }
                        }
                    }
                    if receipts.len() == jobs.len() {
                        let mut stored = Vec::with_capacity(receipts.len());
                        for (r, job) in receipts.iter().zip(jobs) {
                            stored.push(self.durable.record_receipt(&job.body.worker, &job.body.request, r, term).await.map_err(|e| inconclusive(&e))?);
                        }
                        return Ok(stored);
                    }
                }
                Ok(ValidatorResponse::Refused { reason }) => {
                    last = format!("validator {addr}: {reason}");
                    refusals += 1;
                    if refusals >= n {
                        return Err(refused(&last));
                    }
                    continue;
                }
                Ok(ValidatorResponse::Cancelled) => return Err(ControlResponse::Cancelled),
                Ok(other) => last = format!("{addr}: unexpected {other:?}"),
                Err(e) => last = format!("{addr}: {e}"),
            }
            tokio::time::sleep(Duration::from_millis(20 * (attempt as u64 + 1))).await;
        }
        if refusals > 0 {
            return Err(refused(&last));
        }
        Err(inconclusive(&format!("no validator gave a verdict ({last})")))
    }

    /// Send the envelope to validators until one gives a valid receipt or refuses.
    async fn dispatch(&self, job: &SignedJob, mut cancel: watch::Receiver<bool>, term: u64) -> ControlResponse {
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

    /// The workspaces a `Cancel` naming `worker` (or none: every configured one) covers.
    fn cancel_scope(&self, worker: Option<WorkspaceId>) -> Vec<WorkspaceId> {
        match worker {
            Some(w) => vec![w],
            None => {
                let mut all: Vec<WorkspaceId> = self.cfg.store.ring.writers.keys().copied().collect();
                all.extend(self.state.lock().unwrap().workers.keys().copied());
                all.sort();
                all.dedup();
                all
            }
        }
    }

    /// Whether a work request was cancelled: `cancel` writes J3 under each workspace its
    /// scope covers, so a J3 of any configured workspace counts.
    async fn work_cancelled(&self, request: &str) -> paralean_store::Result<bool> {
        for w in self.cancel_scope(None) {
            if self.cfg.store.meta.is_cancelled(&w, request.as_bytes()).await? { return Ok(true) }
        }
        Ok(false)
    }

    /// Cancel `worker`'s `request`, or that request ID of every configured workspace.
    async fn cancel(&self, request: &str, worker: Option<WorkspaceId>) -> ControlResponse {
        let req = request.as_bytes().to_vec();
        let workers = self.cancel_scope(worker);
        // J3 first: from here on no T1 accepts a receipt bound to this request.
        let term = match self.durable.current().await { Ok(Some(l)) => l.term, _ => return inconclusive("controller lost lease") };
        for w in &workers {
            if let Err(e) = self.durable.cancel_job(w, &req, term).await { return inconclusive(&e) }
        }
        let now = match self.durable.clock().await { Ok(v) => v, Err(e) => return inconclusive(&e) };
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
                    j.settled_tick = Some(now);
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

fn batch_receipts(intent: &SignedBatch, receipts: &[Receipt], jobs: &[SignedJob]) -> ControlResponse {
    ControlResponse::BatchReceipts {
        intent: hex::encode(intent.to_bytes()),
        receipts: receipts.iter().map(|r| hex::encode(r.to_bytes())).collect(),
        jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect(),
    }
}

/// Take every entry of `buckets` out of a source snapshot: work in any state (in
/// submission order), groups, and the poll tokens naming moved work, which leave as
/// replay rows of the source (cross-shard poll lookups find them at the destination).
/// Workers of moved running work and groups travel with their capacity.
fn split_for_move(snap: &mut Snapshot, buckets: &HashSet<u16>) -> Result<(Handoff, Vec<PollReplay>), String> {
    if let Some(r) = snap.work.iter().find(|(_, w)| w.bucket.is_none()).map(|(r, _)| r) { return Err(format!("work {r} has no bucket")) }
    if snap.groups.iter().any(|g| g.bucket.is_none()) { return Err("group without bucket".into()) }
    let moved: BTreeSet<String> = snap.work.iter().filter(|(_, w)| w.bucket.is_some_and(|b| buckets.contains(&b))).map(|(r, _)| r.clone()).collect();
    let mut handoff = Handoff::default();
    for r in snap.order.iter().filter(|r| moved.contains(*r)) {
        if let Some(w) = snap.work.remove(r) { handoff.work.push((r.clone(), w)) }
    }
    for r in &moved {
        if let Some(w) = snap.work.remove(r) { handoff.work.push((r.clone(), w)) }
    }
    snap.order.retain(|r| !moved.contains(r));
    let (gone, kept): (Vec<_>, Vec<_>) = std::mem::take(&mut snap.groups).into_iter().partition(|g| g.bucket.is_some_and(|b| buckets.contains(&b)));
    snap.groups = kept;
    handoff.groups = gone;
    let tokens: Vec<String> = snap.poll_responses.iter().filter(|(_, p)| p.work.as_ref().is_some_and(|w| moved.contains(w))).map(|(t, _)| t.clone()).collect();
    let polls = tokens.into_iter().map(|token| {
        let p = snap.poll_responses.remove(&token).unwrap();
        PollReplay { token, worker: p.worker, work: p.work, epoch: p.epoch }
    }).collect();
    let mut affected = BTreeSet::new();
    for (_, w) in &handoff.work {
        if let StoredWorkState::Running { worker, .. } = &w.state { affected.insert(worker.clone()); }
    }
    for g in &handoff.groups { affected.insert(g.owner.clone()); }
    for id in &affected {
        if let Some(info) = snap.workers.get(id) { handoff.workers.insert(id.clone(), info.clone()); }
    }
    recompute_used(snap, &affected);
    snap.history_work_cursor = 0;
    Ok((handoff, polls))
}

/// Merge a handoff into a destination snapshot. A worker unknown here (or expired)
/// gets a fresh lease in this shard's clock, so a dead one expires and its moved work is
/// reassigned here. The recovery pass restarts to cover the moved validation index.
fn merge_handoff(snap: &mut Snapshot, handoff: Handoff, now: u64) -> Result<(), String> {
    let mut affected = BTreeSet::new();
    for (r, w) in handoff.work {
        if let Some(existing) = snap.work.get(&r) {
            if serde_json::to_vec(existing).ok() == serde_json::to_vec(&w).ok() { continue }
            return Err(format!("handoff work {r} conflicts with this shard's"));
        }
        if let StoredWorkState::Running { worker, .. } = &w.state { affected.insert(worker.clone()); }
        snap.order.push(r.clone());
        snap.work.insert(r, w);
    }
    for g in handoff.groups {
        if let Some(existing) = snap.groups.iter().find(|x| x.names == g.names) {
            if serde_json::to_vec(existing).ok() == serde_json::to_vec(&g).ok() { continue }
            return Err("handoff group conflicts with this shard's".into());
        }
        affected.insert(g.owner.clone());
        snap.groups.push(g);
    }
    for (id, info) in handoff.workers {
        let entry = snap.workers.entry(id.clone()).or_insert(StoredWorker { capacity_mb: info.capacity_mb, used_mb: 0, lease_until: 0, alive: false });
        if !entry.alive || entry.lease_until <= now {
            entry.alive = true;
            entry.lease_until = now.saturating_add(8);
        }
        affected.insert(id);
    }
    recompute_used(snap, &affected);
    snap.recovering = true;
    snap.recovery_cursor.clear();
    Ok(())
}

fn recompute_used(snap: &mut Snapshot, workers: &BTreeSet<String>) {
    for id in workers {
        let used = snap.work.values().filter(|w| matches!(&w.state, StoredWorkState::Running { worker, .. } if worker == id)).map(|w| w.memory_mb).sum();
        if let Some(info) = snap.workers.get_mut(id) { info.used_mb = used }
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

    fn alive(st: &mut State, w: WorkspaceId, alive: bool) {
        st.workers.insert(w, WorkerInfo { capacity_mb: 1, used_mb: 0, lease_until: 0, alive });
    }

    /// Spill until nothing is over the bounds, as successive saves do.
    fn spill_all(st: &mut State) -> (Vec<WorkReplay>, Vec<PollReplay>) {
        let (mut work, mut polls) = (Vec::new(), Vec::new());
        loop {
            let (w, p) = st.spill_over_caps(SPILL_BUDGET);
            if w.is_empty() && p.is_empty() { return (work, polls) }
            work.extend(w);
            polls.extend(p);
        }
    }

    #[test]
    fn worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot() {
        let mut st = State::default();
        let (a, b, dead) = (WorkspaceId::derive("snapshot-a"), WorkspaceId::derive("snapshot-b"), WorkspaceId::derive("snapshot-dead"));
        alive(&mut st, a, true);
        alive(&mut st, b, true);
        alive(&mut st, dead, false);
        st.remember_poll("b/kept", &b, None, None, 1);
        st.remember_poll("dead/0", &dead, None, None, 1);
        // A worker polling with a fresh token each time, many times over.
        for i in 0..5000 {
            st.remember_poll(&format!("a/{i}"), &a, None, None, 2);
        }
        let (_, polls) = spill_all(&mut st);
        let mine = st.poll_responses.values().filter(|p| p.worker == a.hex()).count();
        assert_eq!(mine, MAX_POLL_TOKENS_PER_WORKER);
        assert!(st.poll_responses.contains_key("a/4999") && !st.poll_responses.contains_key("a/0"));
        assert!(st.poll_responses.contains_key("b/kept"), "another worker's token was evicted");
        assert!(st.poll_responses.contains_key("dead/0"), "a worker's token within its bound was dropped");
        // Every dropped token left as a replay row (W4 history: a retry still resolves).
        assert_eq!(polls.len(), 5000 - MAX_POLL_TOKENS_PER_WORKER);
        assert!(polls.iter().any(|p| p.token == "a/0" && p.worker == a.hex()));
        // Finished work beyond the bound goes, oldest first; queued and running work stays,
        // and so does finished work a remaining poll token names.
        for i in 0..3000 {
            let r = format!("w/{i}");
            let state = match i % 3 { 0 => WorkState::Done, 1 => WorkState::Failed, _ => WorkState::Cancelled };
            st.order.push(r.clone());
            st.work.insert(r, WorkJob { target: Name::parse("T.x"), memory_mb: 1, state, attempts: 1, settled_tick: Some(1) });
        }
        st.remember_poll("b/names-w0", &b, Some("w/0".into()), Some(1), 3);
        for i in 0..5 {
            let r = format!("live/{i}");
            st.order.insert(0, r.clone());
            st.work.insert(r, WorkJob { target: Name::parse("T.y"), memory_mb: 1, state: WorkState::Queued, attempts: 0, settled_tick: None });
        }
        let (work, _) = spill_all(&mut st);
        assert_eq!(st.work.len(), MAX_FINISHED_WORK + 5);
        assert_eq!(work.len(), 3000 - MAX_FINISHED_WORK);
        assert_eq!(st.order.len(), st.work.len());
        assert!(st.order.iter().all(|r| st.work.contains_key(r)));
        assert!((0..5).all(|i| st.work.contains_key(&format!("live/{i}"))));
        assert!(st.work.contains_key("w/0"), "work named by a kept poll token was dropped");
        assert!(st.work.contains_key("w/2999") && !st.work.contains_key("w/1"));
        assert!(work.iter().any(|r| r.request == "w/1" && r.state == TerminalState::Failed));
        let bounded = snapshot_len(&st);
        for i in 0..3000 {
            st.remember_poll(&format!("again/{i}"), &a, None, None, 4);
        }
        spill_all(&mut st);
        assert!(snapshot_len(&st) <= bounded + 4096, "snapshot grew with poll tokens");
    }

    #[test]
    fn rows_over_the_value_limit_stay_in_the_snapshot() {
        let mut st = State::default();
        for i in 0..MAX_FINISHED_WORK + 2 {
            let r = format!("big/{i}");
            let target = if i == 0 { "x".repeat(SPILL_ROW_LIMIT) } else { "T.ok".into() };
            st.order.push(r.clone());
            st.work.insert(r, WorkJob { target: Name::parse(&target), memory_mb: 1, state: WorkState::Done, attempts: 1, settled_tick: Some(1) });
        }
        let (work, _) = st.spill_over_caps(SPILL_BUDGET);
        assert!(st.work.contains_key("big/0"), "an unwritable row left the snapshot");
        assert_eq!(work.iter().map(|r| r.request.as_str()).collect::<Vec<_>>(), vec!["big/1", "big/2"]);
    }

    #[test]
    fn one_save_spills_within_its_budget() {
        let mut st = State::default();
        let a = WorkspaceId::derive("budget-a");
        alive(&mut st, a, true);
        for i in 0..5000 {
            st.remember_poll(&format!("budget/{i:04}"), &a, None, None, 1);
        }
        let (work, polls) = st.spill_over_caps(SPILL_BUDGET);
        let bytes: usize = polls.iter().map(|p| serde_json::to_vec(p).unwrap().len()).sum();
        assert!(work.is_empty() && !polls.is_empty() && bytes <= SPILL_BUDGET);
        assert!(polls.len() < 5000 - MAX_POLL_TOKENS_PER_WORKER, "the budget did not bound one save");
        assert_eq!(st.poll_responses.len() + polls.len(), 5000);
    }
}
