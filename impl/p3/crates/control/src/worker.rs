//! A worker: registers with the controller, keeps its lease, takes target work, has each
//! group validated and publishes it (T1) only with the receipt.
//!
//! The groups come from an impl/p1 store the worker captured into (here: read as is). A
//! group's dependencies are published first, each with its own receipt, because validators
//! check only against published, receipted dependencies. The worker never certifies a group
//! itself: `Writer::publish` refuses a package whose receipt fails the staging rule, and T1
//! re-checks it in the publication transaction.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Duration;

use paralean_store::receipt::SignedJob;
use paralean_store::*;
use std::result::Result;
use tokio::task::JoinHandle;

use crate::controller::{replay_generation_hint, ControlCall, ControlRequest, ControlResponse, TargetReq};
use crate::p1::{self, P1Group};
use paralean_validator_api::rpc;

#[derive(Debug)]
pub enum WorkerError {
    /// The controller or a validator gave no receipt.
    NoReceipt(ControlResponse),
    Store(StoreError),
    Io(String),
    Input(String),
    /// The work's epoch is not the target record's, or this worker is not its owner.
    Stale(String),
}

impl From<StoreError> for WorkerError {
    fn from(e: StoreError) -> Self {
        WorkerError::Store(e)
    }
}

impl WorkerError {
    pub fn guard(&self) -> Option<&GuardFailure> {
        match self {
            WorkerError::Store(e) => e.guard(),
            _ => None,
        }
    }
}

/// A target job handed out by `Poll`.
#[derive(Clone, Debug)]
pub struct Work {
    pub request: String,
    pub target: Name,
    pub epoch: u64,
    pub memory_mb: u64,
}

pub struct WorkerNode {
    pub writer: Writer,
    pub controller: String,
    pub capacity_mb: u64,
    pub groups: BTreeMap<String, P1Group>,
    lamport: AtomicU64,
    call_timeout: Duration,
    /// Each controller endpoint's replay generation, as last learned from a registration
    /// or a refusal (docs/w4-rest-log.md design 3). Poll tokens and validation request
    /// IDs are sent in it.
    generations: Arc<std::sync::Mutex<BTreeMap<String, u64>>>,
}

impl WorkerNode {
    pub fn new(writer: Writer, controller: &str, capacity_mb: u64, p1_store: &Path) -> Result<Arc<WorkerNode>, String> {
        Ok(Arc::new(WorkerNode {
            writer,
            controller: controller.into(),
            capacity_mb,
            groups: p1::load_store(p1_store)?,
            lamport: AtomicU64::new(1),
            call_timeout: Duration::from_secs(900),
            generations: Arc::default(),
        }))
    }

    pub fn id(&self) -> WorkspaceId {
        self.writer.id
    }

    pub async fn call(&self, req: &ControlRequest) -> Result<ControlResponse, WorkerError> {
        crate::controller::call_controller(&self.controller, req, self.writer.signer(), &self.writer.store.ring.authority, self.call_timeout)
            .await.map_err(|e| WorkerError::Io(e.to_string()))
    }

    /// The replay generation last learned for controller endpoint `addr` (0: none known).
    pub fn replay_generation(&self, addr: &str) -> u64 {
        self.generations.lock().unwrap().get(addr).copied().unwrap_or(0)
    }

    fn learn_generation(generations: &std::sync::Mutex<BTreeMap<String, u64>>, addr: &str, response: &ControlResponse) {
        let learned = match response {
            ControlResponse::Registered { replay_generation, .. } => Some(*replay_generation),
            other => replay_generation_hint(other),
        };
        if let Some(g) = learned { generations.lock().unwrap().insert(addr.to_owned(), g); }
    }

    /// Register as a generation-aware client on `addr`, learning its replay generation.
    async fn register_at(addr: &str, worker: String, capacity_mb: u64, signer: &Signer, authority: &[u8; 32],
        generations: &std::sync::Mutex<BTreeMap<String, u64>>) -> std::io::Result<ControlResponse> {
        let call = ControlCall::scoped(0, ControlRequest::Register { worker, capacity_mb });
        let response = rpc::call_authenticated::<_, ControlResponse>(addr, &call, signer, authority, Duration::from_secs(3)).await?;
        Self::learn_generation(generations, addr, &response);
        Ok(response)
    }

    pub async fn register(&self) -> Result<ControlResponse, WorkerError> {
        // Return after the first live shard accepts us. Per-endpoint heartbeat
        // tasks register other shards on Unknown, and Poll does so immediately
        // for the exact shard it contacted. A blackholed endpoint cannot hold
        // up this worker's first heartbeat; the other registrations still finish
        // (and record their shard's replay generation) in the background.
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel();
        for addr in self.controller.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let addr = addr.to_owned();
            let (worker, capacity_mb) = (self.id().hex(), self.capacity_mb);
            let signer = self.writer.signer().clone();
            let authority = self.writer.store.ring.authority;
            let generations = self.generations.clone();
            let tx = tx.clone();
            tokio::spawn(async move {
                let _ = tx.send(Self::register_at(&addr, worker, capacity_mb, &signer, &authority, &generations).await);
            });
        }
        drop(tx);
        while let Some(result) = rx.recv().await {
            if let Ok(r @ ControlResponse::Registered { .. }) = result { return Ok(r) }
        }
        Err(WorkerError::Io("no controller shard accepted registration".into()))
    }

    /// Renew the lease every `every` until the task is aborted (a crash, for the tests).
    pub fn spawn_heartbeats(self: &Arc<Self>, every: Duration) -> JoinHandle<()> {
        let me = self.clone();
        tokio::spawn(async move {
            let mut tasks = tokio::task::JoinSet::new();
            for addr in me.controller.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                let addr = addr.to_owned();
                let worker = me.id().hex();
                let capacity_mb = me.capacity_mb;
                let signer = me.writer.signer().clone();
                let authority = me.writer.store.ring.authority;
                let generations = me.generations.clone();
                tasks.spawn(async move {
                    loop {
                        tokio::time::sleep(every).await;
                        let response = rpc::call_authenticated::<_, ControlResponse>(&addr,
                            &ControlRequest::Heartbeat { worker: worker.clone() }, &signer, &authority, Duration::from_secs(3)).await;
                        if matches!(response, Ok(ControlResponse::Unknown)) {
                            let _ = Self::register_at(&addr, worker.clone(), capacity_mb, &signer, &authority, &generations).await;
                        }
                    }
                });
            }
            while tasks.join_next().await.is_some() {}
        })
    }

    /// A poll on `addr` with `token` in that shard's replay generation; a refusal that
    /// reports a newer generation is retried once in it (a new identity of the token).
    async fn poll_at(&self, addr: &str, token: &str) -> std::io::Result<ControlResponse> {
        let mut response = Err(std::io::Error::other("no poll attempt"));
        for _ in 0..2 {
            let call = ControlCall::scoped(self.replay_generation(addr),
                ControlRequest::PollRequest { worker: self.id().hex(), request: token.to_owned() });
            response = rpc::call_authenticated(addr, &call, self.writer.signer(), &self.writer.store.ring.authority, Duration::from_secs(3)).await;
            match &response {
                Ok(r) if replay_generation_hint(r).is_some_and(|g| g != self.replay_generation(addr)) => {
                    Self::learn_generation(&self.generations, addr, r);
                }
                _ => break,
            }
        }
        response
    }

    pub async fn poll(&self) -> Result<Option<Work>, WorkerError> {
        let request = format!("poll/{}/{}", self.id().hex(), rand::random::<u64>());
        let mut saw_no_work = false;
        for addr in self.controller.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let response = self.poll_at(addr, &request).await;
            match response {
                Ok(ControlResponse::NoWork) => { saw_no_work = true; continue }
                Ok(ControlResponse::Inconclusive { .. }) => continue,
                Ok(ControlResponse::Unknown) => {
                    let registration = Self::register_at(addr, self.id().hex(), self.capacity_mb,
                        self.writer.signer(), &self.writer.store.ring.authority, &self.generations).await;
                    if matches!(registration, Ok(ControlResponse::Registered { .. })) {
                        match self.poll_at(addr, &request).await {
                            Ok(ControlResponse::Work { request, target, epoch, memory_mb }) => {
                                return Ok(Some(Work { request, target: Name::parse(&target), epoch, memory_mb }));
                            }
                            Ok(ControlResponse::NoWork) => saw_no_work = true,
                            _ => {}
                        }
                    }
                    continue;
                }
                Err(_) => continue,
                Ok(response) => return match response {
            ControlResponse::Work { request, target, epoch, memory_mb } => {
                Ok(Some(Work { request, target: Name::parse(&target), epoch, memory_mb }))
            }
            other => Err(WorkerError::NoReceipt(other)),
                },
            }
        }
        if saw_no_work { Ok(None) } else { Err(WorkerError::Io("no controller shard available to poll".into())) }
    }

    /// The group of the P1 store that declares `name`.
    pub fn group_declaring(&self, name: &Name) -> Option<&P1Group> {
        self.groups.values().find(|g| g.names().contains(name))
    }

    /// Prove a target: read its record once (owner, epoch, head), check it matches the work,
    /// publish the dependencies, get a receipt bound to the target and epoch, publish.
    pub async fn prove(&self, work: &Work) -> Result<PublishOutcome, WorkerError> {
        let pt = self.writer.prepare_target(&work.target).await?;
        if pt.epoch != work.epoch {
            return Err(WorkerError::Stale(format!("record epoch {} != work epoch {}", pt.epoch, work.epoch)));
        }
        let g = self.group_declaring(&work.target).ok_or_else(|| WorkerError::Input(format!("no group declares {}", work.target)))?.clone();
        let statement = g.statement(&work.target).unwrap_or_default();
        self.publish_deps(&g).await?;
        let (receipt, job) = self.validate(&g, &work.request, &[(work.target.clone(), statement)], work.memory_mb).await?;
        let pkg = self.package(&g, receipt, job, vec![pt]);
        Ok(self.writer.publish(&pkg).await?)
    }

    /// Publish every dependency of `g` that is not yet published, in dependency order.
    pub async fn publish_deps(&self, g: &P1Group) -> Result<(), WorkerError> {
        let order = p1::closure(&self.groups, &g.gid).map_err(WorkerError::Input)?;
        for gid in &order[..order.len() - 1] {
            let d = self.groups[gid].clone();
            if self.writer.store.marker(&d.decl).await?.is_some() {
                continue;
            }
            let request = format!("dep/{}", d.decl.hex());
            let (receipt, job) = self.validate(&d, &request, &[], 0).await?;
            let pkg = self.package(&d, receipt, job, vec![]);
            match self.writer.publish(&pkg).await {
                Ok(_) => {}
                // Another worker published it first under its own marker.
                Err(StoreError::Guard(GuardFailure::AlreadyPublished { .. })) => {}
                Err(e) => return Err(e.into()),
            }
        }
        Ok(())
    }

    /// Upload the group's payloads (payload before metadata), then ask the controller for a
    /// receipt. Returns the receipt and the envelope it is bound to; only an accepted
    /// receipt is returned.
    pub async fn validate(
        &self,
        g: &P1Group,
        request: &str,
        targets: &[(Name, String)],
        memory_mb: u64,
    ) -> Result<(Receipt, SignedJob), WorkerError> {
        let st = &self.writer.store;
        st.s3.put_opaque(&g.group_object()).await?;
        st.s3.put_opaque(&g.capsule_object()).await?;
        let order = p1::closure(&self.groups, &g.gid).map_err(WorkerError::Input)?;
        let deps: Vec<String> = order[..order.len() - 1].iter().map(|gid| self.groups[gid].capsule_id().hex()).collect();
        let request_id = request;
        let req = ControlRequest::Validate {
            worker: self.id().hex(),
            request: request.into(),
            group: g.decl.hex(),
            capsule: g.capsule_id().hex(),
            deps,
            targets: targets.iter().map(|(n, s)| TargetReq { name: n.to_string(), statement: s.clone() }).collect(),
            memory_mb,
            deadline_ms: 0,
        };
        // A work ID the controller handed out already names its generation; any other ID
        // goes in the newest generation this worker knows, or the one a refusal reports
        // (the owning shard is not known in advance).
        let scoped = request_id.starts_with(crate::replay::SCOPE_MARK);
        let mut generation = if scoped { 0 } else { self.generations.lock().unwrap().values().copied().max().unwrap_or(0) };
        let mut response = None;
        for _ in 0..3 {
            let call = ControlCall::scoped(generation, req.clone());
            let r = crate::controller::call_controller(&self.controller, &call, self.writer.signer(), &self.writer.store.ring.authority, self.call_timeout)
                .await.map_err(|e| WorkerError::Io(e.to_string()))?;
            match replay_generation_hint(&r) {
                Some(g) if !scoped && g != generation => { generation = g; response = Some(r) }
                _ => { response = Some(r); break }
            }
        }
        match response.expect("at least one attempt") {
            ControlResponse::Receipt { receipt, job } => {
                let r = Receipt::from_bytes(&hex::decode(&receipt).map_err(|e| WorkerError::Io(e.to_string()))?)
                    .map_err(|e| WorkerError::Io(e.to_string()))?;
                let j = SignedJob::from_bytes(&hex::decode(&job).map_err(|e| WorkerError::Io(e.to_string()))?)
                    .map_err(|e| WorkerError::Io(e.to_string()))?;
                if r.body.verdict != Verdict::Accepted {
                    return Err(WorkerError::NoReceipt(ControlResponse::Receipt { receipt, job }));
                }
                Ok((r, j))
            }
            other => Err(WorkerError::NoReceipt(other)),
        }
    }

    /// The package for `g`: one revision per name (a prepared target's revision lists the
    /// recorded head as parent), and its marker.
    pub fn package(&self, g: &P1Group, receipt: Receipt, job: SignedJob, targets: Vec<PreparedTarget>) -> Package {
        let lamport = self.lamport.fetch_add(1, Ordering::SeqCst);
        let author = AgentId::derive(&format!("agent/{}", self.id().hex()));
        let capsule = g.capsule_object();
        let mut revisions: Vec<Revision> = g
            .names()
            .into_iter()
            .map(|name| {
                let parents = targets.iter().find(|t| t.name == name).and_then(|t| t.head).into_iter().collect();
                Revision { group: g.decl, name, parents, capsule: capsule.id(), workspace: self.id() }
            })
            .collect();
        revisions.sort_by_key(|r| r.id());
        let mut rev_ids: Vec<Id> = revisions.iter().map(|r| r.id()).collect();
        rev_ids.sort();
        let marker = Marker {
            group: g.decl,
            revisions: rev_ids,
            receipt: receipt.id(),
            file_path: g.file(),
            anchor: Anchor::FileStart,
            lamport,
            author,
            root_path: vec![],
            lineage_keys: g.names().into_iter().map(|n| (n, lamport, author)).collect(),
        };
        Package { group: g.group_object(), chunks: vec![], capsule, receipt, job, revisions, marker, targets }
    }

    /// Run work forever: poll, prove, report. `hold` delays each proof after the work is
    /// taken (a stand-in for a long elaboration, so tests can kill a worker mid-job).
    pub async fn run(self: &Arc<Self>, idle: Duration, hold: Duration) {
        loop {
            match self.poll().await {
                Ok(Some(w)) => {
                    tokio::time::sleep(hold).await;
                    let ok = self.prove(&w).await.is_ok();
                    let _ = self.call(&ControlRequest::Finish { worker: self.id().hex(), request: w.request.clone(), ok }).await;
                }
                Ok(None) => tokio::time::sleep(idle).await,
                Err(WorkerError::NoReceipt(ControlResponse::Unknown)) => {
                    let _ = self.register().await;
                }
                Err(_) => tokio::time::sleep(idle).await,
            }
        }
    }
}
