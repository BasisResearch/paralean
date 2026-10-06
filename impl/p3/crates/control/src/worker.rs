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
use paralean_validator_api::rpc;
use tokio::task::JoinHandle;

use crate::controller::{ControlRequest, ControlResponse, TargetReq};
use crate::p1::{self, P1Group};

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
        }))
    }

    pub fn id(&self) -> WorkspaceId {
        self.writer.id
    }

    pub async fn call(&self, req: &ControlRequest) -> Result<ControlResponse, WorkerError> {
        rpc::call(&self.controller, req, self.call_timeout).await.map_err(|e| WorkerError::Io(e.to_string()))
    }

    pub async fn register(&self) -> Result<ControlResponse, WorkerError> {
        self.call(&ControlRequest::Register { worker: self.id().hex(), capacity_mb: self.capacity_mb }).await
    }

    /// Renew the lease every `every` until the task is aborted (a crash, for the tests).
    pub fn spawn_heartbeats(self: &Arc<Self>, every: Duration) -> JoinHandle<()> {
        let me = self.clone();
        tokio::spawn(async move {
            loop {
                tokio::time::sleep(every).await;
                let _ = me.call(&ControlRequest::Heartbeat { worker: me.id().hex() }).await;
            }
        })
    }

    pub async fn poll(&self) -> Result<Option<Work>, WorkerError> {
        match self.call(&ControlRequest::Poll { worker: self.id().hex() }).await? {
            ControlResponse::Work { request, target, epoch, memory_mb } => {
                Ok(Some(Work { request, target: Name::parse(&target), epoch, memory_mb }))
            }
            ControlResponse::NoWork => Ok(None),
            other => Err(WorkerError::NoReceipt(other)),
        }
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
        match self.call(&req).await? {
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
