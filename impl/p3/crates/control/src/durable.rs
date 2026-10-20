//! Controller lease and state in the deployment's FoundationDB key space.
//! Every assignment reads the lease in the same transaction that advances target
//! epochs, so a former leader cannot publish an assignment after takeover.

use std::time::Duration;

use foundationdb::Transaction;
use paralean_store::pce::{Enc, Pce};
use paralean_store::{AssignEntry, Name, Receipt, Store, TargetRecord, WorkspaceId};
use paralean_store::receipt::SignedJob;
use paralean_store::id::sha256;
use serde::{Deserialize, Serialize};

/// The per-target ownership claim shared by every scheduler of a deployment.
/// A W4 controller shard stores its shard number; P5's task bridge stores
/// [`P5_TASK_CLAIM`]. Each side refuses a target the other has claimed, so P5
/// and a controller shard never reassign each other's targets through T4.
pub fn target_claim_key(store: &Store, name: &Name) -> Vec<u8> {
    store.meta.keys.root.pack(&("controller", "target-shard", foundationdb::tuple::Bytes::from(&name.to_pce()[..])))
}

/// Claim value for targets scheduled by P5's task bridge. Its length differs from
/// every shard number's encoding, so no shard can mistake it for its own.
pub const P5_TASK_CLAIM: &[u8] = b"p5-task";

/// Claim `name` for a P5 task before any T4 write, or refuse a target that a
/// controller shard owns. The claim is write-once, so once it commits no shard
/// can assign the target; a shard writes its own claim in its T4 transaction.
pub async fn claim_for_task(store: &Store, name: &Name) -> Result<(), String> {
    let key = target_claim_key(store, name);
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        if !claim_in(&trx, &key, name).await? { return Ok(()) }
        match trx.commit().await {
            Ok(_) => return Ok(()),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("target claim outcome unresolved".into())
}

/// Read the claim at `key` in `trx`: refuse a shard's claim, and write P5's
/// claim if there is none. Returns whether a write is pending.
pub async fn claim_in(trx: &Transaction, key: &[u8], name: &Name) -> Result<bool, String> {
    match trx.get(key, false).await.map_err(|e| e.to_string())? {
        Some(v) if v.as_ref() == P5_TASK_CLAIM => Ok(false),
        Some(_) if !cfg!(feature = "mutate-no-task-claim-check") => {
            Err(format!("target {name} belongs to a controller shard, not a P5 task"))
        }
        Some(_) => Ok(false),
        None => { trx.set(key, P5_TASK_CLAIM); Ok(true) }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Lease {
    pub holder: String,
    pub term: u64,
    /// Expiration in the shard's transactionally advanced logical clock.
    pub until_tick: u64,
}

pub struct Durable {
    pub store: Store,
    pub holder: String,
    pub lease_ms: u64,
    pub shard: u32,
    pub shards: u32,
}

const CHUNK_SIZE: usize = 60 * 1024;
const MAX_SHARD_SNAPSHOT: usize = 8 * 1024 * 1024;
const MAX_HISTORY_WRITE: usize = 256 * 1024;
const MAX_HISTORY_VALUE: usize = 90 * 1024;
const LEASE_TICKS: u64 = 8;

/// Immutable replay identity for a terminal work request. These rows remain
/// after the current controller snapshot drops the completed job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WorkReplay {
    pub request: String,
    pub target: String,
    pub memory_mb: u64,
    pub state: TerminalState,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TerminalState { Done, Failed, Cancelled }

/// First selection of a poll token. A retry resolves `work` against the
/// current assignment; an old selection never grants a new job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PollReplay {
    pub token: String,
    pub worker: String,
    pub work: Option<String>,
    pub epoch: Option<u64>,
}

#[derive(Serialize, Deserialize)]
pub(crate) struct SnapshotHead {
    pub(crate) hash: String,
    pub(crate) chunks: u32,
    pub(crate) len: usize,
    pub(crate) generation: u64,
}

#[derive(Serialize, Deserialize)]
pub(crate) struct RetiredSnapshot {
    pub(crate) chunks: u32,
    pub(crate) len: usize,
    pub(crate) retired_tick: u64,
    pub(crate) generation: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GroupRequest {
    pub request: String,
    pub names: Vec<String>,
    pub owner: String,
}

impl Durable {
    pub fn new(store: Store, lease: Duration) -> Self {
        Self::new_shard(store, lease, 0, 1)
    }

    pub fn new_shard(store: Store, lease: Duration, shard: u32, shards: u32) -> Self {
        assert!(shards > 0 && shard < shards, "invalid controller shard topology");
        Durable { store, holder: hex::encode(rand::random::<[u8; 16]>()), lease_ms: (lease.as_millis() as u64).max(500), shard, shards }
    }

    pub(crate) fn lease_key(&self) -> Vec<u8> { self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "lease")) }
    pub(crate) fn clock_key(&self) -> Vec<u8> { self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "clock")) }
    pub(crate) fn state_key(&self) -> Vec<u8> { self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "state")) }
    pub(crate) fn chunk_key(&self, hash: &str, index: u32) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "chunk", hash, index as u64))
    }
    pub(crate) fn retired_key(&self, hash: &str) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "retired", hash))
    }
    pub(crate) fn retained_key(&self, hash: &str) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "retained", hash))
    }
    pub(crate) fn retired_subspace(&self) -> foundationdb::tuple::Subspace {
        self.store.meta.keys.root.subspace(&("controller", "shard", self.shard as u64, "retired"))
    }
    fn work_replay_key(&self, request: &str) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "history-work",
            foundationdb::tuple::Bytes::from(&sha256(request.as_bytes())[..])))
    }
    fn poll_replay_key(&self, token: &str) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "history-poll",
            foundationdb::tuple::Bytes::from(&sha256(token.as_bytes())[..])))
    }
    pub async fn current_snapshot_hash(&self) -> Result<Option<String>, String> {
        self.store.meta.get(self.state_key()).await.map_err(|e| e.to_string())?
            .map(|v| serde_json::from_slice::<SnapshotHead>(&v).map(|h| h.hash).map_err(|e| e.to_string())).transpose()
    }
    pub async fn work_replay(&self, request: &str) -> Result<Option<WorkReplay>, String> {
        let record = self.store.meta.get(self.work_replay_key(request)).await.map_err(|e| e.to_string())?
            .map(|v| serde_json::from_slice::<WorkReplay>(&v).map_err(|e| e.to_string())).transpose()?;
        if record.as_ref().is_some_and(|r| r.request != request) { return Err("work replay hash collision".into()) }
        Ok(record)
    }
    pub async fn poll_replay(&self, token: &str) -> Result<Option<PollReplay>, String> {
        let record = self.store.meta.get(self.poll_replay_key(token)).await.map_err(|e| e.to_string())?
            .map(|v| serde_json::from_slice::<PollReplay>(&v).map_err(|e| e.to_string())).transpose()?;
        if record.as_ref().is_some_and(|r| r.token != token) { return Err("poll replay hash collision".into()) }
        Ok(record)
    }
    fn topology_key(&self) -> Vec<u8> { self.store.meta.keys.root.pack(&("controller", "topology")) }
    fn target_shard_key(&self, name: &Name) -> Vec<u8> { target_claim_key(&self.store, name) }
    fn work_shard_key(&self, request: &str) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "work-shard", foundationdb::tuple::Bytes::from(&sha256(request.as_bytes())[..])))
    }
    fn validation_shard_key(&self, request: &[u8]) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "validation-shard", foundationdb::tuple::Bytes::from(&sha256(request)[..])))
    }
    fn validation_index_key(&self, request: &[u8]) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "validation-job", foundationdb::tuple::Bytes::from(request)))
    }
    pub fn validation_jobs_subspace(&self) -> foundationdb::tuple::Subspace {
        self.store.meta.keys.root.subspace(&("controller", "shard", self.shard as u64, "validation-job"))
    }
    pub fn hash_shard(name: &Name, shards: u32) -> u32 {
        let hash = sha256(&name.to_pce());
        (u64::from_be_bytes(hash[0..8].try_into().unwrap()) % shards as u64) as u32
    }
    pub async fn shard_for_target(&self, name: &Name) -> Result<u32, String> {
        Ok(self.mapped_shard(name).await?.unwrap_or_else(|| Self::hash_shard(name, self.shards)))
    }
    pub async fn mapped_shard(&self, name: &Name) -> Result<Option<u32>, String> {
        let key = self.target_shard_key(name);
        match self.store.meta.get(key).await.map_err(|e| e.to_string())? {
            Some(v) => {
                let b: [u8; 4] = v.as_slice().try_into().map_err(|_| "invalid target shard catalog")?;
                let n = u32::from_be_bytes(b);
                if n >= self.shards { return Err("target shard outside configured topology".into()) }
                Ok(Some(n))
            }
            None => Ok(None),
        }
    }
    pub async fn shard_for_work(&self, request: &str) -> Result<Option<u32>, String> {
        match self.store.meta.get(self.work_shard_key(request)).await.map_err(|e| e.to_string())? {
            Some(v) => {
                if v.len() != 36 { return Err("invalid work shard catalog".into()) }
                let b: [u8; 4] = v.get(..4).ok_or("invalid work shard catalog")?.try_into().unwrap();
                let n = u32::from_be_bytes(b);
                if n >= self.shards { return Err("work shard outside configured topology".into()) }
                Ok(Some(n))
            }
            None => Ok(None),
        }
    }
    pub async fn shard_for_validation(&self, request: &str) -> Result<Option<u32>, String> {
        self.shard_for_validation_bytes(request.as_bytes()).await
    }
    pub async fn shard_for_validation_bytes(&self, request: &[u8]) -> Result<Option<u32>, String> {
        match self.store.meta.get(self.validation_shard_key(request)).await.map_err(|e| e.to_string())? {
            Some(v) => {
                let b: [u8; 4] = v.as_slice().try_into().map_err(|_| "invalid validation shard catalog")?;
                let n = u32::from_be_bytes(b);
                if n >= self.shards { return Err("validation shard outside configured topology".into()) }
                Ok(Some(n))
            }
            None => Ok(None),
        }
    }
    pub async fn reserve_work_shard(&self, request: &str, target: &Name, term: u64) -> Result<(), String> {
        let key = self.work_shard_key(request);
        let target_key = self.target_shard_key(target);
        let mut value = self.shard.to_be_bytes().to_vec();
        value.extend_from_slice(&sha256(&target.to_pce()));
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let mut claimed_target = false;
            if let Some(v) = trx.get(&target_key, false).await.map_err(|e| e.to_string())? {
                if v.as_ref() != self.shard.to_be_bytes() { return Err("target belongs to another controller shard".into()) }
            } else {
                trx.set(&target_key, &self.shard.to_be_bytes());
                claimed_target = true;
            }
            if let Some(v) = trx.get(&key, false).await.map_err(|e| e.to_string())? {
                if v.as_ref() != value { return Err("work request ID already used for another target or shard".into()); }
                if !claimed_target { return Ok(()); }
            } else {
                trx.set(&key, &value);
            }
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("work shard reservation outcome unresolved".into())
    }
    async fn topology_in(&self, trx: &Transaction) -> Result<(), String> {
        let key = self.topology_key();
        match trx.get(&key, false).await.map_err(|e| e.to_string())? {
            Some(value) if value.as_ref() == self.shards.to_be_bytes() => Ok(()),
            Some(_) if !cfg!(feature = "mutate-no-shard-topology") => Err("controller shard topology differs from deployment".into()),
            Some(_) => Ok(()),
            None => {
                for kind in ["state", "lease"] {
                    let old = self.store.meta.keys.root.pack(&("controller", kind));
                    if !cfg!(feature = "mutate-no-shard-topology")
                        && trx.get(&old, false).await.map_err(|e| e.to_string())?.is_some() {
                        return Err("legacy controller deployment requires offline migration".into());
                    }
                }
                trx.set(&key, &self.shards.to_be_bytes());
                // Fence an old binary too. It always reads the legacy lease key
                // before acting; an invalid sentinel makes it fail closed. A
                // concurrent old acquisition conflicts with this write.
                let old_lease = self.store.meta.keys.root.pack(&("controller", "lease"));
                trx.set(&old_lease, b"w4-sharded-controller");
                Ok(())
            }
        }
    }
    pub(crate) async fn read_tick(trx: &Transaction, key: &[u8]) -> Result<u64, String> {
        let value = trx.get(key, false).await.map_err(|e| e.to_string())?;
        value.map(|v| {
            let bytes: [u8; 8] = v.as_ref().try_into().map_err(|_| "invalid controller clock")?;
            Ok(u64::from_be_bytes(bytes))
        }).transpose().map(|v| v.unwrap_or(0))
    }
    pub async fn tick(&self) -> Result<u64, String> {
        let key = self.clock_key();
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.topology_in(&trx).await?;
            let next = Self::read_tick(&trx, &key).await?.checked_add(1).ok_or("controller logical clock exhausted")?;
            trx.set(&key, &next.to_be_bytes());
            match trx.commit().await {
                Ok(_) => return Ok(next),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller tick outcome unresolved".into())
    }
    pub async fn clock(&self) -> Result<u64, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        Self::read_tick(&trx, &self.clock_key()).await
    }
    pub(crate) async fn require_lease(&self, trx: &Transaction, term: u64) -> Result<u64, String> {
        let tick = Self::read_tick(trx, &self.clock_key()).await?;
        let Some(lease) = Self::read_lease(trx, &self.lease_key()).await? else { return Err("controller lost lease".into()) };
        if lease.holder != self.holder
            || (!cfg!(feature = "mutate-no-term-fence") && lease.term != term)
            || (!cfg!(feature = "mutate-no-logical-expiry") && lease.until_tick <= tick) {
            return Err("controller lost lease".into());
        }
        Ok(tick)
    }
    fn group_request_key(&self, request: &str) -> Vec<u8> {
        let hash = sha256(request.as_bytes());
        self.store.meta.keys.root.pack(&("controller", "group-request", foundationdb::tuple::Bytes::from(&hash[..])))
    }

    pub async fn group_request(&self, request: &str) -> Result<Option<GroupRequest>, String> {
        self.store.meta.get(self.group_request_key(request)).await.map_err(|e| e.to_string())?
            .map(|bytes| serde_json::from_slice(&bytes).map_err(|e| e.to_string())).transpose()
    }

    /// Reserve an immutable request descriptor before the group intent. This
    /// preserves identity even after the group's latest request changes owners.
    pub async fn reserve_group_request(&self, descriptor: &GroupRequest, term: u64) -> Result<(), String> {
        let key = self.group_request_key(&descriptor.request);
        let bytes = serde_json::to_vec(descriptor).map_err(|e| e.to_string())?;
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            if let Some(old) = trx.get(&key, false).await.map_err(|e| e.to_string())? {
                let old: GroupRequest = serde_json::from_slice(&old).map_err(|e| e.to_string())?;
                if &old == descriptor { return Ok(()) }
                return Err("assignment request ID already used for another group or owner".into());
            }
            trx.set(&key, &bytes);
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("group request reservation outcome unresolved".into())
    }

    async fn read_lease(trx: &Transaction, key: &[u8]) -> Result<Option<Lease>, String> {
        trx.get(key, false).await.map_err(|e| e.to_string())?
            .map(|b| serde_json::from_slice(&b).map_err(|e| e.to_string())).transpose()
    }

    pub async fn acquire_or_renew(&self) -> Result<Option<Lease>, String> {
        let key = self.lease_key();
        let db = &self.store.meta.db;
        let mut trx = db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.topology_in(&trx).await?;
            let now = Self::read_tick(&trx, &self.clock_key()).await?;
            let old = match Self::read_lease(&trx, &key).await {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            if old.as_ref().is_some_and(|l| l.holder != self.holder && l.until_tick > now) {
                return Ok(None);
            }
            let term = match &old {
                None => 1,
                Some(l) if l.holder == self.holder && l.until_tick > now => l.term,
                Some(l) => l.term.checked_add(1).ok_or("controller term exhausted")?,
            };
            let lease = Lease { holder: self.holder.clone(), term, until_tick: now.saturating_add(LEASE_TICKS) };
            let bytes = serde_json::to_vec(&lease).map_err(|e| e.to_string())?;
            trx.set(&key, &bytes);
            match trx.commit().await {
                Ok(_) => return Ok(Some(lease)),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller lease outcome unresolved".into())
    }

    pub async fn current(&self) -> Result<Option<Lease>, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        let tick = Self::read_tick(&trx, &self.clock_key()).await?;
        let lease = Self::read_lease(&trx, &self.lease_key()).await?;
        Ok(lease.filter(|l| l.holder == self.holder && l.until_tick > tick))
    }

    pub async fn load(&self) -> Result<Option<Vec<u8>>, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        let Some(v) = trx.get(&self.state_key(), false).await.map_err(|e| e.to_string())? else { return Ok(None) };
        let head: SnapshotHead = serde_json::from_slice(&v).map_err(|e| e.to_string())?;
        if head.len > MAX_SHARD_SNAPSHOT || head.chunks as usize != head.len.div_ceil(CHUNK_SIZE) {
            return Err("invalid controller snapshot head".into());
        }
        let mut bytes = Vec::with_capacity(head.len);
        for index in 0..head.chunks {
            let chunk = trx.get(&self.chunk_key(&head.hash, index), false).await.map_err(|e| e.to_string())?
                .ok_or_else(|| format!("controller snapshot chunk {index} missing"))?;
            bytes.extend_from_slice(&chunk);
        }
        if bytes.len() != head.len || hex::encode(sha256(&bytes)) != head.hash {
            return Err("controller snapshot hash mismatch".into());
        }
        Ok(Some(bytes))
    }

    pub async fn save(&self, bytes: &[u8], term: u64) -> Result<(), String> {
        self.save_with_history(bytes, term, &[], &[]).await
    }

    /// Atomically publish a pruned snapshot and immutable replay rows. A
    /// committed head can never omit a terminal request or poll token unless
    /// its replay record was committed in the same FDB transaction.
    pub async fn save_with_history(&self, bytes: &[u8], term: u64, work: &[WorkReplay], polls: &[PollReplay]) -> Result<(), String> {
        if bytes.len() > MAX_SHARD_SNAPSHOT { return Err("controller shard snapshot exceeds 8 MiB".into()) }
        let work_values = work.iter().map(|r| serde_json::to_vec(r).map_err(|e| e.to_string())).collect::<Result<Vec<_>, _>>()?;
        let poll_values = polls.iter().map(|r| serde_json::to_vec(r).map_err(|e| e.to_string())).collect::<Result<Vec<_>, _>>()?;
        if work_values.iter().chain(poll_values.iter()).any(|v| v.len() > MAX_HISTORY_VALUE) {
            return Err("controller history replay record exceeds FDB value limit".into());
        }
        let history_bytes: usize = work_values.iter().chain(poll_values.iter()).map(Vec::len).sum();
        if history_bytes > MAX_HISTORY_WRITE { return Err("controller history batch exceeds transaction write budget".into()) }
        let hash = hex::encode(sha256(bytes));
        let db = &self.store.meta.db;
        let sk = self.state_key();
        let mut trx = db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let tick = if cfg!(feature = "mutate-history-no-term-fence") && (!work.is_empty() || !polls.is_empty()) {
                Self::read_tick(&trx, &self.clock_key()).await?
            } else {
                self.require_lease(&trx, term).await?
            };
            for (record, value) in work.iter().zip(&work_values) {
                let key = self.work_replay_key(&record.request);
                match trx.get(&key, false).await.map_err(|e| e.to_string())? {
                    Some(old) if old.as_ref() == value => {}
                    Some(_) if !cfg!(feature = "mutate-history-no-row-conflict") =>
                        return Err("work replay ID already has another descriptor".into()),
                    Some(_) => trx.set(&key, value),
                    None if !cfg!(feature = "mutate-history-omit-work-marker") => trx.set(&key, value),
                    None => {}
                }
            }
            for (record, value) in polls.iter().zip(&poll_values) {
                let key = self.poll_replay_key(&record.token);
                match trx.get(&key, false).await.map_err(|e| e.to_string())? {
                    Some(old) if old.as_ref() == value => {}
                    Some(_) if !cfg!(feature = "mutate-history-no-row-conflict") =>
                        return Err("poll replay ID already has another binding".into()),
                    Some(_) => trx.set(&key, value),
                    None if !cfg!(feature = "mutate-history-omit-poll-marker") => trx.set(&key, value),
                    None => {}
                }
            }
            let previous = trx.get(&sk, false).await.map_err(|e| e.to_string())?
                .map(|v| serde_json::from_slice::<SnapshotHead>(&v).map_err(|e| e.to_string())).transpose()?;
            let generation = previous.as_ref().map_or(1, |h| h.generation.saturating_add(1));
            let head = SnapshotHead { hash: hash.clone(), chunks: bytes.len().div_ceil(CHUNK_SIZE) as u32, len: bytes.len(), generation };
            let value = serde_json::to_vec(&head).map_err(|e| e.to_string())?;
            if let Some(old) = &previous {
                if old.hash != hash {
                    let retired = RetiredSnapshot { chunks: old.chunks, len: old.len, retired_tick: tick, generation: old.generation };
                    trx.set(&self.retired_key(&old.hash), &serde_json::to_vec(&retired).map_err(|e| e.to_string())?);
                }
            }
            for (index, chunk) in bytes.chunks(CHUNK_SIZE).enumerate() {
                trx.set(&self.chunk_key(&hash, index as u32), chunk);
            }
            trx.set(&sk, &value);
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller state outcome unresolved".into())
    }

    /// Atomic T4 for all names, with the controller lease as an FDB conflict read.
    /// A retry of `request` recovers the same epochs even after an unknown commit.
    pub async fn assign_group(&self, names: &[Name], owner: WorkspaceId, request: &[u8], term: u64) -> Result<Vec<u64>, String> {
        if names.is_empty() { return Err("empty target group".into()) }
        let mut sorted = names.to_vec();
        sorted.sort_by_key(|n| n.to_pce());
        sorted.dedup();
        if sorted.len() != names.len() { return Err("duplicate target name".into()) }
        let keys = &self.store.meta.keys;
        let db = &self.store.meta.db;
        let mut trx = db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let mut claimed_target = false;
            for name in names {
                let key = self.target_shard_key(name);
                if let Some(v) = trx.get(&key, false).await.map_err(|e| e.to_string())? {
                    if !cfg!(feature = "mutate-no-shard-catalog") && v.as_ref() != self.shard.to_be_bytes() { return Err("target belongs to another controller shard".into()) }
                } else {
                    trx.set(&key, &self.shard.to_be_bytes());
                    claimed_target = true;
                }
            }
            let mut epochs = Vec::with_capacity(names.len());
            let mut missing = Vec::new();
            for name in names {
                let rk = keys.assign_request(name, request);
                if let Some(v) = trx.get(&rk, false).await.map_err(|e| e.to_string())? {
                    let mut d = paralean_store::pce::Dec::new(&v);
                    let n = d.uvarint().map_err(|e| e.to_string())?;
                    d.end().map_err(|e| e.to_string())?;
                    let current = trx.get(&keys.target(name), false).await.map_err(|e| e.to_string())?
                        .ok_or("target record disappeared")?;
                    let current = TargetRecord::from_pce(&current).map_err(|e| e.to_string())?;
                    if current.owner != owner || current.epoch != n {
                        return Err(format!("assignment for {name} superseded"));
                    }
                    epochs.push(n);
                } else {
                    let tk = keys.target(name);
                    let cur = trx.get(&tk, false).await.map_err(|e| e.to_string())?
                        .map(|v| TargetRecord::from_pce(&v).map_err(|e| e.to_string())).transpose()?;
                    let epoch = cur.as_ref().map_or(0, |r| r.epoch + 1);
                    let rec = TargetRecord { name: name.clone(), owner, epoch, head: cur.and_then(|r| r.head), last_request: request.to_vec() };
                    missing.push((name.clone(), rec));
                    epochs.push(epoch);
                }
            }
            if missing.is_empty() && !claimed_target { return Ok(epochs) }
            for (name, rec) in missing {
                trx.set(&keys.target(&name), &rec.to_pce());
                trx.set(&keys.assign(&name, rec.epoch), &AssignEntry { owner, request: request.to_vec() }.to_pce());
                trx.set(&keys.assign_request(&name, request), &Enc::new().uvarint(rec.epoch).out.clone());
            }
            match trx.commit().await {
                Ok(_) => return Ok(epochs),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("target assignment outcome unresolved".into())
    }

    /// J2 is leader-fenced as well as write-once: an old controller cannot finish
    /// dispatch after a new replica takes the lease.
    pub async fn record_receipt(&self, request: &[u8], receipt: &Receipt, term: u64) -> Result<Receipt, String> {
        let rk = self.store.meta.keys.job_receipt(request);
        let route_key = self.validation_shard_key(request);
        let job_key = self.store.meta.keys.job_request(request);
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            if !cfg!(feature = "mutate-no-receipt-shard-check") {
                match trx.get(&route_key, false).await.map_err(|e| e.to_string())? {
                    Some(route) if route.as_ref() == self.shard.to_be_bytes() => {}
                    Some(_) => return Err("validation request belongs to another shard".into()),
                    None if trx.get(&job_key, false).await.map_err(|e| e.to_string())?.is_some() => {
                        return Err("issued job has no validation shard route".into());
                    }
                    None => {}
                }
            }
            if let Some(bytes) = trx.get(&rk, false).await.map_err(|e| e.to_string())? {
                return Receipt::from_bytes(&bytes).map_err(|e| e.to_string());
            }
            trx.set(&rk, &receipt.to_bytes());
            match trx.commit().await {
                Ok(_) => return Ok(receipt.clone()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("receipt outcome unresolved".into())
    }

    pub async fn issue_job(&self, job: &SignedJob, term: u64) -> Result<SignedJob, String> {
        let key = self.store.meta.keys.job_request(&job.body.request);
        let route_key = self.validation_shard_key(&job.body.request);
        let index_key = self.validation_index_key(&job.body.request);
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let had_route = if let Some(v) = trx.get(&route_key, false).await.map_err(|e| e.to_string())? {
                if v.as_ref() != self.shard.to_be_bytes() { return Err("validation request belongs to another shard".into()) }
                true
            } else if !cfg!(feature = "mutate-no-validation-catalog") {
                trx.set(&route_key, &self.shard.to_be_bytes());
                false
            } else { false };
            if let Some(bytes) = trx.get(&key, false).await.map_err(|e| e.to_string())? {
                if !had_route { return Err("issued job has no validation shard route".into()) }
                let stored = SignedJob::from_bytes(&bytes).map_err(|e| e.to_string())?;
                if trx.get(&index_key, false).await.map_err(|e| e.to_string())?.is_some() { return Ok(stored) }
                trx.set(&index_key, &bytes);
                match trx.commit().await {
                    Ok(_) => return Ok(stored),
                    Err(e) => { trx = e.on_error().await.map_err(|e| e.to_string())?; continue }
                }
            }
            trx.set(&key, &job.to_bytes());
            trx.set(&index_key, &job.to_bytes());
            match trx.commit().await {
                Ok(_) => return Ok(job.clone()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("job issue outcome unresolved".into())
    }

    pub async fn cancel_job(&self, request: &[u8], term: u64) -> Result<(), String> {
        let key = self.store.meta.keys.job_cancel(request);
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            if trx.get(&key, false).await.map_err(|e| e.to_string())?.is_some() { return Ok(()) }
            trx.set(&key, b"1");
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("job cancel outcome unresolved".into())
    }
}
