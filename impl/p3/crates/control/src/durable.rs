//! Controller lease and state in the deployment's FoundationDB key space.
//! Every assignment reads the lease in the same transaction that advances target
//! epochs, so a former leader cannot publish an assignment after takeover.

use std::time::{Duration, SystemTime, UNIX_EPOCH};

use foundationdb::Transaction;
use paralean_store::pce::{Enc, Pce};
use paralean_store::{AssignEntry, Name, Receipt, Store, TargetRecord, WorkspaceId};
use paralean_store::id::sha256;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Lease {
    pub holder: String,
    pub term: u64,
    pub until_ms: u64,
}

pub fn now_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).unwrap_or_default().as_millis() as u64
}

pub struct Durable {
    pub store: Store,
    pub holder: String,
    pub lease_ms: u64,
}

const CHUNK_SIZE: usize = 60 * 1024;
const MAX_SNAPSHOT: usize = 8 * 1024 * 1024;

#[derive(Serialize, Deserialize)]
struct SnapshotHead {
    hash: String,
    chunks: u32,
    len: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GroupRequest {
    pub request: String,
    pub names: Vec<String>,
    pub owner: String,
}

impl Durable {
    pub fn new(store: Store, lease: Duration) -> Self {
        Durable { store, holder: hex::encode(rand::random::<[u8; 16]>()), lease_ms: (lease.as_millis() as u64).max(500) }
    }

    fn lease_key(&self) -> Vec<u8> { self.store.meta.keys.root.pack(&("controller", "lease")) }
    fn state_key(&self) -> Vec<u8> { self.store.meta.keys.root.pack(&("controller", "state")) }
    fn chunk_key(&self, hash: &str, index: u32) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "chunk", hash, index as u64))
    }
    fn group_request_key(&self, request: &str) -> Vec<u8> {
        let hash = sha256(request.as_bytes());
        self.store.meta.keys.root.pack(&("controller", "group-request", foundationdb::tuple::Bytes::from(&hash[..])))
    }

    fn recovery_key(&self, worker: &WorkspaceId, request: &[u8]) -> Vec<u8> {
        let mut id = worker.0.to_vec();
        id.extend_from_slice(request);
        self.store.meta.keys.root.pack(&("controller", "recovery", foundationdb::tuple::Bytes::from(&sha256(&id)[..])))
    }

    /// Count one recovery dispatch of (`worker`, `request`) if fewer than `limit` happened
    /// so far (over all leaders); false when the envelope has used them all.
    pub async fn count_recovery(&self, worker: &WorkspaceId, request: &[u8], limit: u64, term: u64) -> Result<bool, String> {
        let key = self.recovery_key(worker, request);
        let lk = self.lease_key();
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let Some(lease) = Self::read_lease(&trx, &lk).await? else { return Err("controller lost lease".into()) };
            if lease.holder != self.holder || lease.term != term || lease.until_ms <= now_ms() {
                return Err("controller lost lease".into());
            }
            let used = match trx.get(&key, false).await.map_err(|e| e.to_string())? {
                Some(v) => u64::from_be_bytes(v[..].try_into().map_err(|_| "bad recovery count")?),
                None => 0,
            };
            if used >= limit { return Ok(false) }
            trx.set(&key, &(used + 1).to_be_bytes());
            match trx.commit().await {
                Ok(_) => return Ok(true),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("recovery count outcome unresolved".into())
    }

    pub async fn group_request(&self, request: &str) -> Result<Option<GroupRequest>, String> {
        self.store.meta.get(self.group_request_key(request)).await.map_err(|e| e.to_string())?
            .map(|bytes| serde_json::from_slice(&bytes).map_err(|e| e.to_string())).transpose()
    }

    /// Reserve an immutable request descriptor before the group intent. This
    /// preserves identity even after the group's latest request changes owners.
    pub async fn reserve_group_request(&self, descriptor: &GroupRequest, term: u64) -> Result<(), String> {
        let key = self.group_request_key(&descriptor.request);
        let lk = self.lease_key();
        let bytes = serde_json::to_vec(descriptor).map_err(|e| e.to_string())?;
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let Some(lease) = Self::read_lease(&trx, &lk).await? else { return Err("controller lost lease".into()) };
            if lease.holder != self.holder || lease.term != term || lease.until_ms <= now_ms() {
                return Err("controller lost lease".into());
            }
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
            let now = now_ms();
            let old = match Self::read_lease(&trx, &key).await {
                Ok(v) => v,
                Err(e) => return Err(e),
            };
            if old.as_ref().is_some_and(|l| l.holder != self.holder && l.until_ms > now) {
                return Ok(None);
            }
            let term = old.as_ref().map_or(1, |l| if l.holder == self.holder { l.term } else { l.term + 1 });
            let lease = Lease { holder: self.holder.clone(), term, until_ms: now + self.lease_ms };
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
        let Some(bytes) = self.store.meta.get(self.lease_key()).await.map_err(|e| e.to_string())? else { return Ok(None) };
        let lease: Lease = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        Ok((lease.holder == self.holder && lease.until_ms > now_ms()).then_some(lease))
    }

    /// Every snapshot chunk key (`controller/chunk/<hash>/<i>`), of any snapshot.
    pub fn chunk_space(&self) -> foundationdb::tuple::Subspace {
        self.store.meta.keys.root.subspace(&("controller", "chunk"))
    }

    /// The head and its chunks are read in one transaction: a concurrent save, which
    /// clears the previous snapshot's chunks, cannot interleave.
    pub async fn load(&self) -> Result<Option<Vec<u8>>, String> {
        let sk = self.state_key();
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            match self.load_in(&trx, &sk).await {
                Ok(v) => return v,
                Err(e) => trx = trx.on_error(e).await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller state read unresolved".into())
    }

    async fn load_in(&self, trx: &Transaction, sk: &[u8]) -> Result<Result<Option<Vec<u8>>, String>, foundationdb::FdbError> {
        let Some(v) = trx.get(sk, false).await? else { return Ok(Ok(None)) };
        let head: SnapshotHead = match serde_json::from_slice(&v) { Ok(h) => h, Err(e) => return Ok(Err(e.to_string())) };
        if head.len > MAX_SNAPSHOT || head.chunks as usize != head.len.div_ceil(CHUNK_SIZE) {
            return Ok(Err("invalid controller snapshot head".into()));
        }
        let mut bytes = Vec::with_capacity(head.len);
        for index in 0..head.chunks {
            let Some(chunk) = trx.get(&self.chunk_key(&head.hash, index), false).await? else {
                return Ok(Err(format!("controller snapshot chunk {index} missing")));
            };
            bytes.extend_from_slice(&chunk);
        }
        if bytes.len() != head.len || hex::encode(sha256(&bytes)) != head.hash {
            return Ok(Err("controller snapshot hash mismatch".into()));
        }
        Ok(Ok(Some(bytes)))
    }

    pub async fn save(&self, bytes: &[u8], term: u64) -> Result<(), String> {
        if bytes.len() > MAX_SNAPSHOT { return Err("controller snapshot exceeds 8 MiB; shard job history before accepting more work".into()) }
        let hash = hex::encode(sha256(bytes));
        let head = SnapshotHead { hash: hash.clone(), chunks: bytes.len().div_ceil(CHUNK_SIZE) as u32, len: bytes.len() };
        let value = serde_json::to_vec(&head).map_err(|e| e.to_string())?;
        let db = &self.store.meta.db;
        let lk = self.lease_key();
        let sk = self.state_key();
        let mut trx = db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let Some(lease) = Self::read_lease(&trx, &lk).await? else { return Err("controller lost lease".into()) };
            if lease.holder != self.holder || lease.term != term || lease.until_ms <= now_ms() {
                return Err("controller lost lease".into());
            }
            // The head swap drops every other snapshot's chunks in the same transaction,
            // so superseded snapshots (and chunks orphaned by older versions) do not pile up.
            if !cfg!(feature = "mutate-keep-old-snapshot-chunks") {
                let (begin, end) = self.chunk_space().range();
                trx.clear_range(&begin, &end);
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
        let lk = self.lease_key();
        let db = &self.store.meta.db;
        let mut trx = db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let Some(lease) = Self::read_lease(&trx, &lk).await? else { return Err("controller lost lease".into()) };
            if lease.holder != self.holder || lease.term != term || lease.until_ms <= now_ms() {
                return Err("controller lost lease".into());
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
            if missing.is_empty() { return Ok(epochs) }
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
    pub async fn record_receipt(&self, worker: &WorkspaceId, request: &[u8], receipt: &Receipt, term: u64) -> Result<Receipt, String> {
        let lk = self.lease_key();
        let rk = self.store.meta.keys.job_receipt(worker, request);
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let Some(lease) = Self::read_lease(&trx, &lk).await? else { return Err("controller lost lease".into()) };
            if lease.holder != self.holder || lease.term != term || lease.until_ms <= now_ms() {
                return Err("controller lost lease".into());
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
}
