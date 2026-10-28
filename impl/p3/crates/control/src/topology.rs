//! W4-rest design 2: a dynamic controller shard topology (docs/w4-rest-log.md).
//!
//! A legacy deployment keeps its 4-byte `controller/topology` (the fixed shard count)
//! and is never touched by this module. A dynamic deployment stores a versioned
//! [`TopologyRecord`] there instead: a topology epoch, the member shards (each
//! `Active` or `Retired`) and a fixed bucket count [`NB`]. A target's bucket is
//! `sha256(name) mod NB`; `controller/bucket/<b>` holds `{shard, epoch, moving}`.
//!
//! Claims, work routes and validation routes store a bucket (`0xB0 ‖ u16`), never a
//! shard, so a move rewrites only bucket records and the moved shard-local state.
//! Every shard-local durable write keyed by a bucket reads the bucket record in its
//! transaction and requires `shard = self` and no move in progress (the shard-epoch
//! fence beside W4's lease/term fence).
//!
//! A move runs in three fenced, idempotent steps keyed by its move record:
//! **Begin** (the authority, [`begin_move`]) marks the buckets `moving`;
//! **Export** (the source leader, [`Durable::export_commit`]) removes the buckets'
//! entries from the source snapshot, writes them to the move's handoff record, moves
//! the source's validation-index entries and flips each bucket to the destination,
//! still `moving`; **Import** (the destination leader, [`Durable::import_commit`])
//! merges the handoff into the destination snapshot, deletes it and clears `moving`.
//! At every commit version a job is in exactly one of the source snapshot, the handoff
//! or the destination snapshot.

use std::collections::BTreeMap;

use foundationdb::options::StreamingMode;
use foundationdb::tuple::{Bytes, Subspace};
use foundationdb::{KeySelector, RangeOption, Transaction};
use paralean_store::id::sha256;
use paralean_store::pce::Pce;
use paralean_store::{Name, Store, WorkspaceId};
use serde::{Deserialize, Serialize};

use crate::durable::{Durable, HeadWrite, PollReplay, SnapshotHead, CHUNK_SIZE, MAX_SHARD_SNAPSHOT};

/// Buckets of a dynamic deployment.
pub const NB: u16 = 256;
/// First byte of a bucket-valued claim or route; no legacy value starts a 3-byte value
/// with it (legacy claims and validation routes are 4 bytes, P5's claim is 7).
pub const BUCKET_TAG: u8 = 0xB0;
/// A handoff and the source's new snapshot (with the moved index entries and poll
/// rows) must fit one FDB transaction together.
pub const MOVE_LIMIT: usize = 9 * 1024 * 1024;
/// The lease value of a retired shard: not a lease record, so every fenced write and
/// every acquisition of that shard fails.
pub const RETIRED_LEASE: &[u8] = b"w4r-retired-shard";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MemberState { Active, Retired }

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TopologyRecord {
    pub version: u32,
    pub epoch: u64,
    pub nb: u16,
    pub members: BTreeMap<u32, MemberState>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BucketRecord {
    pub shard: u32,
    pub epoch: u64,
    pub moving: Option<u64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MoveState { Prepared, Exported, Done, Aborted }

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MoveRecord {
    pub id: u64,
    pub buckets: Vec<u16>,
    pub from: u32,
    pub to: u32,
    pub state: MoveState,
    #[serde(default)]
    pub reason: String,
    #[serde(default)]
    pub handoff_len: usize,
}

/// The value of `controller/topology`.
pub enum Topology { Fixed(u32), Dynamic(TopologyRecord) }

pub fn parse_topology(value: &[u8]) -> Result<Topology, String> {
    if value.len() == 4 { return Ok(Topology::Fixed(u32::from_be_bytes(value.try_into().unwrap()))) }
    let record: TopologyRecord = serde_json::from_slice(value).map_err(|_| "invalid controller topology record")?;
    if record.version != 1 || record.nb != NB { return Err("unsupported controller topology record".into()) }
    Ok(Topology::Dynamic(record))
}

pub fn encode_bucket(bucket: u16) -> [u8; 3] {
    let [hi, lo] = bucket.to_be_bytes();
    [BUCKET_TAG, hi, lo]
}

pub fn decode_bucket(value: &[u8]) -> Option<u16> {
    if value.len() != 3 || value[0] != BUCKET_TAG { return None }
    let bucket = u16::from_be_bytes([value[1], value[2]]);
    (bucket < NB).then_some(bucket)
}

/// `sha256(name) mod NB`, from the hash's first eight bytes as W4's shard hash.
pub fn name_bucket(name: &Name) -> u16 {
    let hash = sha256(&name.to_pce());
    (u64::from_be_bytes(hash[0..8].try_into().unwrap()) % NB as u64) as u16
}

/// The bucket of a target-free validation: its (workspace, request) identity (W2-32).
pub fn validation_bucket(worker: &WorkspaceId, request: &[u8]) -> u16 {
    let mut id = worker.0.to_vec();
    id.extend_from_slice(request);
    let hash = sha256(&id);
    (u64::from_be_bytes(hash[0..8].try_into().unwrap()) % NB as u64) as u16
}

/// The bucket of a group from its names' claims: every claimed name must name the same
/// bucket; with none claimed, the bucket of the first name in sorted order.
pub fn group_bucket(names: &[Name], claims: &[Option<Vec<u8>>]) -> Result<u16, String> {
    let mut found = None;
    for (name, claim) in names.iter().zip(claims) {
        let Some(value) = claim else { continue };
        let bucket = decode_bucket(value).ok_or_else(|| format!("target {name} is not claimed by a controller bucket"))?;
        if found.is_some_and(|f| f != bucket) { return Err("group spans controller buckets".into()) }
        found = Some(bucket);
    }
    if let Some(bucket) = found { return Ok(bucket) }
    names.iter().min_by_key(|n| n.to_string()).map(name_bucket).ok_or_else(|| "empty target group".into())
}

// ------------------------------------------------------------------ keys

fn root(store: &Store) -> &Subspace { &store.meta.keys.root }
pub fn topology_key(store: &Store) -> Vec<u8> { root(store).pack(&("controller", "topology")) }
pub fn bucket_key(store: &Store, bucket: u16) -> Vec<u8> { root(store).pack(&("controller", "bucket", bucket as u64)) }
fn bucket_subspace(store: &Store) -> Subspace { root(store).subspace(&("controller", "bucket")) }
pub fn move_key(store: &Store, id: u64) -> Vec<u8> { root(store).pack(&("controller", "move", id)) }
fn active_key(store: &Store, id: u64) -> Vec<u8> { root(store).pack(&("controller", "moves-active", id)) }
fn active_subspace(store: &Store) -> Subspace { root(store).subspace(&("controller", "moves-active")) }
pub fn handoff_subspace(store: &Store, id: u64) -> Subspace { root(store).subspace(&("controller", "handoff", id)) }
fn handoff_head_key(store: &Store, id: u64) -> Vec<u8> { root(store).pack(&("controller", "handoff", id, "head")) }
fn handoff_chunk_key(store: &Store, id: u64, index: u32) -> Vec<u8> {
    root(store).pack(&("controller", "handoff", id, "chunk", index as u64))
}
pub fn shard_lease_key(store: &Store, shard: u32) -> Vec<u8> { root(store).pack(&("controller", "shard", shard as u64, "lease")) }
fn shard_state_key(store: &Store, shard: u32) -> Vec<u8> { root(store).pack(&("controller", "shard", shard as u64, "state")) }
pub(crate) fn work_replay_key_of(store: &Store, shard: u32, request: &str) -> Vec<u8> {
    if let Some(g) = crate::replay::identity_generation(request) {
        return crate::replay::replay_row_key_of(store, shard, g, "work", request);
    }
    root(store).pack(&("controller", "shard", shard as u64, "history-work", Bytes::from(&sha256(request.as_bytes())[..])))
}
pub(crate) fn poll_replay_key_of(store: &Store, shard: u32, token: &str) -> Vec<u8> {
    if let Some(g) = crate::replay::identity_generation(token) {
        return crate::replay::replay_row_key_of(store, shard, g, "poll", token);
    }
    root(store).pack(&("controller", "shard", shard as u64, "history-poll", Bytes::from(&sha256(token.as_bytes())[..])))
}
/// A dynamic shard's validation index is keyed by bucket first, so a move reads and
/// moves exactly the entries of its buckets.
pub(crate) fn index_bucket_subspace(store: &Store, shard: u32, bucket: u16) -> Subspace {
    root(store).subspace(&("controller", "shard", shard as u64, "validation-job", bucket as u64))
}
pub(crate) fn index_key_of(store: &Store, shard: u32, bucket: u16, worker: &WorkspaceId, request: &[u8]) -> Vec<u8> {
    index_bucket_subspace(store, shard, bucket).pack(&(Bytes::from(&worker.0[..]), Bytes::from(request)))
}

// ------------------------------------------------------------------ reads

fn json<T: Serialize>(value: &T) -> Result<Vec<u8>, String> { serde_json::to_vec(value).map_err(|e| e.to_string()) }

pub(crate) async fn read_range(trx: &Transaction, sub: &Subspace) -> Result<Vec<(Vec<u8>, Vec<u8>)>, String> {
    let (begin, end) = sub.range();
    let mut out: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    let mut iteration = 1;
    loop {
        let start = match out.last() {
            Some((key, _)) => KeySelector::first_greater_than(key.clone()),
            None => KeySelector::first_greater_or_equal(begin.clone()),
        };
        let opt = RangeOption { mode: StreamingMode::WantAll, ..RangeOption::from((start, KeySelector::first_greater_or_equal(end.clone()))) };
        let page = trx.get_range(&opt, iteration, false).await.map_err(|e| e.to_string())?;
        let more = page.more();
        let before = out.len();
        out.extend(page.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())));
        if !more || out.len() == before { return Ok(out) }
        iteration += 1;
    }
}

pub(crate) async fn topology_in(trx: &Transaction, store: &Store) -> Result<TopologyRecord, String> {
    match trx.get(&topology_key(store), false).await.map_err(|e| e.to_string())? {
        None => Err("dynamic controller topology is not initialized (topology init)".into()),
        Some(v) => match parse_topology(&v)? {
            Topology::Fixed(_) => Err("deployment uses a fixed controller topology".into()),
            Topology::Dynamic(record) => Ok(record),
        },
    }
}

pub(crate) async fn bucket_in(trx: &Transaction, store: &Store, bucket: u16) -> Result<BucketRecord, String> {
    if bucket >= NB { return Err("bucket outside the topology".into()) }
    let value = trx.get(&bucket_key(store, bucket), false).await.map_err(|e| e.to_string())?
        .ok_or("controller bucket record missing")?;
    serde_json::from_slice(&value).map_err(|e| e.to_string())
}

pub(crate) async fn move_in(trx: &Transaction, store: &Store, id: u64) -> Result<Option<MoveRecord>, String> {
    trx.get(&move_key(store, id), false).await.map_err(|e| e.to_string())?
        .map(|v| serde_json::from_slice(&v).map_err(|e| e.to_string())).transpose()
}

pub async fn read_topology(store: &Store) -> Result<TopologyRecord, String> {
    let trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    topology_in(&trx, store).await
}

pub async fn read_bucket(store: &Store, bucket: u16) -> Result<BucketRecord, String> {
    let trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    bucket_in(&trx, store, bucket).await
}

pub async fn read_buckets(store: &Store) -> Result<Vec<BucketRecord>, String> {
    let trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    buckets_in(&trx, store).await
}

async fn buckets_in(trx: &Transaction, store: &Store) -> Result<Vec<BucketRecord>, String> {
    let sub = bucket_subspace(store);
    let rows = read_range(trx, &sub).await?;
    let mut out = vec![None; NB as usize];
    for (key, value) in rows {
        let (bucket,): (u64,) = sub.unpack(&key).map_err(|e| e.to_string())?;
        let slot = out.get_mut(bucket as usize).ok_or("bucket outside the topology")?;
        *slot = Some(serde_json::from_slice::<BucketRecord>(&value).map_err(|e| e.to_string())?);
    }
    out.into_iter().map(|b| b.ok_or_else(|| "controller bucket record missing".to_string())).collect()
}

pub async fn read_move(store: &Store, id: u64) -> Result<Option<MoveRecord>, String> {
    let trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    move_in(&trx, store, id).await
}

/// Moves not yet `Done` or `Aborted`.
pub async fn active_moves(store: &Store) -> Result<Vec<MoveRecord>, String> {
    let trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    let sub = active_subspace(store);
    let mut out = Vec::new();
    for (key, _) in read_range(&trx, &sub).await? {
        let (id,): (u64,) = sub.unpack(&key).map_err(|e| e.to_string())?;
        if let Some(m) = move_in(&trx, store, id).await? { out.push(m) }
    }
    Ok(out)
}

/// Topology, bucket ownership and active moves, for operators.
pub async fn status(store: &Store) -> Result<serde_json::Value, String> {
    let trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    let topology = topology_in(&trx, store).await?;
    let buckets = buckets_in(&trx, store).await?;
    let mut owned: BTreeMap<u32, Vec<u16>> = BTreeMap::new();
    let mut moving = Vec::new();
    for (b, record) in buckets.iter().enumerate() {
        owned.entry(record.shard).or_default().push(b as u16);
        if let Some(id) = record.moving { moving.push(serde_json::json!({"bucket": b, "move": id, "shard": record.shard})) }
    }
    drop(trx);
    let moves = active_moves(store).await?;
    Ok(serde_json::json!({
        "epoch": topology.epoch, "nb": topology.nb,
        "members": topology.members.iter().map(|(n, s)| serde_json::json!({"shard": n, "state": format!("{s:?}"),
            "buckets": owned.get(n).map_or(0, Vec::len)})).collect::<Vec<_>>(),
        "owned": owned, "moving": moving, "active_moves": moves,
    }))
}

// ------------------------------------------------------------------ authority steps

/// Make a fresh deployment dynamic: `shards` active members, buckets in contiguous
/// ranges. Refuses a deployment that has a topology or legacy controller state.
pub async fn init_dynamic(store: &Store, shards: u32) -> Result<TopologyRecord, String> {
    if shards == 0 || shards > NB as u32 { return Err("a dynamic topology needs 1..=256 shards".into()) }
    let record = TopologyRecord { version: 1, epoch: 1, nb: NB, members: (0..shards).map(|n| (n, MemberState::Active)).collect() };
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        if let Some(v) = trx.get(&topology_key(store), false).await.map_err(|e| e.to_string())? {
            return match parse_topology(&v)? {
                Topology::Dynamic(existing) if existing.members == record.members && existing.epoch == 1 => Ok(existing),
                _ => Err("controller topology already initialized".into()),
            };
        }
        for kind in ["state", "lease"] {
            if trx.get(&root(store).pack(&("controller", kind)), false).await.map_err(|e| e.to_string())?.is_some() {
                return Err("legacy controller deployment requires offline migration".into());
            }
        }
        trx.set(&topology_key(store), &json(&record)?);
        for b in 0..NB {
            let shard = (b as u32 * shards) / NB as u32;
            trx.set(&bucket_key(store, b), &json(&BucketRecord { shard, epoch: 1, moving: None })?);
        }
        // Fence pre-W4 binaries as the fixed topology does.
        trx.set(&root(store).pack(&("controller", "lease")), b"w4-sharded-controller");
        match trx.commit().await {
            Ok(_) => return Ok(record),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("topology init outcome unresolved".into())
}

/// Add shard `shard` (or the next unused number) as `Active`. It owns nothing until a
/// move gives it buckets. Idempotent for an existing active member.
pub async fn add_shard(store: &Store, shard: Option<u32>) -> Result<u32, String> {
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        let mut record = topology_in(&trx, store).await?;
        let n = shard.unwrap_or_else(|| record.members.keys().next_back().map_or(0, |m| m + 1));
        match record.members.get(&n) {
            Some(MemberState::Active) => return Ok(n),
            Some(MemberState::Retired) => return Err(format!("shard {n} is retired; shard numbers are never reused")),
            None => {}
        }
        record.members.insert(n, MemberState::Active);
        record.epoch += 1;
        trx.set(&topology_key(store), &json(&record)?);
        match trx.commit().await {
            Ok(_) => return Ok(n),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("add shard outcome unresolved".into())
}

/// Retire `shard`: it must own no bucket and take part in no active move. Its lease
/// becomes [`RETIRED_LEASE`], which fails every fenced write of a leader it still has.
/// Its replay rows stay readable (cross-shard replay lookups read every member).
pub async fn remove_shard(store: &Store, shard: u32) -> Result<(), String> {
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        let mut record = topology_in(&trx, store).await?;
        match record.members.get(&shard) {
            None => return Err(format!("shard {shard} is not in the topology")),
            Some(MemberState::Retired) => return Ok(()),
            Some(MemberState::Active) => {}
        }
        if !cfg!(feature = "mutate-shard-remove-owning") {
            let buckets = buckets_in(&trx, store).await?;
            if let Some(b) = buckets.iter().position(|r| r.shard == shard) {
                return Err(format!("shard {shard} still owns bucket {b}"));
            }
            for (key, _) in read_range(&trx, &active_subspace(store)).await? {
                let (id,): (u64,) = active_subspace(store).unpack(&key).map_err(|e| e.to_string())?;
                if move_in(&trx, store, id).await?.is_some_and(|m| m.from == shard || m.to == shard) {
                    return Err(format!("shard {shard} takes part in move {id}"));
                }
            }
        }
        record.members.insert(shard, MemberState::Retired);
        record.epoch += 1;
        trx.set(&topology_key(store), &json(&record)?);
        if !cfg!(feature = "mutate-shard-retired-lease-live") {
            trx.set(&shard_lease_key(store, shard), RETIRED_LEASE);
        }
        match trx.commit().await {
            Ok(_) => return Ok(()),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("remove shard outcome unresolved".into())
}

/// Begin move `id` of `buckets` from `from` to `to`: every bucket must be owned by
/// `from` with no move in progress. Idempotent for the same move.
pub async fn begin_move(store: &Store, id: u64, buckets: &[u16], from: u32, to: u32) -> Result<MoveRecord, String> {
    let mut buckets = buckets.to_vec();
    buckets.sort_unstable();
    buckets.dedup();
    if buckets.is_empty() || buckets.iter().any(|b| *b >= NB) { return Err("a move needs buckets below 256".into()) }
    if from == to { return Err("a move needs two different shards".into()) }
    let record = MoveRecord { id, buckets: buckets.clone(), from, to, state: MoveState::Prepared, reason: String::new(), handoff_len: 0 };
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        let mut topology = topology_in(&trx, store).await?;
        if let Some(existing) = move_in(&trx, store, id).await? {
            if existing.buckets == buckets && existing.from == from && existing.to == to { return Ok(existing) }
            return Err(format!("move {id} already exists for other buckets or shards"));
        }
        for shard in [from, to] {
            if topology.members.get(&shard) != Some(&MemberState::Active) { return Err(format!("shard {shard} is not active")) }
        }
        let mut updated = Vec::with_capacity(buckets.len());
        for b in &buckets {
            let mut current = bucket_in(&trx, store, *b).await?;
            if current.shard != from { return Err(format!("bucket {b} is not owned by shard {from}")) }
            if let Some(other) = current.moving { return Err(format!("bucket {b} is already moving (move {other})")) }
            current.moving = Some(id);
            updated.push((*b, current));
        }
        for (b, current) in &updated { trx.set(&bucket_key(store, *b), &json(current)?) }
        trx.set(&move_key(store, id), &json(&record)?);
        trx.set(&active_key(store, id), b"");
        topology.epoch += 1;
        trx.set(&topology_key(store), &json(&topology)?);
        match trx.commit().await {
            Ok(_) => return Ok(record),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("move begin outcome unresolved".into())
}

/// Abort a move that has not been exported: its buckets stay with the source.
pub async fn abort_move(store: &Store, id: u64, reason: &str) -> Result<MoveRecord, String> {
    let mut trx = store.meta.db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        let mut record = move_in(&trx, store, id).await?.ok_or("no such move")?;
        match record.state {
            MoveState::Prepared => {}
            MoveState::Aborted => return Ok(record),
            other => return Err(format!("move {id} is {other:?}; only a prepared move can be aborted")),
        }
        abort_in(&trx, store, &mut record, reason).await?;
        match trx.commit().await {
            Ok(_) => return Ok(record),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("move abort outcome unresolved".into())
}

async fn abort_in(trx: &Transaction, store: &Store, record: &mut MoveRecord, reason: &str) -> Result<(), String> {
    for b in &record.buckets {
        let mut current = bucket_in(trx, store, *b).await?;
        if current.moving == Some(record.id) && current.shard == record.from {
            current.moving = None;
            trx.set(&bucket_key(store, *b), &json(&current)?);
        }
    }
    record.state = MoveState::Aborted;
    record.reason = reason.into();
    trx.set(&move_key(store, record.id), &json(record)?);
    trx.clear(&active_key(store, record.id));
    Ok(())
}

// ------------------------------------------------------------------ shard steps

/// What an export or import commit did.
#[derive(Debug, PartialEq, Eq)]
pub enum MoveOutcome {
    Committed,
    /// The move record is already past this step (an earlier leader or attempt did it).
    AlreadyDone,
    /// The export does not fit one transaction; the source aborted the move.
    TooLarge(String),
}

#[derive(Serialize, Deserialize)]
struct HandoffHead { hash: String, chunks: u32, len: usize }

impl Durable {
    pub fn new_dynamic(store: Store, lease: std::time::Duration, shard: u32) -> Self {
        let mut d = Self::new_shard(store, lease, 0, 1);
        d.shard = shard;
        d.shards = 0;
        d.dynamic = true;
        d
    }

    /// Bytes an export may write in one transaction; tests lower it.
    pub fn set_move_limit(&self, bytes: usize) { self.move_limit.store(bytes, std::sync::atomic::Ordering::SeqCst) }

    pub(crate) async fn dynamic_topology_in(&self, trx: &Transaction) -> Result<TopologyRecord, String> {
        let record = topology_in(trx, &self.store).await?;
        match record.members.get(&self.shard) {
            Some(MemberState::Active) => Ok(record),
            Some(MemberState::Retired) => Err("controller shard retired".into()),
            None => Err("controller shard is not in the topology".into()),
        }
    }

    /// The shard-epoch fence: `bucket` is this shard's and no move is in progress.
    pub(crate) async fn require_bucket(&self, trx: &Transaction, bucket: u16, skip: bool) -> Result<BucketRecord, String> {
        let record = bucket_in(trx, &self.store, bucket).await?;
        if skip { return Ok(record) }
        if record.shard != self.shard { return Err("bucket belongs to another controller shard".into()) }
        if record.moving.is_some() { return Err("bucket moving".into()) }
        Ok(record)
    }

    /// J2's fence: as [`Self::require_bucket`], except that the source of a prepared
    /// (not yet exported) move still records the receipts of validations it drains.
    async fn require_bucket_for_receipt(&self, trx: &Transaction, bucket: u16) -> Result<(), String> {
        let record = bucket_in(trx, &self.store, bucket).await?;
        if cfg!(feature = "mutate-shard-no-fence-receipt") { return Ok(()) }
        if record.shard != self.shard { return Err("bucket belongs to another controller shard".into()) }
        if let Some(id) = record.moving {
            let m = move_in(trx, &self.store, id).await?.ok_or("moving bucket without move record")?;
            if !(m.state == MoveState::Prepared && m.from == self.shard) { return Err("bucket moving".into()) }
        }
        Ok(())
    }

    /// The bucket of a claim value at `key`, or None if unclaimed.
    async fn claim_bucket_in(trx: &Transaction, key: &[u8], name: &Name) -> Result<Option<u16>, String> {
        match trx.get(key, false).await.map_err(|e| e.to_string())? {
            None => Ok(None),
            Some(v) => decode_bucket(&v).map(Some).ok_or_else(|| format!("target {name} belongs to another scheduler")),
        }
    }

    async fn names_bucket_in(&self, trx: &Transaction, names: &[Name]) -> Result<(u16, Vec<Name>), String> {
        let mut claims = Vec::with_capacity(names.len());
        for name in names {
            claims.push(trx.get(&crate::durable::target_claim_key(&self.store, name), false).await.map_err(|e| e.to_string())?.map(|v| v.to_vec()));
        }
        let bucket = group_bucket(names, &claims)?;
        let missing = names.iter().zip(&claims).filter(|(_, c)| c.is_none()).map(|(n, _)| n.clone()).collect();
        Ok((bucket, missing))
    }

    async fn owner_of(&self, bucket: u16) -> Result<u32, String> {
        Ok(read_bucket(&self.store, bucket).await?.shard)
    }

    /// Owner shard of `name`'s bucket (its claim's, else its hash bucket).
    pub(crate) async fn dyn_shard_for_target(&self, name: &Name, mapped_only: bool) -> Result<Option<u32>, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        let claim = Self::claim_bucket_in(&trx, &crate::durable::target_claim_key(&self.store, name), name).await?;
        let bucket = match claim { Some(b) => b, None if mapped_only => return Ok(None), None => name_bucket(name) };
        Ok(Some(self.owner_of(bucket).await?))
    }

    pub async fn bucket_for_names(&self, names: &[Name]) -> Result<u16, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        Ok(self.names_bucket_in(&trx, names).await?.0)
    }

    /// The bucket a work request's route names, if routed.
    pub async fn work_bucket(&self, request: &str) -> Result<Option<u16>, String> {
        match self.store.meta.get(self.work_shard_key(request)).await.map_err(|e| e.to_string())? {
            None => Ok(None),
            Some(v) => decode_bucket(v.get(..3).filter(|_| v.len() == 35).ok_or("invalid work route")?).map(Some).ok_or_else(|| "invalid work route".into()),
        }
    }

    /// The bucket a validation route names, if routed.
    pub async fn validation_route_bucket(&self, worker: &WorkspaceId, request: &[u8]) -> Result<Option<u16>, String> {
        match self.store.meta.get(self.validation_shard_key(worker, request)).await.map_err(|e| e.to_string())? {
            None => Ok(None),
            Some(v) => decode_bucket(&v).map(Some).ok_or_else(|| "invalid validation route".into()),
        }
    }

    pub(crate) async fn dyn_shard_for_work(&self, request: &str) -> Result<Option<u32>, String> {
        match self.work_bucket(request).await? { Some(b) => Ok(Some(self.owner_of(b).await?)), None => Ok(None) }
    }

    pub(crate) async fn dyn_shard_for_validation(&self, worker: &WorkspaceId, request: &[u8]) -> Result<Option<u32>, String> {
        match self.validation_route_bucket(worker, request).await? { Some(b) => Ok(Some(self.owner_of(b).await?)), None => Ok(None) }
    }

    /// Reserve a work route `bucket ‖ sha256(target)` and claim the target's bucket.
    pub(crate) async fn dyn_reserve_work(&self, request: &str, target: &Name, term: u64) -> Result<u16, String> {
        let key = self.work_shard_key(request);
        let target_key = crate::durable::target_claim_key(&self.store, target);
        let target_hash = sha256(&target.to_pce());
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let claimed = Self::claim_bucket_in(&trx, &target_key, target).await?;
            let route = trx.get(&key, false).await.map_err(|e| e.to_string())?;
            let bucket = match (&route, claimed) {
                (Some(v), _) => {
                    let b = decode_bucket(v.get(..3).filter(|_| v.len() == 35).ok_or("invalid work route")?).ok_or("invalid work route")?;
                    if v[3..] != target_hash[..] || claimed.is_some_and(|c| c != b) {
                        return Err("work request ID already used for another target or shard".into());
                    }
                    b
                }
                (None, Some(b)) => b,
                (None, None) => name_bucket(target),
            };
            self.require_bucket(&trx, bucket, cfg!(feature = "mutate-shard-no-fence-reserve")).await?;
            let mut write = false;
            if claimed.is_none() { trx.set(&target_key, &encode_bucket(bucket)); write = true }
            if route.is_none() {
                let mut value = encode_bucket(bucket).to_vec();
                value.extend_from_slice(&target_hash);
                trx.set(&key, &value);
                write = true;
            }
            if !write { return Ok(bucket) }
            match trx.commit().await {
                Ok(_) => return Ok(bucket),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("work shard reservation outcome unresolved".into())
    }

    /// The claim part of T4: the group's bucket must be this shard's and not moving;
    /// unclaimed names are claimed for it. Returns whether a claim was written.
    pub(crate) async fn dyn_claim_group_in(&self, trx: &Transaction, names: &[Name]) -> Result<bool, String> {
        let (bucket, missing) = self.names_bucket_in(trx, names).await?;
        self.require_bucket(trx, bucket, cfg!(feature = "mutate-shard-no-fence-assign")).await?;
        for name in &missing { trx.set(&crate::durable::target_claim_key(&self.store, name), &encode_bucket(bucket)) }
        Ok(!missing.is_empty())
    }

    /// The bucket of a validation inside `trx`: its route's, else its targets', else
    /// its (workspace, request) hash for a target-free validation.
    async fn validation_bucket_in(&self, trx: &Transaction, job: &paralean_store::receipt::SignedJob) -> Result<(u16, bool), String> {
        let route_key = self.validation_shard_key(&job.body.worker, &job.body.request);
        if let Some(v) = trx.get(&route_key, false).await.map_err(|e| e.to_string())? {
            return decode_bucket(&v).map(|b| (b, true)).ok_or_else(|| "invalid validation route".into());
        }
        if job.body.targets.is_empty() { return Ok((validation_bucket(&job.body.worker, &job.body.request), false)) }
        let names: Vec<Name> = job.body.targets.iter().map(|t| t.name.clone()).collect();
        Ok((self.names_bucket_in(trx, &names).await?.0, false))
    }

    /// J1 with its route and this shard's bucket-keyed index entry, fenced by the bucket.
    pub(crate) async fn dyn_issue_job(&self, job: &paralean_store::receipt::SignedJob, term: u64) -> Result<paralean_store::receipt::SignedJob, String> {
        use paralean_store::receipt::SignedJob;
        let key = self.store.meta.keys.job_request(&job.body.worker, &job.body.request);
        let receipt_key = self.store.meta.keys.job_receipt(&job.body.worker, &job.body.request);
        let route_key = self.validation_shard_key(&job.body.worker, &job.body.request);
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let (bucket, had_route) = self.validation_bucket_in(&trx, job).await?;
            self.require_bucket(&trx, bucket, cfg!(feature = "mutate-shard-no-fence-issue-job")).await?;
            let index_key = index_key_of(&self.store, self.shard, bucket, &job.body.worker, &job.body.request);
            if !had_route { trx.set(&route_key, &encode_bucket(bucket)) }
            if let Some(bytes) = trx.get(&key, false).await.map_err(|e| e.to_string())? {
                if !had_route { return Err("issued job has no validation shard route".into()) }
                let stored = SignedJob::from_bytes(&bytes).map_err(|e| e.to_string())?;
                // A receipted job needs no recovery entry; an unreceipted one keeps one.
                if trx.get(&index_key, false).await.map_err(|e| e.to_string())?.is_some()
                    || trx.get(&receipt_key, false).await.map_err(|e| e.to_string())?.is_some() { return Ok(stored) }
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

    /// J2, fenced by the route's bucket; clears this shard's recovery index entry.
    pub(crate) async fn dyn_record_receipt(&self, worker: &WorkspaceId, request: &[u8], receipt: &paralean_store::Receipt, term: u64) -> Result<paralean_store::Receipt, String> {
        use paralean_store::Receipt;
        let rk = self.store.meta.keys.job_receipt(worker, request);
        let route_key = self.validation_shard_key(worker, request);
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let route = trx.get(&route_key, false).await.map_err(|e| e.to_string())?
                .ok_or("validation request has no shard route")?;
            let bucket = decode_bucket(&route).ok_or("invalid validation route")?;
            self.require_bucket_for_receipt(&trx, bucket).await?;
            if let Some(bytes) = trx.get(&rk, false).await.map_err(|e| e.to_string())? {
                return Receipt::from_bytes(&bytes).map_err(|e| e.to_string());
            }
            trx.set(&rk, &receipt.to_bytes());
            trx.clear(&index_key_of(&self.store, self.shard, bucket, worker, request));
            match trx.commit().await {
                Ok(_) => return Ok(receipt.clone()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("receipt outcome unresolved".into())
    }

    /// The fence of a recovered dispatch: the route's bucket is this shard's, not moving.
    pub(crate) async fn dyn_recovery_fence(&self, trx: &Transaction, worker: &WorkspaceId, request: &[u8]) -> Result<(), String> {
        let route = trx.get(&self.validation_shard_key(worker, request), false).await.map_err(|e| e.to_string())?
            .ok_or("validation request has no shard route")?;
        let bucket = decode_bucket(&route).ok_or("invalid validation route")?;
        self.require_bucket(trx, bucket, cfg!(feature = "mutate-shard-no-fence-recovery")).await.map(|_| ())
    }

    /// Every member shard ever in the topology, this one first.
    async fn replay_shards(&self, trx: &Transaction) -> Result<Vec<u32>, String> {
        let topology = topology_in(trx, &self.store).await?;
        let mut shards = vec![self.shard];
        if !cfg!(feature = "mutate-shard-no-cross-replay") {
            shards.extend(topology.members.keys().copied().filter(|n| *n != self.shard));
        }
        Ok(shards)
    }

    /// The replay row of `request` written by any shard (point reads per member).
    pub(crate) async fn dyn_work_replay(&self, request: &str) -> Result<Option<crate::durable::WorkReplay>, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for shard in self.replay_shards(&trx).await? {
            if let Some(v) = trx.get(&work_replay_key_of(&self.store, shard, request), false).await.map_err(|e| e.to_string())? {
                let record: crate::durable::WorkReplay = serde_json::from_slice(&v).map_err(|e| e.to_string())?;
                if record.request != request { return Err("work replay hash collision".into()) }
                return Ok(Some(record));
            }
        }
        Ok(None)
    }

    /// Every shard's replay row of poll `token`, this shard's first.
    pub async fn poll_replays(&self, token: &str) -> Result<Vec<PollReplay>, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        let mut out = Vec::new();
        for shard in self.replay_shards(&trx).await? {
            if let Some(v) = trx.get(&poll_replay_key_of(&self.store, shard, token), false).await.map_err(|e| e.to_string())? {
                let record: PollReplay = serde_json::from_slice(&v).map_err(|e| e.to_string())?;
                if record.token != token { return Err("poll replay hash collision".into()) }
                out.push(record);
            }
        }
        Ok(out)
    }

    /// Export step of `mv` in one transaction: under this shard's lease and `term`,
    /// with the head still at `expected` (the generation `snapshot` was computed from),
    /// write the source's new snapshot and the move's poll rows, the handoff, move this
    /// shard's index entries of the buckets to the destination, flip every bucket to the
    /// destination (epoch + 1, still moving) and mark the move `Exported`.
    #[allow(clippy::too_many_arguments)]
    pub async fn export_commit(&self, id: u64, term: u64, expected: Option<u64>, snapshot: &[u8], handoff: &[u8], polls: &[PollReplay]) -> Result<MoveOutcome, String> {
        if snapshot.len() > MAX_SHARD_SNAPSHOT { return Err("controller shard snapshot exceeds 8 MiB".into()) }
        let poll_values = polls.iter().map(json).collect::<Result<Vec<_>, _>>()?;
        let handoff_hash = hex::encode(sha256(handoff));
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let tick = if cfg!(feature = "mutate-shard-export-no-lease") {
                Self::read_tick(&trx, &self.clock_key()).await?
            } else {
                self.require_lease(&trx, term).await?
            };
            let Some(mut record) = move_in(&trx, &self.store, id).await? else { return Err("no such move".into()) };
            if record.state != MoveState::Prepared { return Ok(MoveOutcome::AlreadyDone) }
            if record.from != self.shard { return Err("move is not exported by this shard".into()) }
            let mut buckets = Vec::with_capacity(record.buckets.len());
            for b in &record.buckets {
                let current = bucket_in(&trx, &self.store, *b).await?;
                if current.shard != self.shard || current.moving != Some(id) { return Err("move bucket record changed".into()) }
                buckets.push((*b, current));
            }
            let mut index = Vec::new();
            let mut index_bytes = 0usize;
            for (b, _) in &buckets {
                let sub = index_bucket_subspace(&self.store, self.shard, *b);
                for (key, value) in read_range(&trx, &sub).await? {
                    let suffix = key.get(sub.bytes().len()..).ok_or("invalid validation index key")?.to_vec();
                    index_bytes += key.len() + value.len();
                    index.push((*b, suffix, value));
                }
            }
            let rows: usize = poll_values.iter().map(Vec::len).sum();
            let total = snapshot.len() + handoff.len() + index_bytes + rows;
            let limit = self.move_limit.load(std::sync::atomic::Ordering::SeqCst);
            if total > limit {
                return Ok(MoveOutcome::TooLarge(format!("export of {total} bytes exceeds the {limit}-byte move limit; split the move")));
            }
            // A size bound only: a snapshot read, so the destination's saves do not conflict.
            let dest = trx.get(&shard_state_key(&self.store, record.to), true).await.map_err(|e| e.to_string())?
                .map(|v| serde_json::from_slice::<SnapshotHead>(&v).map_err(|e| e.to_string())).transpose()?;
            if dest.as_ref().map_or(0, |h| h.len) + handoff.len() > MAX_SHARD_SNAPSHOT {
                return Ok(MoveOutcome::TooLarge("destination snapshot would exceed 8 MiB; split the move".into()));
            }
            self.write_poll_rows_in(&trx, polls, &poll_values).await?;
            if let HeadWrite::AlreadyCommitted(_) = self.write_snapshot_in(&trx, snapshot, tick, Some(expected)).await? {
                return Err("controller snapshot generation changed since load".into());
            }
            trx.set(&handoff_head_key(&self.store, id), &json(&HandoffHead { hash: handoff_hash.clone(), chunks: handoff.len().div_ceil(CHUNK_SIZE) as u32, len: handoff.len() })?);
            for (i, chunk) in handoff.chunks(CHUNK_SIZE).enumerate() { trx.set(&handoff_chunk_key(&self.store, id, i as u32), chunk) }
            for (b, suffix, value) in &index {
                let dest = [index_bucket_subspace(&self.store, record.to, *b).bytes(), suffix.as_slice()].concat();
                trx.set(&dest, value);
            }
            for (b, mut current) in buckets {
                let (begin, end) = index_bucket_subspace(&self.store, self.shard, b).range();
                trx.clear_range(&begin, &end);
                current.shard = record.to;
                current.epoch += 1;
                trx.set(&bucket_key(&self.store, b), &json(&current)?);
            }
            record.state = MoveState::Exported;
            record.handoff_len = handoff.len();
            trx.set(&move_key(&self.store, id), &json(&record)?);
            match trx.commit().await {
                Ok(_) => return Ok(MoveOutcome::Committed),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("move export outcome unresolved".into())
    }

    /// The source aborts a prepared move it cannot export (too large), under its lease.
    pub async fn abort_export(&self, id: u64, term: u64, reason: &str) -> Result<(), String> {
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let Some(mut record) = move_in(&trx, &self.store, id).await? else { return Err("no such move".into()) };
            if record.state != MoveState::Prepared || record.from != self.shard { return Ok(()) }
            abort_in(&trx, &self.store, &mut record, reason).await?;
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("move abort outcome unresolved".into())
    }

    /// The handoff of move `id` and its hash, read in one transaction.
    pub async fn read_handoff(&self, id: u64) -> Result<Option<(String, Vec<u8>)>, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        let Some(head) = trx.get(&handoff_head_key(&self.store, id), false).await.map_err(|e| e.to_string())? else { return Ok(None) };
        let head: HandoffHead = serde_json::from_slice(&head).map_err(|e| e.to_string())?;
        let mut bytes = Vec::with_capacity(head.len);
        for i in 0..head.chunks {
            let chunk = trx.get(&handoff_chunk_key(&self.store, id, i), false).await.map_err(|e| e.to_string())?
                .ok_or("handoff chunk missing")?;
            bytes.extend_from_slice(&chunk);
        }
        if bytes.len() != head.len || hex::encode(sha256(&bytes)) != head.hash { return Err("handoff hash mismatch".into()) }
        Ok(Some((head.hash, bytes)))
    }

    /// Import step of move `id` in one transaction: under this shard's lease and `term`,
    /// with the head still at `expected` and the handoff still the one hashed `handoff`,
    /// write `merged` (this shard's snapshot with the handoff merged), delete the handoff,
    /// clear `moving` on every bucket and mark the move `Done`.
    pub async fn import_commit(&self, id: u64, term: u64, expected: Option<u64>, merged: &[u8], handoff: &str) -> Result<MoveOutcome, String> {
        if merged.len() > MAX_SHARD_SNAPSHOT { return Err("controller shard snapshot exceeds 8 MiB".into()) }
        let unchecked = cfg!(feature = "mutate-shard-import-no-state-check");
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let tick = self.require_lease(&trx, term).await?;
            let Some(mut record) = move_in(&trx, &self.store, id).await? else { return Err("no such move".into()) };
            if !unchecked {
                match record.state {
                    MoveState::Exported => {}
                    MoveState::Done => return Ok(MoveOutcome::AlreadyDone),
                    other => return Err(format!("move {id} is {other:?}, not exported")),
                }
            }
            if record.to != self.shard { return Err("move is not imported by this shard".into()) }
            let mut buckets = Vec::with_capacity(record.buckets.len());
            for b in &record.buckets {
                let current = bucket_in(&trx, &self.store, *b).await?;
                if !unchecked && (current.shard != self.shard || current.moving != Some(id)) { return Err("move bucket record changed".into()) }
                buckets.push((*b, current));
            }
            if !unchecked {
                let head = trx.get(&handoff_head_key(&self.store, id), false).await.map_err(|e| e.to_string())?
                    .ok_or("handoff missing")?;
                let head: HandoffHead = serde_json::from_slice(&head).map_err(|e| e.to_string())?;
                if head.hash != handoff { return Err("handoff changed".into()) }
            }
            if let HeadWrite::AlreadyCommitted(_) = self.write_snapshot_in(&trx, merged, tick, Some(expected)).await? {
                return Err("controller snapshot generation changed since load".into());
            }
            if !unchecked {
                let (begin, end) = handoff_subspace(&self.store, id).range();
                trx.clear_range(&begin, &end);
            }
            for (b, mut current) in buckets {
                current.moving = None;
                trx.set(&bucket_key(&self.store, b), &json(&current)?);
            }
            record.state = MoveState::Done;
            trx.set(&move_key(&self.store, id), &json(&record)?);
            trx.clear(&active_key(&self.store, id));
            match trx.commit().await {
                Ok(_) => return Ok(MoveOutcome::Committed),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("move import outcome unresolved".into())
    }
}
