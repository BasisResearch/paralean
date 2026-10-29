//! Physical store GC (docs/w4-rest-log.md, "Design 1: physical store GC").
//!
//! Collects S3 objects that no committed metadata names: staging garbage (payloads of
//! transactions that never committed) and the snapshots and manifests of dead catalogue
//! records. Published protocol content is never collected: every transaction that makes
//! committed metadata name an object writes a reference into a transactional reverse index,
//! and the collector dooms only objects whose index range is empty.
//!
//! Keys (under the deployment root, besides the protocol's own):
//!
//! | Key | Value | Written by |
//! |---|---|---|
//! | `gcref/<kind>/<id>/<H(referrer)>` | the referrer key | every referencing transaction; backfill |
//! | `gcobj/<kind>/<id>` | `GcState` (absent: none) | sweep (Sighted, Doomed), s3-guard (Deleting, Gone), references and revival (clear) |
//! | `gc/clock` | u64 BE, serializable increments | sweep (one tick per pass) |
//! | `gc/dooms` | u64 LE, atomic add | sweep |
//! | `gc/backfilled`, `gc/indexed` | clock | `backfill`, `enable` |
//! | `gc/deadseen/catalog/<c>` | clock first seen dead | sweep |
//! | `gc/retired/catalog/<c>` | clock | dead-record retirement |
//! | `gcaeref/<source>/<event>/<kind>/<id>` | empty | anti-entropy part persistence (index of the `aepending` referrer's objects) |
//!
//! Reference rule (`reference_in`): read `gcobj`; `Doomed`, `Deleting` or `Gone` abort with
//! `GuardFailure::Collected`; `Sighted` is cleared (the grace period restarts); the `gcref`
//! key is written. A doom (`sweep`) reads the object's whole `gcref` range and `gcobj` in one
//! transaction, so a racing reference conflicts with it and exactly one commits first.
//!
//! Revival (`Store::gc_revive`): a writer whose transaction aborted with `Collected` waits for
//! `Gone{clock, nonce}`, re-PUTs the bytes (or verifies them with a GET) *after* reading that
//! state, then clears `gcobj` if it still holds the same `Gone`. Its retried reference then
//! sees no state. Invariant: when `gcobj` is absent or `Sighted`, every object ever
//! acknowledged is present (a delete needs `Doomed`; leaving `Gone` needs a presence check
//! that happened after the delete). Deviation from the design text: the reference
//! transaction itself refuses `Gone` and the separate revival transaction clears it.
//!
//! Collection is off unless `gc/indexed` is set (`backfill`, then `enable`) and a sweep is
//! explicitly requested. Deletion goes through s3-guard's GC principal, which performs the
//! `Doomed → Deleting{nonce} → Gone{clock}` transitions in FDB around the forwarded DELETE.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::time::{Duration, Instant};

use foundationdb::options::MutationType;
use foundationdb::tuple::{Bytes, Subspace};
use foundationdb::Transaction;
use serde::Serialize;

use crate::error::{GuardFailure, Result, StoreError};
use crate::faults::Txn;
use crate::group_chunks::unique_chunks;
use crate::id::{sha256, Id, Kind};
use crate::meta::{get, range, Envelope, Keys, Step};
use crate::objects::*;
use crate::pce::{Dec, Pce};
use crate::receipt::SignedJob;
use crate::s3::{Acked, Payloads};
use crate::store::Store;

// ---------------------------------------------------------------- object state

/// `gcobj/<kind>/<id>`. Absent means "none". The byte layout is shared with s3-guard
/// (`impl/p2/crates/s3-guard/src/main.rs`, `GcState`), which performs the delete transitions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GcState {
    /// Listed by a sweep with no reference at `clock`.
    Sighted { clock: u64 },
    /// No reference for at least the grace period; `size` is the listed object size.
    Doomed { clock: u64, size: u64 },
    /// s3-guard admitted a GC-principal DELETE (`nonce` identifies the attempt).
    Deleting { nonce: [u8; 16], size: u64 },
    /// Garage acknowledged the delete. `nonce` identifies this incarnation's deletion.
    Gone { clock: u64, nonce: [u8; 16] },
}

impl GcState {
    pub fn encode(&self) -> Vec<u8> {
        let mut v = Vec::with_capacity(25);
        match self {
            GcState::Sighted { clock } => {
                v.push(1);
                v.extend_from_slice(&clock.to_be_bytes());
            }
            GcState::Doomed { clock, size } => {
                v.push(2);
                v.extend_from_slice(&clock.to_be_bytes());
                v.extend_from_slice(&size.to_be_bytes());
            }
            GcState::Deleting { nonce, size } => {
                v.push(3);
                v.extend_from_slice(nonce);
                v.extend_from_slice(&size.to_be_bytes());
            }
            GcState::Gone { clock, nonce } => {
                v.push(4);
                v.extend_from_slice(&clock.to_be_bytes());
                v.extend_from_slice(nonce);
            }
        }
        v
    }

    pub fn decode(v: &[u8]) -> Result<GcState> {
        let u = |b: &[u8]| u64::from_be_bytes(b.try_into().expect("length checked"));
        let n = |b: &[u8]| -> [u8; 16] { b.try_into().expect("length checked") };
        Ok(match (v.first(), v.len()) {
            (Some(1), 9) => GcState::Sighted { clock: u(&v[1..9]) },
            (Some(2), 17) => GcState::Doomed { clock: u(&v[1..9]), size: u(&v[9..17]) },
            (Some(3), 25) => GcState::Deleting { nonce: n(&v[1..17]), size: u(&v[17..25]) },
            (Some(4), 25) => GcState::Gone { clock: u(&v[1..9]), nonce: n(&v[9..25]) },
            _ => return Err(StoreError::Invalid("bad store-GC object state".into())),
        })
    }

    /// Doomed, deleting or gone: no new reference or object certificate may name it.
    pub fn retired(&self) -> bool {
        !matches!(self, GcState::Sighted { .. })
    }

    pub fn name(&self) -> &'static str {
        match self {
            GcState::Sighted { .. } => "sighted",
            GcState::Doomed { .. } => "doomed",
            GcState::Deleting { .. } => "deleting",
            GcState::Gone { .. } => "gone",
        }
    }
}

fn u64_be(v: &[u8]) -> Result<u64> {
    Ok(u64::from_be_bytes(v.try_into().map_err(|_| StoreError::Invalid("bad store-GC counter".into()))?))
}

// ---------------------------------------------------------------- keys

impl Keys {
    pub fn gcobj(&self, kind: Kind, id: &Id) -> Vec<u8> {
        self.root.pack(&("gcobj", kind.name(), Bytes::from(&id.0[..])))
    }
    pub fn gcobj_sub(&self) -> Subspace {
        self.sub("gcobj")
    }
    /// `gcref/<kind>/<id>/<SHA-256(referrer)>`, valued with the referrer key itself.
    pub fn gcref(&self, kind: Kind, id: &Id, referrer: &[u8]) -> Vec<u8> {
        self.root.pack(&("gcref", kind.name(), Bytes::from(&id.0[..]), Bytes::from(&sha256(referrer)[..])))
    }
    pub fn gcrefs_of(&self, kind: Kind, id: &Id) -> Subspace {
        self.root.subspace(&("gcref", kind.name(), Bytes::from(&id.0[..])))
    }
    pub fn gc_clock(&self) -> Vec<u8> {
        self.root.pack(&("gc", "clock"))
    }
    pub fn gc_dooms(&self) -> Vec<u8> {
        self.root.pack(&("gc", "dooms"))
    }
    pub fn gc_indexed(&self) -> Vec<u8> {
        self.root.pack(&("gc", "indexed"))
    }
    pub fn gc_backfilled(&self) -> Vec<u8> {
        self.root.pack(&("gc", "backfilled"))
    }
    pub fn gc_retired_catalog(&self, c: &Id) -> Vec<u8> {
        self.root.pack(&("gc", "retired", "catalog", Bytes::from(&c.0[..])))
    }
    pub fn gc_dead_seen(&self, c: &Id) -> Vec<u8> {
        self.root.pack(&("gc", "deadseen", "catalog", Bytes::from(&c.0[..])))
    }
    pub fn gc_aeref(&self, source: &str, event: &[u8], kind: Kind, id: &Id) -> Vec<u8> {
        self.root.pack(&("gcaeref", source, Bytes::from(event), kind.name(), Bytes::from(&id.0[..])))
    }
    pub fn gc_aerefs_of(&self, source: &str, event: &[u8]) -> Subspace {
        self.root.subspace(&("gcaeref", source, Bytes::from(event)))
    }
}

/// The blob an envelope spills to, if any.
pub fn envelope_blob(v: &[u8]) -> Option<Id> {
    match Envelope::decode(v) {
        Ok(Envelope::Blob { blob, .. }) => Some(blob),
        _ => None,
    }
}

fn dedup(objects: &[(Kind, Id)]) -> Vec<(Kind, Id)> {
    objects.iter().copied().collect::<BTreeSet<_>>().into_iter().collect()
}

// ---------------------------------------------------------------- in-transaction rules

async fn states_in(trx: &Transaction, k: &Keys, objects: &[(Kind, Id)]) -> Result<Vec<Option<GcState>>> {
    let reads = objects.iter().map(|(kind, id)| trx.get(&k.gcobj(*kind, id), false));
    let values = futures::future::try_join_all(reads).await?;
    values.into_iter().map(|v| v.map(|v| GcState::decode(&v)).transpose()).collect()
}

/// The object state read in `trx` (in its read-conflict set).
pub async fn state_in(trx: &Transaction, k: &Keys, kind: Kind, id: &Id) -> Result<Option<GcState>> {
    get(trx, &k.gcobj(kind, id)).await?.map(|v| GcState::decode(&v)).transpose()
}

/// A committed reference from `referrer` to each object: refuse a doomed, deleting or gone
/// object (`Collected`), clear `Sighted`, write `gcref`. Point reads (issued concurrently)
/// and point writes only.
pub async fn reference_in(trx: &Transaction, k: &Keys, objects: &[(Kind, Id)], referrer: &[u8]) -> Result<()> {
    let objects = dedup(objects);
    let states = states_in(trx, k, &objects).await?;
    for ((kind, id), state) in objects.iter().zip(states) {
        match state {
            None => {}
            Some(GcState::Sighted { .. }) => trx.clear(&k.gcobj(*kind, id)),
            // Mutation: a reference that treats a gone object as present (no revival).
            Some(GcState::Gone { .. }) if cfg!(feature = "mutate-storegc-ref-no-gone-check") => trx.clear(&k.gcobj(*kind, id)),
            // Mutation: a reference that ignores a doomed or deleting object.
            Some(GcState::Doomed { .. } | GcState::Deleting { .. }) if cfg!(feature = "mutate-storegc-t1-no-doomed-check") => {}
            Some(_) => return Err(GuardFailure::Collected { kind: *kind, id: *id }.into()),
        }
        trx.set(&k.gcref(*kind, id, referrer), referrer);
    }
    Ok(())
}

/// A protective reference (the `aepending` referrer of a pending anti-entropy event): it
/// never aborts. `Sighted` is cleared; a doomed or deleting object keeps its state (the
/// receiver fetches it again after `Gone`, through `Store::put_live`).
pub(crate) async fn protect_in(trx: &Transaction, k: &Keys, objects: &[(Kind, Id)], referrer: &[u8]) -> Result<()> {
    if cfg!(feature = "mutate-storegc-ae-pending-no-ref") {
        return Ok(());
    }
    let objects = dedup(objects);
    let states = states_in(trx, k, &objects).await?;
    for ((kind, id), state) in objects.iter().zip(states) {
        if matches!(state, Some(GcState::Sighted { .. })) {
            trx.clear(&k.gcobj(*kind, id));
        }
        trx.set(&k.gcref(*kind, id, referrer), referrer);
    }
    Ok(())
}

/// Release `referrer`'s references (in the transaction that removes the reason).
pub(crate) fn release_in(trx: &Transaction, k: &Keys, objects: &[(Kind, Id)], referrer: &[u8]) {
    for (kind, id) in objects {
        trx.clear(&k.gcref(*kind, id, referrer));
    }
}

/// Release every reference of a pending anti-entropy event (referrer `aepending/<source>/
/// <event>`), in the transaction that archives, imports or drops the event. The objects are
/// listed by the event's `gcaeref` index, written with its parts.
pub(crate) async fn release_ae_event(trx: &Transaction, k: &Keys, source: &str, event: &[u8]) -> Result<()> {
    let referrer = k.ae_pending(source, event);
    let sub = k.gc_aerefs_of(source, event);
    let (mut begin, end) = sub.range();
    loop {
        let rows = range(trx, begin.clone(), end.clone(), 1024).await?;
        let mut last = None;
        for kv in rows.iter() {
            let (kind, raw): (String, Bytes) = sub.unpack(kv.key()).map_err(|e| StoreError::Invalid(format!("bad gcaeref key: {e}")))?;
            let kind = Kind::from_name(&kind).ok_or_else(|| StoreError::Invalid("bad gcaeref kind".into()))?;
            let id = Id(raw[..].try_into().map_err(|_| StoreError::Invalid("bad gcaeref id".into()))?);
            trx.clear(&k.gcref(kind, &id, &referrer));
            last = Some(kv.key().to_vec());
        }
        // Continue while FDB reports more, never on a short batch.
        match last {
            Some(mut key) if rows.more() => {
                key.push(0);
                begin = key;
            }
            _ => break,
        }
    }
    let (b0, e0) = sub.range();
    trx.clear_range(&b0, &e0);
    Ok(())
}

/// T6's check: an object certificate never vouches for an object about to disappear.
pub(crate) async fn check_live_in(trx: &Transaction, k: &Keys, kind: Kind, id: &Id) -> Result<()> {
    if cfg!(feature = "mutate-storegc-t6-no-doomed-check") {
        return Ok(());
    }
    match state_in(trx, k, kind, id).await? {
        Some(s) if s.retired() => Err(GuardFailure::Collected { kind, id: *id }.into()),
        _ => Ok(()),
    }
}

/// The objects a J1 envelope names: its group, capsule and dependency capsules.
pub fn job_objects(job: &SignedJob) -> Vec<(Kind, Id)> {
    let mut v = vec![(Kind::Group, job.body.group), (Kind::Capsule, job.body.capsule)];
    v.extend(job.body.deps.iter().map(|c| (Kind::Capsule, *c)));
    dedup(&v)
}

/// J1's references (referrer `jobreq/<workspace>/<request>`), in the caller's issuing
/// transaction. Released by the sweep once J2 or J3 exists.
pub async fn job_refs_in(trx: &Transaction, k: &Keys, job: &SignedJob) -> Result<()> {
    reference_in(trx, k, &job_objects(job), &k.job_request(&job.body.worker, &job.body.request)).await
}

/// Before J1: revive any of the job's objects that the store GC deleted and a worker has
/// since uploaded again (a verified GET after reading `Gone`). A doomed or deleting object is
/// left for J1 to refuse (`Collected`); the worker uploads again after `Gone`.
pub async fn revive_job_objects(store: &Store, job: &SignedJob) -> Result<()> {
    for (kind, id) in job_objects(job) {
        if matches!(store.gc_state(kind, &id).await?, Some(GcState::Gone { .. })) {
            match store.gc_revive_now(kind, &id, None).await {
                Ok(_) | Err(StoreError::Missing { .. }) => {}
                Err(e) => return Err(e),
            }
        }
    }
    Ok(())
}

/// The objects a catalogue record names (referrer `catalog/<c>` or `xcatalog/<src>/<c>`):
/// its snapshot and, when the snapshot is known, both export manifests.
/// The objects a batch record names (its referrer is `batch/<id>`): each member's staged
/// marker or tombstone, and each publication's group.
pub fn batch_objects(rec: &crate::batch::BatchRecord) -> Vec<(Kind, Id)> {
    let mut out = Vec::new();
    for e in &rec.entries {
        match e.member {
            crate::batch::BatchMember::Publish { group, .. } => {
                out.push((Kind::StagedMarker, e.object));
                out.push((Kind::Group, group));
            }
            crate::batch::BatchMember::Tombstone { .. } => out.push((Kind::StagedTombstone, e.object)),
        }
    }
    dedup(&out)
}

pub fn record_objects(snapshot_id: Id, snapshot: Option<&Snapshot>) -> Vec<(Kind, Id)> {
    let mut v = vec![(Kind::Snapshot, snapshot_id)];
    if let Some(s) = snapshot.filter(|s| s.id() == snapshot_id) {
        v.push((Kind::Manifest, s.source_root));
        v.push((Kind::Manifest, s.build_receipt));
    }
    v
}

/// The objects a marker key names (T1, T9 and backfill agree): the group, the staged marker
/// copy, the capsules of its revisions, the chunks of its chunk index and every blob the
/// marker and revision envelopes spill to.
pub fn marker_objects(group: Id, marker: Id, capsules: &[Id], chunks: &[Id], values: &[&[u8]]) -> Vec<(Kind, Id)> {
    let mut v = vec![(Kind::Group, group), (Kind::StagedMarker, marker)];
    v.extend(capsules.iter().map(|c| (Kind::Capsule, *c)));
    v.extend(chunks.iter().map(|c| (Kind::Chunk, *c)));
    v.extend(values.iter().filter_map(|value| envelope_blob(value)).map(|b| (Kind::Blob, b)));
    dedup(&v)
}

// ---------------------------------------------------------------- writer side

impl Store {
    /// The object's GC state at a fresh read version.
    pub async fn gc_state(&self, kind: Kind, id: &Id) -> Result<Option<GcState>> {
        Ok(self.meta.get(self.meta.keys.gcobj(kind, id)).await?.map(|v| GcState::decode(&v)).transpose()?)
    }

    /// One revival attempt without waiting: if the object is `Gone`, re-PUT `bytes` (or verify
    /// the present bytes with a GET) after that read, then clear the state if it is still the
    /// same `Gone`. Returns the acknowledgement when the object is live afterwards.
    pub(crate) async fn gc_revive_now(&self, kind: Kind, id: &Id, bytes: Option<&[u8]>) -> Result<Option<Acked>> {
        let gone = match self.gc_state(kind, id).await? {
            None | Some(GcState::Sighted { .. }) => return Ok(Some(Acked::seen(kind, *id))),
            Some(g @ GcState::Gone { .. }) => g,
            Some(_) => return Ok(None),
        };
        let acked = match bytes {
            Some(b) => {
                let a = self.s3.put(kind, b).await?;
                if a.id() != *id {
                    return Err(StoreError::Invalid("revival bytes hash to another ID".into()));
                }
                a
            }
            None => self.s3.get_acked(kind, id).await?.ok_or(StoreError::Missing { kind: "collected object", id: *id })?.0,
        };
        let (key, expect) = (self.meta.keys.gcobj(kind, id), gone.encode());
        let cleared = self.meta.run(Txn::Gc, Box::new(move |trx| {
            let (key, expect) = (key.clone(), expect.clone());
            Box::pin(async move {
                match get(trx, &key).await? {
                    Some(v) if v == expect => {
                        trx.clear(&key);
                        Ok(Step::Commit(true))
                    }
                    None => Ok(Step::Done(true)),
                    Some(_) => Ok(Step::Done(false)),
                }
            })
        })).await?;
        Ok(cleared.then_some(acked))
    }

    /// The revival path: wait (up to `gc_wait`) until the object is not doomed or being
    /// deleted, then revive it if it is gone. `bytes` is the object's preimage when the
    /// writer has it; otherwise the bytes must still be (or again be) present.
    pub async fn gc_revive(&self, kind: Kind, id: &Id, bytes: Option<&[u8]>) -> Result<Acked> {
        let deadline = Instant::now() + self.gc_wait;
        let mut pause = Duration::from_millis(20);
        loop {
            if let Some(acked) = self.gc_revive_now(kind, id, bytes).await? {
                self.faults.count("gc-revived");
                return Ok(acked);
            }
            if Instant::now() >= deadline {
                return Err(GuardFailure::Collected { kind, id: *id }.into());
            }
            tokio::time::sleep(pause).await;
            pause = (pause * 2).min(Duration::from_millis(500));
        }
    }

    /// A writer's payload PUT: a plain PUT, unless the gateway refuses it because the store
    /// GC is deleting the key; then wait for `Gone` and revive with these bytes.
    pub async fn put_payload(&self, kind: Kind, preimage: &[u8]) -> Result<Acked> {
        match self.s3.put(kind, preimage).await {
            Ok(a) => Ok(a),
            Err(e) => {
                let id = Id(sha256(preimage));
                match self.gc_state(kind, &id).await? {
                    Some(s) if s.retired() => self.gc_revive(kind, &id, Some(preimage)).await,
                    _ => Err(e),
                }
            }
        }
    }

    /// A receiver's PUT of fetched bytes: refused while the local copy is doomed or being
    /// deleted (retry later); after `Gone` the PUT is the revival.
    pub async fn put_live(&self, kind: Kind, preimage: &[u8]) -> Result<Acked> {
        let id = Id(sha256(preimage));
        match self.gc_state(kind, &id).await? {
            Some(GcState::Gone { .. }) => self.gc_revive_now(kind, &id, Some(preimage)).await?
                .ok_or_else(|| GuardFailure::Collected { kind, id }.into()),
            Some(s) if s.retired() => Err(GuardFailure::Collected { kind, id }.into()),
            _ => self.s3.put(kind, preimage).await,
        }
    }

    /// Whether `gc/indexed` is set (collection may run).
    pub async fn gc_enabled(&self) -> Result<bool> {
        Ok(self.meta.get(self.meta.keys.gc_indexed()).await?.is_some())
    }

    /// Anti-entropy object service: a doomed, deleting or gone object is `Retired`, never
    /// served, even while its bytes are still present.
    pub async fn ae_fetch(&self, kind: Kind, id: &Id) -> Result<AeFetch> {
        if !cfg!(feature = "mutate-storegc-ae-serves-gone") {
            if let Some(s) = self.gc_state(kind, id).await? {
                if s.retired() {
                    return Ok(AeFetch::Retired);
                }
            }
        }
        Ok(match self.s3.get(kind, id).await? {
            Some(bytes) => AeFetch::Object(bytes),
            None => AeFetch::Missing,
        })
    }
}

/// What the anti-entropy object endpoint answers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AeFetch {
    Object(Vec<u8>),
    Missing,
    /// Collected by this deployment's store GC: the receiver archives the event.
    Retired,
}

// ---------------------------------------------------------------- collector

/// Collector settings. Nothing is collected unless `gc/indexed` is set and `sweep` is called.
#[derive(Clone, Debug)]
pub struct GcConfig {
    /// Sweep passes (clock ticks) an unreferenced object stays `Sighted` before its doom; the
    /// same grace applies to dead catalogue records.
    pub grace: u64,
}

impl Default for GcConfig {
    fn default() -> Self {
        GcConfig { grace: 2 }
    }
}

/// Counters of one GC operation (backfill, sweep or delete pass).
#[derive(Clone, Debug, Default, Serialize)]
pub struct GcReport {
    pub clock: u64,
    /// S3 objects listed and examined by a sweep.
    pub examined: u64,
    pub examined_bytes: u64,
    pub listing_pages: u64,
    pub referenced: u64,
    /// New `Sighted` states (including gone objects that reappeared).
    pub sighted: u64,
    /// `Sighted` states cleared because a reference appeared.
    pub unsighted: u64,
    pub waiting: u64,
    pub doomed: u64,
    pub doomed_bytes: u64,
    /// Doomed or deleting objects seen by a sweep (not yet deleted).
    pub pending_delete: u64,
    /// Objects whose delete s3-guard admitted and Garage acknowledged (`Gone`).
    pub deleted: u64,
    /// Listed bytes of the deleted objects.
    pub reclaimed_bytes: u64,
    pub delete_failures: u64,
    pub referrers: u64,
    pub references_written: u64,
    pub jobs_examined: u64,
    pub jobs_released: u64,
    pub catalogue_examined: u64,
    pub catalogue_dead_seen: u64,
    pub catalogue_retired: u64,
    pub keys_scanned: u64,
    pub transactions: u64,
    pub elapsed_ms: u64,
    pub anomalies: Vec<String>,
}

/// Read-only summary (`gc status`).
#[derive(Clone, Debug, Default, Serialize)]
pub struct GcStatus {
    pub indexed: bool,
    pub backfilled: bool,
    pub clock: u64,
    pub dooms: u64,
    pub states: BTreeMap<String, u64>,
    pub references: u64,
    pub retired_catalogue: u64,
}

async fn read_clock(trx: &Transaction, k: &Keys) -> Result<u64> {
    Ok(match get(trx, &k.gc_clock()).await? {
        Some(v) => u64_be(&v)?,
        None => 0,
    })
}

/// Advance `gc/clock` by a serializable read-modify-write (never an atomic add: the
/// increment must order against the guard's `Gone` writes, which read the clock).
pub async fn tick(store: &Store) -> Result<u64> {
    let k = store.meta.keys.clone();
    store.meta.run(Txn::Gc, Box::new(move |trx| {
        let k = k.clone();
        Box::pin(async move {
            let next = read_clock(trx, &k).await? + 1;
            trx.set(&k.gc_clock(), &next.to_be_bytes());
            Ok(Step::Commit(next))
        })
    })).await
}

fn job_key_parts(k: &Keys, key: &[u8]) -> Option<(crate::id::WorkspaceId, Vec<u8>)> {
    let (_, w, r): (String, Bytes, Bytes) = k.root.unpack(key).ok()?;
    Some((crate::id::WorkspaceId(w[..].try_into().ok()?), r.to_vec()))
}

/// The objects a scanned referrer names, computed outside the write transaction.
struct Referrer {
    key: Vec<u8>,
    value: Vec<u8>,
    objects: Vec<(Kind, Id)>,
    /// For a job: the J2/J3 keys that must be absent. For a pending event: aeref index rows.
    absent: Vec<Vec<u8>>,
    aerefs: Vec<Vec<u8>>,
}

async fn snapshot_of(store: &Store, id: &Id) -> Option<Snapshot> {
    store.s3.get_object::<Snapshot>(Kind::Snapshot, id).await.ok().flatten()
}

async fn chunks_of_group(store: &Store, group: &Id) -> Result<Vec<Id>> {
    if let Some(v) = store.meta.get(store.meta.keys.group_chunks(group)).await? {
        let mut d = Dec::new(&v);
        let list = d.list(|d| Ok((Id::decode(d)?, d.uvarint()?)))?;
        return Ok(list.into_iter().map(|(id, _)| id).collect());
    }
    Ok(match store.s3.get(Kind::Group, group).await? {
        Some(bytes) => unique_chunks(Kind::Group.domain().strip(&bytes)?)?.map(|m| m.into_keys().collect()).unwrap_or_default(),
        None => vec![],
    })
}

async fn marker_referrer(store: &Store, key: Vec<u8>, value: Vec<u8>, report: &mut GcReport) -> Result<Option<Referrer>> {
    let Some(stored) = store.open_value(&value).await? else {
        report.anomalies.push(format!("marker value under {} unreadable", hex::encode(&key)));
        return Ok(None);
    };
    let m = Marker::from_preimage(&stored)?;
    let mut capsules = Vec::new();
    let mut values = vec![value.clone()];
    for rid in &m.revisions {
        if let Some(rv) = store.meta.get(store.meta.keys.revision(rid)).await? {
            if let Some(r) = store.revision(rid).await? {
                capsules.push(r.capsule);
            }
            values.push(rv);
        }
    }
    let chunks = chunks_of_group(store, &m.group).await?;
    let refs: Vec<&[u8]> = values.iter().map(Vec::as_slice).collect();
    let objects = marker_objects(m.group, m.id(), &capsules, &chunks, &refs);
    Ok(Some(Referrer { key, value, objects, absent: vec![], aerefs: vec![] }))
}

/// Write the references of a batch of referrers, re-reading each referrer key in the
/// transaction (a referrer retired meanwhile is skipped).
async fn write_batch(store: &Store, batch: Vec<Referrer>, report: &mut GcReport) -> Result<()> {
    if batch.is_empty() {
        return Ok(());
    }
    let k = store.meta.keys.clone();
    let batch = Arc::new(batch);
    let (written, anomalies): (u64, Vec<String>) = store.meta.run(Txn::Gc, Box::new(move |trx| {
        let (k, batch) = (k.clone(), batch.clone());
        Box::pin(async move {
            let mut written = 0;
            let mut anomalies = Vec::new();
            for r in batch.iter() {
                if get(trx, &r.key).await?.as_deref() != Some(r.value.as_slice()) {
                    continue;
                }
                let mut skip = false;
                for a in &r.absent {
                    skip |= get(trx, a).await?.is_some();
                }
                if skip {
                    continue;
                }
                let states = states_in(trx, &k, &r.objects).await?;
                for ((kind, id), state) in r.objects.iter().zip(states) {
                    match state {
                        Some(GcState::Sighted { .. }) => trx.clear(&k.gcobj(*kind, id)),
                        Some(s) if s.retired() => {
                            anomalies.push(format!("referrer {} names {} {} in state {}", hex::encode(&r.key), kind.name(), id, s.name()));
                        }
                        _ => {}
                    }
                    trx.set(&k.gcref(*kind, id, &r.key), &r.key);
                    written += 1;
                }
                for a in &r.aerefs {
                    trx.set(a, b"");
                }
            }
            Ok(Step::Commit((written, anomalies)))
        })
    })).await?;
    report.transactions += 1;
    report.references_written += written;
    report.anomalies.extend(anomalies);
    Ok(())
}

const BACKFILL_BATCH: usize = 32;

/// Walk every referencing key space and write the missing references (idempotent). Run
/// after every writer is GC-aware and before `enable`.
pub async fn backfill(store: &Store) -> Result<GcReport> {
    let start = Instant::now();
    let mut report = GcReport::default();
    let k = store.meta.keys.clone();
    let page = store.page;
    let mut batch: Vec<Referrer> = Vec::new();
    macro_rules! push {
        ($r:expr) => {{
            batch.push($r);
            report.referrers += 1;
            if batch.len() >= BACKFILL_BATCH {
                write_batch(store, std::mem::take(&mut batch), &mut report).await?;
            }
        }};
    }
    // Markers and marker variants.
    for sub in ["marker", "mvariant"] {
        let rows = store.meta.scan(&k.sub(sub), page, |_| None).await?;
        report.keys_scanned += rows.len() as u64;
        for (key, value) in rows {
            if let Some(r) = marker_referrer(store, key, value, &mut report).await? {
                push!(r);
            }
        }
    }
    // Tombstones: the staged copy and the envelope's blob.
    let rows = store.meta.scan(&k.sub("tombstone"), page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let (_, raw): (String, Bytes) = k.root.unpack(&key).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let tid = Id(raw[..].try_into().map_err(|_| StoreError::Invalid("bad tombstone key".into()))?);
        let mut objects = vec![(Kind::StagedTombstone, tid)];
        objects.extend(envelope_blob(&value).map(|b| (Kind::Blob, b)));
        push!(Referrer { key, value, objects, absent: vec![], aerefs: vec![] });
    }
    // Local catalogue records (staged or committed).
    let rows = store.meta.scan(&k.sub("catalog"), page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let Ok(rec) = SignedRecord::from_bytes(&value) else { continue };
        let snap = snapshot_of(store, &rec.body.snapshot).await;
        let objects = record_objects(rec.body.snapshot, snap.as_ref());
        push!(Referrer { key, value, objects, absent: vec![], aerefs: vec![] });
    }
    // Foreign catalogue copies: the record's objects and the payloads of its contents.
    let rows = store.meta.scan(&k.sub("xcatalog"), page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let Ok(rec) = SignedRecord::from_bytes(&value) else { continue };
        let (_, source, _): (String, String, Bytes) = k.root.unpack(&key).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let snap = snapshot_of(store, &rec.body.snapshot).await;
        let mut objects = record_objects(rec.body.snapshot, snap.as_ref());
        if let Some(s) = &snap {
            for rid in &s.contents {
                let Some(bytes) = store.meta.get(k.xrevision(&source, rid)).await? else { continue };
                let Ok(rev) = Revision::from_preimage(&bytes) else { continue };
                objects.push((Kind::Group, rev.group));
                objects.push((Kind::Capsule, rev.capsule));
                for c in chunks_of_group(store, &rev.group).await? {
                    objects.push((Kind::Chunk, c));
                }
            }
        }
        let objects = dedup(&objects);
        push!(Referrer { key, value, objects, absent: vec![], aerefs: vec![] });
    }
    // Committed batch records: each member's staged marker or tombstone and group.
    let rows = store.meta.scan(&k.batches(), page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let Ok(rec) = crate::batch::BatchRecord::decode_value(&value) else { continue };
        push!(Referrer { key, value, objects: batch_objects(&rec), absent: vec![], aerefs: vec![] });
    }
    // Pending validation jobs (J1 without J2 or J3).
    let rows = store.meta.scan(&k.sub("jobreq"), page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let Ok(job) = SignedJob::from_bytes(&value) else { continue };
        let Some((w, r)) = job_key_parts(&k, &key) else { continue };
        let absent = vec![k.job_receipt(&w, &r), k.job_cancel(&w, &r)];
        push!(Referrer { key, value, objects: job_objects(&job), absent, aerefs: vec![] });
    }
    // Pending anti-entropy events: the object references among their staged parts.
    let rows = store.meta.scan(&k.sub("aepending"), page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let (_, source, event): (String, String, Bytes) = k.root.unpack(&key).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let parts = store.meta.scan(&k.ae_parts(&source, &event), page, |_| None).await?;
        report.keys_scanned += parts.len() as u64;
        let mut objects = Vec::new();
        for (_, part) in parts {
            if let Ok(crate::ae::AePart::ObjectRef { kind, id, .. }) = crate::ae::AePart::from_pce(&part) {
                objects.push((kind, id));
            }
        }
        let objects = dedup(&objects);
        let aerefs = objects.iter().map(|(kind, id)| k.gc_aeref(&source, &event, *kind, id)).collect();
        push!(Referrer { key, value, objects, absent: vec![], aerefs });
    }
    // P5 task history: each immutable event row names its task blob.
    let p5 = k.root.subspace(&("p5", "event"));
    let rows = store.meta.scan(&p5, page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        if value.len() != 40 {
            continue;
        }
        let blob = Id(value[8..40].try_into().expect("length checked"));
        push!(Referrer { key, value, objects: vec![(Kind::Blob, blob)], absent: vec![], aerefs: vec![] });
    }
    write_batch(store, batch, &mut report).await?;
    let kb = k.gc_backfilled();
    store.meta.run(Txn::Gc, Box::new(move |trx| {
        let kb = kb.clone();
        Box::pin(async move {
            trx.set(&kb, b"1");
            Ok(Step::Commit(()))
        })
    })).await?;
    report.transactions += 1;
    report.elapsed_ms = start.elapsed().as_millis() as u64;
    Ok(report)
}

/// Set `gc/indexed` (sweeps may run). Requires a completed backfill.
pub async fn enable(store: &Store) -> Result<()> {
    let k = store.meta.keys.clone();
    store.meta.run(Txn::Gc, Box::new(move |trx| {
        let k = k.clone();
        Box::pin(async move {
            if get(trx, &k.gc_backfilled()).await?.is_none() {
                return Err(StoreError::Invalid("store GC: run the reference backfill before enabling collection".into()));
            }
            if get(trx, &k.gc_indexed()).await?.is_some() {
                return Ok(Step::Done(()));
            }
            trx.set(&k.gc_indexed(), b"1");
            Ok(Step::Commit(()))
        })
    })).await
}

/// Clear `gc/indexed`: later sweeps refuse to run. References keep being maintained.
pub async fn disable(store: &Store) -> Result<()> {
    let key = store.meta.keys.gc_indexed();
    store.meta.run(Txn::Gc, Box::new(move |trx| {
        let key = key.clone();
        Box::pin(async move {
            trx.clear(&key);
            Ok(Step::Commit(()))
        })
    })).await
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Swept {
    Referenced,
    Unsighted,
    Sighted,
    Waiting,
    Doomed,
    PendingDelete,
}

/// One sweep pass: tick the clock, release finished jobs' references, retire dead catalogue
/// records past grace, then list every S3 kind and run one transaction per object. Refuses
/// to run unless collection is enabled (`gc/indexed`).
pub async fn sweep(store: &Store, cfg: &GcConfig) -> Result<GcReport> {
    let start = Instant::now();
    let mut report = GcReport::default();
    if !store.gc_enabled().await? {
        return Err(StoreError::Invalid("store GC is not enabled (run gc backfill, then gc enable)".into()));
    }
    let c0 = tick(store).await?;
    report.clock = c0;
    report.transactions += 1;
    release_jobs(store, &mut report).await?;
    retire_dead_records(store, cfg, c0, &mut report).await?;
    let k = store.meta.keys.clone();
    for kind in Kind::S3_KINDS {
        let (objects, pages) = store.s3.list_sized(kind).await?;
        report.listing_pages += pages;
        for (id, size) in objects {
            report.examined += 1;
            report.examined_bytes += size;
            let k = k.clone();
            let grace = cfg.grace;
            let swept = store.meta.run(Txn::Gc, Box::new(move |trx| {
                let k = k.clone();
                Box::pin(async move { sweep_one(trx, &k, kind, id, size, grace, c0).await })
            })).await?;
            report.transactions += 1;
            match swept {
                Swept::Referenced => report.referenced += 1,
                Swept::Unsighted => report.unsighted += 1,
                Swept::Sighted => report.sighted += 1,
                Swept::Waiting => report.waiting += 1,
                Swept::Doomed => {
                    report.doomed += 1;
                    report.doomed_bytes += size;
                }
                Swept::PendingDelete => report.pending_delete += 1,
            }
        }
    }
    report.elapsed_ms = start.elapsed().as_millis() as u64;
    Ok(report)
}

async fn sweep_one(trx: &Transaction, k: &Keys, kind: Kind, id: Id, size: u64, grace: u64, c0: u64) -> Result<Step<Swept>> {
    let (b0, e0) = k.gcrefs_of(kind, &id).range();
    // Limit one; FDB adds the whole requested range to the read-conflict set when it is
    // empty, so a reference committed first aborts this transaction.
    let referenced = !range(trx, b0, e0, 1).await?.is_empty() && !cfg!(feature = "mutate-storegc-doom-no-ref-check");
    let key = k.gcobj(kind, &id);
    let state = state_in(trx, k, kind, &id).await?;
    let clock = read_clock(trx, k).await?;
    Ok(match (referenced, state) {
        (true, Some(GcState::Sighted { .. })) => {
            trx.clear(&key);
            Step::Commit(Swept::Unsighted)
        }
        (true, _) => Step::Done(Swept::Referenced),
        (false, None) => {
            trx.set(&key, &GcState::Sighted { clock }.encode());
            Step::Commit(Swept::Sighted)
        }
        (false, Some(GcState::Sighted { clock: t })) => {
            if clock.saturating_sub(t) >= grace || cfg!(feature = "mutate-storegc-doom-no-grace") {
                trx.set(&key, &GcState::Doomed { clock, size }.encode());
                if !cfg!(feature = "mutate-storegc-doom-no-ocert-clear") {
                    trx.clear(&k.ocert(kind, &id));
                }
                trx.atomic_op(&k.gc_dooms(), &1u64.to_le_bytes(), MutationType::Add);
                Step::Commit(Swept::Doomed)
            } else {
                Step::Done(Swept::Waiting)
            }
        }
        // Listed after the delete completed (its `Gone` precedes this pass's tick): the bytes
        // were uploaded again and nothing references them. Start over.
        (false, Some(GcState::Gone { clock: t, .. })) if t < c0 => {
            trx.set(&key, &GcState::Sighted { clock }.encode());
            Step::Commit(Swept::Sighted)
        }
        (false, Some(_)) => Step::Done(Swept::PendingDelete),
    })
}

/// J1 references are released once J2 (a receipt) or J3 (a cancellation) exists.
async fn release_jobs(store: &Store, report: &mut GcReport) -> Result<()> {
    let k = store.meta.keys.clone();
    let rows = store.meta.scan(&k.sub("jobreq"), store.page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let Ok(job) = SignedJob::from_bytes(&value) else { continue };
        let Some((w, r)) = job_key_parts(&k, &key) else { continue };
        report.jobs_examined += 1;
        let (k2, key, objects) = (k.clone(), Arc::new(key), Arc::new(job_objects(&job)));
        let (receipt, cancel) = (k.job_receipt(&w, &r), k.job_cancel(&w, &r));
        let released = store.meta.run(Txn::Gc, Box::new(move |trx| {
            let (k, key, objects, receipt, cancel) = (k2.clone(), key.clone(), objects.clone(), receipt.clone(), cancel.clone());
            Box::pin(async move {
                let finished = get(trx, &receipt).await?.is_some() || get(trx, &cancel).await?.is_some();
                if !finished && !cfg!(feature = "mutate-storegc-job-release-no-check") {
                    return Ok(Step::Done(false));
                }
                let (kind, id) = objects[0];
                if get(trx, &k.gcref(kind, &id, &key)).await?.is_none() {
                    return Ok(Step::Done(false));
                }
                release_in(trx, &k, &objects, &key);
                Ok(Step::Commit(true))
            })
        })).await?;
        report.transactions += 1;
        if released {
            report.jobs_released += 1;
        }
    }
    Ok(())
}

/// A staged `catalog/<c>` with no `rcert/<c>` whose token rank is below the fence can never
/// commit (T5 needs `rank = fence`; the fence only grows) and recovery never adopts it. After
/// `grace` ticks it is cleared with its references, and `gc/retired/catalog/<c>` recorded.
async fn retire_dead_records(store: &Store, cfg: &GcConfig, c0: u64, report: &mut GcReport) -> Result<()> {
    let k = store.meta.keys.clone();
    let rows = store.meta.scan(&k.sub("catalog"), store.page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    for (key, value) in rows {
        let Ok(rec) = SignedRecord::from_bytes(&value) else { continue };
        let c = rec.id();
        if key != k.catalog(&c) {
            continue;
        }
        report.catalogue_examined += 1;
        if store.meta.get(k.rcert(&c)).await?.is_some() {
            continue;
        }
        let snap = snapshot_of(store, &rec.body.snapshot).await;
        let objects = Arc::new(record_objects(rec.body.snapshot, snap.as_ref()));
        let (k2, key, value, rank, grace) = (k.clone(), Arc::new(key), Arc::new(value), rec.body.token.rank, cfg.grace);
        let outcome = store.meta.run(Txn::Gc, Box::new(move |trx| {
            let (k, key, value, objects) = (k2.clone(), key.clone(), value.clone(), objects.clone());
            Box::pin(async move {
                if get(trx, &key).await?.as_deref() != Some(value.as_slice()) || get(trx, &k.rcert(&c)).await?.is_some() {
                    return Ok(Step::Done(0));
                }
                let fence = match get(trx, &k.fence()).await? {
                    Some(v) => { let mut d = Dec::new(&v); let n = d.uvarint()?; d.end()?; n }
                    None => 0,
                };
                if rank >= fence && !cfg!(feature = "mutate-storegc-retire-no-fence-check") {
                    return Ok(Step::Done(0));
                }
                let clock = read_clock(trx, &k).await?;
                let seen_key = k.gc_dead_seen(&c);
                match get(trx, &seen_key).await? {
                    None => {
                        trx.set(&seen_key, &clock.to_be_bytes());
                        Ok(Step::Commit(1))
                    }
                    Some(t) if clock.saturating_sub(u64_be(&t)?) >= grace => {
                        trx.clear(&key);
                        trx.clear(&seen_key);
                        release_in(trx, &k, &objects, &key);
                        trx.set(&k.gc_retired_catalog(&c), &clock.to_be_bytes());
                        Ok(Step::Commit(2))
                    }
                    Some(_) => Ok(Step::Done(0)),
                }
            })
        })).await?;
        let _ = c0;
        report.transactions += 1;
        match outcome {
            1 => report.catalogue_dead_seen += 1,
            2 => report.catalogue_retired += 1,
            _ => {}
        }
    }
    Ok(())
}

/// Drive the deletion of every doomed (or interrupted deleting) object: a GC-principal
/// DELETE through s3-guard, which moves the state to `Deleting{nonce}` before forwarding and
/// to `Gone` after Garage's success. `gc_s3` holds the GC principal's credentials.
pub async fn delete_doomed(store: &Store, gc_s3: &Payloads) -> Result<GcReport> {
    let start = Instant::now();
    let mut report = GcReport::default();
    if !store.gc_enabled().await? {
        return Err(StoreError::Invalid("store GC is not enabled".into()));
    }
    let k = store.meta.keys.clone();
    let rows = store.meta.scan(&k.gcobj_sub(), store.page, |_| None).await?;
    report.keys_scanned += rows.len() as u64;
    report.transactions += rows.len().div_ceil(store.page.max(1)) as u64;
    for (key, value) in rows {
        let size = match GcState::decode(&value)? {
            GcState::Doomed { size, .. } | GcState::Deleting { size, .. } => size,
            _ => continue,
        };
        let (_, kind, raw): (String, String, Bytes) = k.root.unpack(&key).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let kind = Kind::from_name(&kind).ok_or_else(|| StoreError::Invalid("bad gcobj kind".into()))?;
        let id = Id(raw[..].try_into().map_err(|_| StoreError::Invalid("bad gcobj id".into()))?);
        report.examined += 1;
        match gc_s3.try_delete(kind, &id).await {
            Ok(()) => {
                report.transactions += 1;
                match store.gc_state(kind, &id).await? {
                    Some(GcState::Gone { .. }) => {
                        report.deleted += 1;
                        report.reclaimed_bytes += size;
                    }
                    other => report.anomalies.push(format!("{} {id}: delete acknowledged but state {:?}", kind.name(), other)),
                }
            }
            Err(e) => {
                report.delete_failures += 1;
                if report.anomalies.len() < 16 {
                    report.anomalies.push(format!("{} {id}: delete refused or failed: {}", kind.name(), e.chars().take(300).collect::<String>()));
                }
            }
        }
    }
    report.elapsed_ms = start.elapsed().as_millis() as u64;
    Ok(report)
}

/// Read-only counters for `gc status`.
pub async fn status(store: &Store) -> Result<GcStatus> {
    let k = &store.meta.keys;
    let mut s = GcStatus {
        indexed: store.meta.get(k.gc_indexed()).await?.is_some(),
        backfilled: store.meta.get(k.gc_backfilled()).await?.is_some(),
        clock: store.meta.get(k.gc_clock()).await?.map(|v| u64_be(&v)).transpose()?.unwrap_or(0),
        dooms: store.meta.get(k.gc_dooms()).await?
            .map(|v| v.get(..8).and_then(|b| b.try_into().ok()).map(u64::from_le_bytes).unwrap_or(0)).unwrap_or(0),
        ..Default::default()
    };
    for (_, v) in store.meta.scan(&k.gcobj_sub(), store.page, |_| None).await? {
        *s.states.entry(GcState::decode(&v)?.name().into()).or_default() += 1;
    }
    s.references = store.meta.scan(&k.sub("gcref"), store.page, |_| None).await?.len() as u64;
    s.retired_catalogue = store.meta.scan(&k.root.subspace(&("gc", "retired", "catalog")), store.page, |_| None).await?.len() as u64;
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn state_encoding_round_trips_and_is_small() {
        for s in [
            GcState::Sighted { clock: 7 },
            GcState::Doomed { clock: 9, size: 1 << 40 },
            GcState::Deleting { nonce: [3; 16], size: 12 },
            GcState::Gone { clock: u64::MAX, nonce: [9; 16] },
        ] {
            let v = s.encode();
            assert!(v.len() <= 25, "far below FDB's 100 kB value limit");
            assert_eq!(GcState::decode(&v).unwrap(), s);
        }
        assert!(GcState::decode(&[1, 0]).is_err());
        assert!(GcState::decode(&[5; 9]).is_err());
        assert!(!GcState::Sighted { clock: 0 }.retired());
        assert!(GcState::Gone { clock: 0, nonce: [0; 16] }.retired());
    }

    /// s3-guard computes the same key bytes from the tuple layer without this crate.
    #[test]
    fn gcobj_key_layout_is_the_documented_tuple() {
        let k = Keys::new("dep");
        let id = Id([0xab; 32]);
        let expected = Subspace::from(("paralean", "dep")).pack(&("gcobj", "group", Bytes::from(&id.0[..])));
        assert_eq!(k.gcobj(Kind::Group, &id), expected);
        assert_eq!(k.gc_clock(), Subspace::from(("paralean", "dep")).pack(&("gc", "clock")));
        assert_ne!(k.gcref(Kind::Group, &id, b"a"), k.gcref(Kind::Group, &id, b"b"));
        assert!(k.gcref(Kind::Group, &id, &[7; 4096]).len() < 200, "referrers are hashed into the key");
    }
}
