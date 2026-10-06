//! Anti-entropy between independent deployments (each its own FoundationDB cluster and S3
//! store, each its own abstract replica σ of store.md).
//!
//! A sender exports what it has *discovered* (published groups and tombstones, by
//! certificates only) as self-verifying items: payload objects with their IDs, and groups
//! and tombstones with the sender's certificates. A receiver trusts nothing in transit:
//!
//! - every object is re-hashed against its ID, every decoded object against the IDs that
//!   name it (marker → revisions, receipt; certificate → marker or tombstone);
//! - every certificate and receipt signature is verified under the receiver's key ring
//!   (which must list the sender's writers and validators);
//! - a group or tombstone is applied only with at least one valid sender certificate (§8.3:
//!   receiving a published group needs a live certificate), only after its payloads are
//!   acknowledged by the receiver's own S3, and only if its revision parents (groups) or
//!   its target (tombstones) are already published here; otherwise it is deferred;
//! - the receiver certifies on its own replica, signed by its own sync writer (AckCertificates
//!   `put` needs only `known n d`). It never stores the sender's certificates as its own:
//!   they are kept under `xcert/` as evidence and never counted by discovery. T7 repair,
//!   the only copy of a certificate the model allows, requires the same σ and is not used.
//!
//! Every receive is one idempotent transaction (T9 for groups, T10 for tombstones), so
//! duplicates, reordering, partial transfers and lost replies are absorbed: what arrives
//! late or broken is deferred or rejected and supplied again by a later round. Rounds
//! repeat until neither side changes. The published set (groups with their markers,
//! tombstones) only grows and each item's effect is a function of the item, so any delivery
//! order reaches the same union. The exception is a group published at two deployments
//! with different markers; the store holds one marker per group (as the Workspaces model's
//! `Layout` holds one position per group), so that is reported as a conflict and neither
//! side's marker is replaced.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::error::{GuardFailure, Result, StoreError};
use crate::id::{sha256, Id, Kind};
use crate::meta::{ReceiveGroupArgs, ReceiveTombstoneArgs};
use crate::objects::*;
use crate::pce::{DResult, Dec, DecodeError, Enc, Pce};
use crate::recovery::discover;
use crate::store::Store;
use crate::writer::Writer;

/// One unit of transfer. Bytes are exactly the stored forms: preimages for unsigned objects,
/// `Signed` bytes for receipts and certificates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Object { kind: Kind, id: Id, bytes: Vec<u8> },
    Group { marker: Vec<u8>, revisions: Vec<Vec<u8>>, receipt: Vec<u8>, certs: Vec<Vec<u8>> },
    Tombstone { tombstone: Vec<u8>, certs: Vec<Vec<u8>> },
}

impl Pce for Item {
    fn encode(&self, e: &mut Enc) {
        match self {
            Item::Object { kind, id, bytes } => {
                e.byte(0).string(kind.name());
                id.encode(e);
                e.bytes(bytes);
            }
            Item::Group { marker, revisions, receipt, certs } => {
                e.byte(1).bytes(marker);
                e.list(revisions, |e, r| {
                    e.bytes(r);
                });
                e.bytes(receipt);
                e.list(certs, |e, c| {
                    e.bytes(c);
                });
            }
            Item::Tombstone { tombstone, certs } => {
                e.byte(2).bytes(tombstone);
                e.list(certs, |e, c| {
                    e.bytes(c);
                });
            }
        }
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        let bytes_list = |d: &mut Dec<'_>| d.list(|d| Ok(d.bytes()?.to_vec()));
        match d.byte()? {
            0 => Ok(Item::Object {
                kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("object kind"))?,
                id: Id::decode(d)?,
                bytes: d.bytes()?.to_vec(),
            }),
            1 => Ok(Item::Group {
                marker: d.bytes()?.to_vec(),
                revisions: bytes_list(d)?,
                receipt: d.bytes()?.to_vec(),
                certs: bytes_list(d)?,
            }),
            2 => Ok(Item::Tombstone { tombstone: d.bytes()?.to_vec(), certs: bytes_list(d)? }),
            tag => Err(DecodeError::UnknownTag { what: "anti-entropy item", tag }),
        }
    }
}

/// What a receiver did with an item.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Written now.
    Applied,
    /// Already present (a duplicate, or the receiver's own publication).
    Present,
    /// Not applicable yet (a payload, parent or target has not arrived); a later round
    /// supplies it.
    Deferred(String),
    /// Fails verification (corrupt or forged bytes, untrusted signer, rule violation).
    Rejected(String),
    /// The group is published here with another marker.
    Conflict { group: Id, local: Id, remote: Id },
}

/// The objects a discovered group or tombstone needs at the receiver.
fn needs_of_group(m: &Marker, revs: &[Revision]) -> Vec<(Kind, Id)> {
    let mut v = vec![(Kind::Group, m.group), (Kind::StagedMarker, m.id())];
    v.extend(revs.iter().map(|r| (Kind::Capsule, r.capsule)));
    v.sort();
    v.dedup();
    v
}

/// Export everything `store` has discovered, objects first, then groups (ancestors before
/// descendants where the sender knows them), then tombstones. A payload missing or corrupt
/// at the sender is left out; the group then waits at the receiver until a later round.
pub async fn export(store: &Store) -> Result<Vec<Item>> {
    let d = discover(store).await?;
    let mut objects = Vec::new();
    let mut groups = Vec::new();
    let mut seen = BTreeSet::new();
    for p in d.groups.values() {
        let mut revs = Vec::new();
        for rid in &p.marker.revisions {
            revs.push(store.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?);
        }
        for (kind, id) in needs_of_group(&p.marker, &revs) {
            if seen.insert((kind, id)) {
                if let Some(bytes) = store.s3.get(kind, &id).await? {
                    objects.push(Item::Object { kind, id, bytes });
                }
            }
        }
        let Some(receipt) = store.receipt(&p.marker.receipt).await? else { continue };
        let certs = store.certs(&p.marker.group).await?;
        let certs: Vec<Vec<u8>> = certs.iter().filter(|c| c.body.marker == p.marker_id).map(|c| c.to_bytes()).collect();
        let depth = revs.iter().map(|r| r.parents.len()).sum::<usize>();
        groups.push((
            depth,
            p.marker.lamport,
            Item::Group {
                marker: p.marker.preimage(),
                revisions: revs.iter().map(|r| r.preimage()).collect(),
                receipt: receipt.to_bytes(),
                certs,
            },
        ));
    }
    groups.sort_by(|a, b| (a.0, a.1).cmp(&(b.0, b.1)));
    let mut out = objects;
    out.extend(groups.into_iter().map(|g| g.2));
    for (tid, pt) in &d.tombstones {
        if let Some(bytes) = store.s3.get(Kind::StagedTombstone, tid).await? {
            out.push(Item::Object { kind: Kind::StagedTombstone, id: *tid, bytes });
        }
        let certs = store.tcerts(tid).await?;
        out.push(Item::Tombstone { tombstone: pt.tombstone.preimage(), certs: certs.iter().map(|c| c.to_bytes()).collect() });
    }
    Ok(out)
}

fn reject<T: std::fmt::Display>(why: T) -> Result<Outcome> {
    Ok(Outcome::Rejected(why.to_string()))
}

/// Map a receive transaction's guard failure to an outcome.
fn guard_outcome(e: StoreError) -> Result<Outcome> {
    match e {
        StoreError::Guard(GuardFailure::MarkerConflict { group, local, remote }) => Ok(Outcome::Conflict { group, local, remote }),
        StoreError::Guard(g @ (GuardFailure::UnknownParentRevision(_) | GuardFailure::NotPublished(_) | GuardFailure::Uncertified(_))) => {
            Ok(Outcome::Deferred(g.to_string()))
        }
        StoreError::Guard(g) => Ok(Outcome::Rejected(g.to_string())),
        e => Err(e),
    }
}

/// Receive one encoded item (as it arrived: possibly truncated or corrupt).
pub async fn import_bytes(w: &Writer, bytes: &[u8]) -> Result<Outcome> {
    match Item::from_pce(bytes) {
        Ok(item) => import(w, &item).await,
        Err(e) => reject(format!("undecodable item: {e}")),
    }
}

/// Receive one item at `w`'s deployment, certifying as `w`.
pub async fn import(w: &Writer, item: &Item) -> Result<Outcome> {
    let st = &w.store;
    match item {
        Item::Object { kind, id, bytes } => {
            if Id(sha256(bytes)) != *id || kind.domain().strip(bytes).is_err() {
                return reject(format!("{} {id:?}: bytes do not hash to the ID", kind.name()));
            }
            // A copy that is missing or corrupt here is (re-)PUT: this is also the payload
            // repair of store.md (content addressing fixes the bytes).
            if st.s3.get(*kind, id).await?.is_some() {
                return Ok(Outcome::Present);
            }
            st.s3.put(*kind, bytes).await?;
            Ok(Outcome::Applied)
        }
        Item::Group { marker, revisions, receipt, certs } => {
            let Ok(m) = Marker::from_preimage(marker) else { return reject("marker does not decode") };
            let (g, mid) = (m.group, m.id());
            let mut revs = Vec::new();
            for r in revisions {
                let Ok(r) = Revision::from_preimage(r) else { return reject("revision does not decode") };
                revs.push(r);
            }
            let ids: Vec<Id> = {
                let s: BTreeSet<Id> = revs.iter().map(|r| r.id()).collect();
                s.into_iter().collect()
            };
            if ids != m.revisions || ids.len() != revs.len() || revs.iter().any(|r| r.group != g) {
                return reject("revisions differ from the marker's");
            }
            let Ok(receipt) = Receipt::from_bytes(receipt) else { return reject("receipt does not decode") };
            if receipt.id() != m.receipt || !receipt.admits(&g, &st.ring) {
                return reject("receipt does not admit the group under a trusted validator");
            }
            let mut evidence = Vec::new();
            for c in certs {
                let Ok(c) = Cert::from_bytes(c) else { continue };
                let valid = c.body.group == g && c.body.marker == mid && st.ring.verify_writer(&c.body.writer, &c.id(), &c.sig);
                if valid || cfg!(feature = "mutate-receive-unverified-certs") {
                    evidence.push((st.meta.keys.xcert("cert", &g, &c.body.replica.0, &c.body.writer), c.to_bytes()));
                }
            }
            if evidence.is_empty() {
                return reject("no valid certificate from a trusted writer (a published group needs one)");
            }
            if let Some((local, _)) = st.marker(&g).await? {
                if local != mid && !cfg!(feature = "mutate-receive-overwrite-marker") {
                    return Ok(Outcome::Conflict { group: g, local, remote: mid });
                }
                if !st.certs(&g).await?.is_empty() {
                    return Ok(Outcome::Present);
                }
            }
            for (kind, id) in needs_of_group(&m, &revs) {
                if st.s3.get_acked(kind, &id).await?.is_none() && !cfg!(feature = "mutate-receive-no-payload-ack") {
                    return Ok(Outcome::Deferred(format!("{} {id:?} not acknowledged here", kind.name())));
                }
            }
            st.faults.point("receive:before-group")?;
            let mut rv = Vec::new();
            for r in &revs {
                rv.push((r.id(), r.clone(), st.stage_value(r.id(), r.preimage()).await?));
            }
            let mine = Cert::sign(CertBody { replica: st.replica, marker: mid, group: g, writer: w.id }, w.signer());
            // Mutation: store the sender's certificate as one of this deployment's.
            let mine_kv = if cfg!(feature = "mutate-receive-foreign-cert") {
                let c = Cert::from_bytes(&evidence[0].1)?;
                (st.meta.keys.cert(&g, &c.body.writer), c.to_bytes())
            } else {
                (st.meta.keys.cert(&g, &w.id), mine.to_bytes())
            };
            let args = ReceiveGroupArgs {
                group: g,
                marker_id: mid,
                marker_value: st.stage_value(mid, m.preimage()).await?,
                revisions: rv,
                receipt_id: receipt.id(),
                receipt_value: receipt.to_bytes(),
                cert: mine_kv,
                evidence,
            };
            match st.meta.t9_receive_group(Arc::new(args)).await {
                Ok(true) => Ok(Outcome::Applied),
                Ok(false) => Ok(Outcome::Present),
                Err(e) => guard_outcome(e),
            }
        }
        Item::Tombstone { tombstone, certs } => {
            let Ok(t) = Tombstone::from_preimage(tombstone) else { return reject("tombstone does not decode") };
            let tid = t.id();
            let mut evidence = Vec::new();
            let mut certifiers = Vec::new();
            for c in certs {
                let Ok(c) = TombstoneCert::from_bytes(c) else { continue };
                if c.body.tombstone == tid && c.body.target == t.target && st.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
                    certifiers.push(c.body.writer);
                    evidence.push((st.meta.keys.xcert("tcert", &tid, &c.body.replica.0, &c.body.writer), c.to_bytes()));
                }
            }
            if evidence.is_empty() {
                return reject("no valid tombstone certificate from a trusted writer");
            }
            if st.tombstone(&tid).await?.is_some() && !st.tcerts(&tid).await?.is_empty() {
                return Ok(Outcome::Present);
            }
            if st.s3.get_acked(Kind::StagedTombstone, &tid).await?.is_none() {
                return Ok(Outcome::Deferred("tombstone copy not acknowledged here".into()));
            }
            let Some((_, m)) = st.marker(&t.target).await? else {
                return Ok(Outcome::Deferred(format!("target {:?} not published here", t.target)));
            };
            let (mut names, mut workspaces) = (Vec::new(), Vec::new());
            for rid in &m.revisions {
                let r = st.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?;
                names.push(r.name);
                workspaces.push(r.workspace);
            }
            // The deleter is a certifier who is the target's author workspace (T8 wrote its
            // certificate); receivers' certificates do not make them deleters.
            let deleter = certifiers.iter().find(|c| workspaces.contains(c)).copied().unwrap_or(certifiers[0]);
            st.faults.point("receive:before-tombstone")?;
            let mine = TombstoneCert::sign(
                TombstoneCertBody { replica: st.replica, tombstone: tid, target: t.target, writer: w.id },
                w.signer(),
            );
            let args = ReceiveTombstoneArgs {
                tombstone: t.clone(),
                tombstone_id: tid,
                value: st.stage_value(tid, t.preimage()).await?,
                target_marker: m,
                target_names: names,
                target_workspaces: workspaces,
                deleter,
                cert: (st.meta.keys.tcert(&tid, &w.id), mine.to_bytes()),
                evidence,
            };
            match st.meta.t10_receive_tombstone(Arc::new(args)).await {
                Ok(true) => Ok(Outcome::Applied),
                Ok(false) => Ok(Outcome::Present),
                Err(e) => guard_outcome(e),
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct RoundStats {
    pub applied: usize,
    pub present: usize,
    pub deferred: usize,
    pub rejected: Vec<String>,
    pub conflicts: BTreeSet<(Id, Id, Id)>,
}

impl RoundStats {
    pub fn add(&mut self, o: &Outcome) {
        match o {
            Outcome::Applied => self.applied += 1,
            Outcome::Present => self.present += 1,
            Outcome::Deferred(_) => self.deferred += 1,
            Outcome::Rejected(r) => self.rejected.push(r.clone()),
            Outcome::Conflict { group, local, remote } => {
                self.conflicts.insert((*group, *local, *remote));
            }
        }
    }
}

/// One one-way round: export from `from`, import everything at `to`.
pub async fn push(from: &Store, to: &Writer) -> Result<RoundStats> {
    let mut s = RoundStats::default();
    for item in export(from).await? {
        s.add(&import(to, &item).await?);
    }
    Ok(s)
}

/// Bidirectional rounds until a round in both directions applies nothing. Returns the
/// number of rounds and the last round's statistics per direction.
pub async fn sync(a: (&Store, &Writer), b: (&Store, &Writer), max_rounds: usize) -> Result<(usize, RoundStats, RoundStats)> {
    for round in 1..=max_rounds {
        let ab = push(a.0, b.1).await?;
        let ba = push(b.0, a.1).await?;
        if ab.applied == 0 && ba.applied == 0 {
            return Ok((round, ab, ba));
        }
    }
    Err(StoreError::Invalid(format!("no convergence after {max_rounds} rounds")))
}

/// The published state a deployment exposes: discovered groups with their markers,
/// discovered tombstones, and the rendered files. Two deployments have converged when these
/// are equal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublishedSet {
    pub groups: BTreeMap<Id, Id>,
    pub tombstones: BTreeSet<Id>,
    pub files: BTreeMap<String, Vec<Id>>,
}

pub async fn published_set(store: &Store) -> Result<PublishedSet> {
    let d = discover(store).await?;
    Ok(PublishedSet {
        groups: d.groups.iter().map(|(g, p)| (*g, p.marker_id)).collect(),
        tombstones: d.tombstones.keys().copied().collect(),
        files: d.files,
    })
}
