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
//! - a group's receipt must pass P3's staging rule (`receipt::check`) against the job
//!   envelope it answers, under the receiver's key ring: a trusted validator, an accepted
//!   verdict, an envelope from a trusted issuer, the receiver's pinned policy and checker.
//!   An envelope binding a target names another deployment's target epochs; only that
//!   deployment's controller can sign it, so such a group is never received. T9 reads the
//!   receiver's revocation of the validator in its own transaction, as T1 does, and a
//!   sender does not export groups whose validator it has revoked;
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
//! order reaches the same union. Receipt-only variants of a group's marker can coexist
//! when their immutable fields agree. Different position or lineage fields conflict;
//! neither side's placement is replaced.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::error::{GuardFailure, Result, StoreError};
use crate::group_chunks::unique_chunks;
use crate::id::{sha256, Id, Kind};
use crate::meta::{ReceiveGroupArgs, ReceiveTombstoneArgs};
use crate::objects::*;
use crate::pce::{DResult, Dec, DecodeError, Enc, Pce};
use crate::receipt::{check, prepared_of, SignedJob};
use crate::recovery::discover;
use crate::store::Store;
use crate::writer::Writer;

/// One unit of transfer. Bytes are exactly the stored forms: preimages for unsigned objects,
/// `Signed` bytes for receipts and certificates.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Item {
    Object { kind: Kind, id: Id, bytes: Vec<u8> },
    /// `job` is the signed job envelope the receipt answers (P3 receipt binding).
    Group { marker: Vec<u8>, revisions: Vec<Vec<u8>>, receipt: Vec<u8>, job: Vec<u8>, certs: Vec<Vec<u8>> },
    Tombstone { tombstone: Vec<u8>, certs: Vec<Vec<u8>>, controller_grant: Option<Vec<u8>> },
    /// A committed batch (`batch/<id>` value) and its members, in commit order, each a
    /// `Group` or `Tombstone` item. Applied all or nothing by T13.
    Batch { record: Vec<u8>, members: Vec<Item> },
}

impl Pce for Item {
    fn encode(&self, e: &mut Enc) {
        match self {
            Item::Object { kind, id, bytes } => {
                e.byte(0).string(kind.name());
                id.encode(e);
                e.bytes(bytes);
            }
            Item::Group { marker, revisions, receipt, job, certs } => {
                e.byte(1).bytes(marker);
                e.list(revisions, |e, r| {
                    e.bytes(r);
                });
                e.bytes(receipt).bytes(job);
                e.list(certs, |e, c| {
                    e.bytes(c);
                });
            }
            Item::Tombstone { tombstone, certs, controller_grant } => {
                e.byte(2).bytes(tombstone);
                e.list(certs, |e, c| {
                    e.bytes(c);
                });
                // Preserve the original v0 bytes when no controller grant is present.
                if let Some(grant) = controller_grant { e.byte(1).bytes(grant); }
            }
            Item::Batch { record, members } => {
                e.byte(3).bytes(record);
                e.list(members, |e, m| {
                    e.bytes(&m.to_pce());
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
                job: d.bytes()?.to_vec(),
                certs: bytes_list(d)?,
            }),
            2 => {
                let tombstone = d.bytes()?.to_vec();
                let certs = bytes_list(d)?;
                let controller_grant = if d.remaining() == 0 { None } else { d.option(|d| Ok(d.bytes()?.to_vec()))? };
                Ok(Item::Tombstone { tombstone, certs, controller_grant })
            }
            3 => {
                let record = d.bytes()?.to_vec();
                let members = d.list(|d| Item::from_pce(d.bytes()?))?;
                if members.iter().any(|m| !matches!(m, Item::Group { .. } | Item::Tombstone { .. })) {
                    return Err(DecodeError::Invalid("batch member item"));
                }
                Ok(Item::Batch { record, members })
            }
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
    // Batch members travel only inside their batch's item (T13 applies it whole).
    let batch_markers: BTreeSet<(Id, Id)> = d.batches.values().flat_map(|r| r.markers().collect::<Vec<_>>()).collect();
    let batch_tombstones: BTreeSet<Id> = d.batches.values().flat_map(|r| r.tombstones().collect::<Vec<_>>()).collect();
    let mut members: BTreeMap<Id, Item> = BTreeMap::new();
    for p in d.positions.values() {
        let mut revs = Vec::new();
        for rid in &p.marker.revisions {
            revs.push(store.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?);
        }
        let mut required = needs_of_group(&p.marker, &revs);
        if let Some(group_bytes) = store.s3.get(Kind::Group, &p.marker.group).await? {
            if let Some(chunks) = unique_chunks(Kind::Group.domain().strip(&group_bytes)?)? {
                required.extend(chunks.keys().map(|id| (Kind::Chunk, *id)));
            }
        }
        required.sort(); required.dedup();
        for (kind, id) in required {
            if seen.insert((kind, id)) {
                if let Some(bytes) = store.s3.get(kind, &id).await? {
                    objects.push(Item::Object { kind, id, bytes });
                }
            }
        }
        let Some(receipt) = store.receipt(&p.marker.receipt).await? else { continue };
        // The envelope T1 (or T9) stored with the receipt; without it the receipt cannot be
        // checked anywhere (the sender's audit reports that). A group whose validator this
        // deployment has revoked is suspect here and is not spread further.
        let Some(job) = receipt_job(&receipt).map(|j| store.meta.keys.job(&j)) else { continue };
        let Some(job) = store.meta.get(job).await? else { continue };
        if store.meta.is_revoked(&receipt.body.validator_key).await? {
            continue;
        }
        let certs = store.certs(&p.marker.group).await?;
        let mut certs: Vec<Vec<u8>> = certs.iter().filter(|c| c.body.marker == p.marker_id).map(|c| c.to_bytes()).collect();
        for (_, value) in store.meta.scan(&store.meta.keys.xcertvs_of("cert", &p.marker.group), store.page, |_| None).await? {
            if Cert::from_bytes(&value).ok().is_some_and(|c| c.body.group == p.marker.group && c.body.marker == p.marker_id) {
                if !certs.contains(&value) { certs.push(value); }
            }
        }
        let depth = revs.iter().map(|r| r.parents.len()).sum::<usize>();
        let item = Item::Group {
            marker: p.marker.preimage(),
            revisions: revs.iter().map(|r| r.preimage()).collect(),
            receipt: receipt.to_bytes(),
            job,
            certs,
        };
        if batch_markers.contains(&(p.marker.group, p.marker_id)) {
            members.insert(p.marker_id, item);
        } else {
            groups.push((depth, p.marker.lamport, item));
        }
    }
    groups.sort_by(|a, b| (a.0, a.1).cmp(&(b.0, b.1)));
    let mut out = objects;
    out.extend(groups.into_iter().map(|g| g.2));
    let mut tombstones = Vec::new();
    for (tid, pt) in &d.tombstones {
        if let Some(bytes) = store.s3.get(Kind::StagedTombstone, tid).await? {
            out.push(Item::Object { kind: Kind::StagedTombstone, id: *tid, bytes });
        }
        let certs = store.tcerts(tid).await?;
        let mut certs: Vec<Vec<u8>> = certs.iter().map(|c| c.to_bytes()).collect();
        for (_, value) in store.meta.scan(&store.meta.keys.xcertvs_of("tcert", tid), store.page, |_| None).await? {
            if TombstoneCert::from_bytes(&value).ok().is_some_and(|c| c.body.tombstone == *tid) {
                if !certs.contains(&value) { certs.push(value); }
            }
        }
        let controller_grant = store.meta.get(store.meta.keys.delete_grant(tid)).await?;
        let item = Item::Tombstone { tombstone: pt.tombstone.preimage(), certs, controller_grant };
        if batch_tombstones.contains(tid) {
            members.insert(*tid, item);
        } else {
            tombstones.push(item);
        }
    }
    // A batch whose member cannot be exported here (missing receipt or job, revoked
    // validator) is left out whole; the receiver never gets part of it.
    'batches: for rec in d.batches.values() {
        let mut items = Vec::new();
        for e in &rec.entries {
            match members.get(&e.object) {
                Some(item) => items.push(item.clone()),
                None => continue 'batches,
            }
        }
        out.push(Item::Batch { record: rec.encode_value(), members: items });
    }
    out.extend(tombstones);
    Ok(out)
}

/// The job envelope ID a receipt's `requestID` slot names.
fn receipt_job(r: &Receipt) -> Option<Id> {
    r.body.request.as_ref().and_then(|q| <[u8; 32]>::try_from(&q[..]).ok()).map(Id)
}

fn reject<T: std::fmt::Display>(why: T) -> Result<Outcome> {
    Ok(Outcome::Rejected(why.to_string()))
}

/// Map a receive transaction's guard failure to an outcome.
fn guard_outcome(e: StoreError) -> Result<Outcome> {
    match e {
        StoreError::Guard(GuardFailure::MarkerConflict { group, local, remote }) => Ok(Outcome::Conflict { group, local, remote }),
        StoreError::Guard(
            g @ (GuardFailure::UnknownParentRevision(_)
            | GuardFailure::NotPublished(_)
            | GuardFailure::Uncertified(_)
            | GuardFailure::TombstoneReceiptAbsent(_)),
        ) => {
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
        Item::Batch { record, members } => import_batch(w, record, members).await,
        Item::Group { marker, revisions, receipt, job, certs } => {
            let args = match prepare_group(w, marker, revisions, receipt, job, certs, None).await? {
                Prep::Ready(args) => args,
                Prep::Out(o) => return Ok(o),
            };
            let variant = args.variant;
            match st.meta.t9_receive_group(Arc::new(args)).await {
                Ok(true) => Ok(Outcome::Applied),
                Ok(false) => Ok(Outcome::Present),
                // Both callers can observe an empty marker slot. If the other caller
                // commits first, re-stage against its marker on the next round so a
                // receipt-only variant can pass the ordinary compatibility check.
                Err(StoreError::Guard(GuardFailure::MarkerConflict { .. })) if !variant =>
                    Ok(Outcome::Deferred("marker changed during receive; retry compatibility check".into())),
                Err(e) => guard_outcome(e),
            }
        }
        Item::Tombstone { tombstone, certs, controller_grant } => {
            let args = match prepare_tombstone(w, tombstone, certs, controller_grant, None).await? {
                Prep::Ready(args) => args,
                Prep::Out(o) => return Ok(o),
            };
            match st.meta.t10_receive_tombstone(Arc::new(args)).await {
                Ok(true) => Ok(Outcome::Applied),
                Ok(false) => Ok(Outcome::Present),
                Err(e) => guard_outcome(e),
            }
        }
    }
}

/// A member that cannot be applied yet defers or rejects its whole batch. The mutation
/// `mutate-batch-ae-partial` instead applies the members checked so far.
macro_rules! o_or_prefix {
    ($o:expr, $prepared:expr, $id:expr, $record:expr, $st:expr) => {{
        if cfg!(feature = "mutate-batch-ae-partial") && !$prepared.is_empty() {
            let _ = crate::batch::t13_receive_batch($st, $id, std::mem::take(&mut $prepared), $record.to_vec()).await;
        }
        return Ok($o);
    }};
}

/// The members of a batch already checked, before the one being checked.
pub(crate) struct BatchContext {
    pub markers: Vec<(Marker, Vec<Revision>)>,
}

/// A checked member, ready for its T9 or T10 body inside T13.
pub(crate) enum Prepared {
    Group(ReceiveGroupArgs),
    Tombstone(ReceiveTombstoneArgs),
}

/// Receive a committed batch: verify its signed intent and record, check every member as
/// T9/T10's callers do (later members may depend on, revise or delete earlier ones), then
/// apply all of them, with the record and one relay event, in one T13 transaction. Any
/// member that is deferred or rejected defers or rejects the whole batch.
async fn import_batch(w: &Writer, record: &[u8], members: &[Item]) -> Result<Outcome> {
    let st = &w.store;
    let Ok(rec) = crate::batch::BatchRecord::decode_value(record) else { return reject("batch record does not decode") };
    let id = rec.id();
    let federation = st.ae_federation().await?;
    let mut issuers: Vec<[u8; 32]> = std::iter::once(st.ring.authority).chain(st.ring.job_issuers.iter().copied()).collect();
    if let Some(cfg) = &federation {
        for m in cfg.members.values() {
            issuers.push(m.authority);
            issuers.extend(m.job_issuers.iter().copied());
        }
    }
    if !issuers.iter().any(|k| import_verify(k, &id, &rec.intent.sig)) {
        return reject("batch intent is not signed by a trusted controller or job issuer");
    }
    if rec.entries.iter().map(|e| e.member.clone()).collect::<Vec<_>>() != rec.intent.body.members
        || rec.entries.len() != members.len() {
        return reject("batch record differs from its signed intent or its members");
    }
    if st.batch(&id).await?.is_some() {
        return Ok(Outcome::Present);
    }
    let mut ctx = BatchContext { markers: Vec::new() };
    let mut prepared = Vec::new();
    for (entry, item) in rec.entries.iter().zip(members) {
        let p = match (&entry.member, item) {
            (crate::batch::BatchMember::Publish { group, .. }, Item::Group { marker, revisions, receipt, job, certs }) => {
                let Ok(m) = Marker::from_preimage(marker) else { return reject("batch marker does not decode") };
                if m.group != *group || m.id() != entry.object {
                    return reject("batch marker differs from its record");
                }
                // The member's own publisher certificate is the origin evidence.
                let mut certs = certs.clone();
                let Some(at) = certs.iter().position(|c| Cert::from_bytes(c).is_ok_and(|c| c.id() == entry.cert)) else {
                    return reject("batch member lacks its publisher certificate");
                };
                certs.swap(0, at);
                match prepare_group(w, marker, revisions, receipt, job, &certs, Some(&ctx)).await? {
                    Prep::Ready(args) => {
                        let revs = revisions.iter().map(|r| Revision::from_preimage(r)).collect::<DResult<Vec<_>>>()?;
                        ctx.markers.push((m, revs));
                        Prepared::Group(args)
                    }
                    Prep::Out(o) => o_or_prefix!(o, prepared, id, record, st),
                }
            }
            (crate::batch::BatchMember::Tombstone { target, position, .. }, Item::Tombstone { tombstone, certs, controller_grant }) => {
                let Ok(t) = Tombstone::from_preimage(tombstone) else { return reject("batch tombstone does not decode") };
                if t.id() != entry.object || t.target != *target || t.position != *position {
                    return reject("batch tombstone differs from its record");
                }
                if !certs.iter().any(|c| TombstoneCert::from_bytes(c).is_ok_and(|c| c.id() == entry.cert)) {
                    return reject("batch tombstone lacks its certificate");
                }
                match prepare_tombstone(w, tombstone, certs, controller_grant, Some(&ctx)).await? {
                    Prep::Ready(args) => Prepared::Tombstone(args),
                    Prep::Out(o) => o_or_prefix!(o, prepared, id, record, st),
                }
            }
            _ => return reject("batch member kind differs from its record"),
        };
        prepared.push(p);
    }
    st.faults.point("receive:before-batch")?;
    match crate::batch::t13_receive_batch(st, id, prepared, record.to_vec()).await {
        Ok(true) => Ok(Outcome::Applied),
        Ok(false) => Ok(Outcome::Present),
        Err(e) => guard_outcome(e),
    }
}

pub(crate) enum Prep<T> {
    Ready(T),
    Out(Outcome),
}

fn prep_reject<T, D: std::fmt::Display>(why: D) -> Result<Prep<T>> {
    Ok(Prep::Out(Outcome::Rejected(why.to_string())))
}

/// Check a received group as T9's caller does: decoding, the staging rule under this
/// deployment's ring, certificates, payload acknowledgement and dependencies. In a batch,
/// `ctx` holds the members before it.
async fn prepare_group(w: &Writer, marker: &[u8], revisions: &[Vec<u8>], receipt: &[u8], job: &[u8], certs: &[Vec<u8>],
    ctx: Option<&BatchContext>) -> Result<Prep<ReceiveGroupArgs>> {
    let st = &w.store;
        let Ok(m) = Marker::from_preimage(marker) else { return prep_reject("marker does not decode") };
        let (g, mid) = (m.group, m.id());
        let mut revs = Vec::new();
        for r in revisions {
            let Ok(r) = Revision::from_preimage(r) else { return prep_reject("revision does not decode") };
            revs.push(r);
        }
        let ids: Vec<Id> = {
            let s: BTreeSet<Id> = revs.iter().map(|r| r.id()).collect();
            s.into_iter().collect()
        };
        if ids != m.revisions || ids.len() != revs.len() || revs.iter().any(|r| r.group != g) {
            return prep_reject("revisions differ from the marker's");
        }
        let Ok(receipt) = Receipt::from_bytes(receipt) else { return prep_reject("receipt does not decode") };
        if receipt.id() != m.receipt {
            return prep_reject("receipt is not the marker's");
        }
        let Ok(job) = SignedJob::from_bytes(job) else { return prep_reject("job envelope does not decode") };
        // A target is published only by its pinned home. Validate the original home
        // controller's signed job, while retaining this receiver's validator pins and
        // revocations. A receiver never creates or advances its own target record.
        let federation = st.ae_federation().await?;
        let mut target_home: Option<String> = None;
        let mut target_names = BTreeSet::new();
        if let Some(cfg) = &federation {
            for r in &revs {
                if let Some(home) = cfg.target_homes.get(&r.name) {
                    if target_home.as_ref().is_some_and(|h| h != home) {
                        return prep_reject("group declares target names at different homes");
                    }
                    target_home = Some(home.clone());
                    target_names.insert(r.name.clone());
                }
            }
        }
        if target_home.is_some() && job.body.targets.iter().map(|t| t.name.clone()).collect::<BTreeSet<_>>() != target_names {
            return prep_reject("home target publication has missing or extra target bindings");
        }
        if target_home.is_none() && !job.body.targets.is_empty() && federation.is_some() {
            return prep_reject("job binds names not declared in federation target homes");
        }
        let mut receipt_ring = (*st.ring).clone();
        if let Some(home) = &target_home {
            let cfg = federation.as_ref().expect("home only from config");
            if home == &st.deployment && st.marker_base(&g).await?.is_none() {
                return prep_reject("home target publication cannot be received as foreign before local publication");
            }
            let member = &cfg.members[home];
            receipt_ring.authority = member.authority;
            receipt_ring.job_issuers.clear();
        }
        if !cfg!(feature = "mutate-receive-no-receipt-check") {
            if !job.body.targets.is_empty() && !job.issued_by_controller(&receipt_ring) {
                return prep_reject("receipt is bound to another deployment's target epochs (TargetNames: one record per name, in one store)");
            }
            if let Err(e) = check(&receipt, &job, &g, &prepared_of(&job), &receipt_ring) {
                return prep_reject(format!("receipt fails the staging rule here: {e}"));
            }
        }
        let mut evidence = Vec::new();
        for c in certs {
            let Ok(c) = Cert::from_bytes(c) else { continue };
            let mut valid = c.body.group == g && c.body.marker == mid
                && st.ring.signing_writer_key_path(IMPORT_RELAXED, &c.body.writer, &c.id(), &c.sig).is_some();
            if let Some(cfg) = &federation {
                valid &= cfg.members.values().any(|member| member.replica == c.body.replica
                    && member.verify_writer_path(IMPORT_RELAXED, &st.ring, &c.body.writer, &c.id(), &c.sig));
            }
            if let Some(home) = &target_home {
                let member = &federation.as_ref().expect("home only from config").members[home];
                valid &= c.body.replica == member.replica && member.verify_writer_path(IMPORT_RELAXED, &st.ring, &c.body.writer, &c.id(), &c.sig);
            }
            if valid || cfg!(feature = "mutate-receive-unverified-certs") {
                evidence.push((st.meta.keys.xcertv("cert", &g, &c.id()), c.to_bytes()));
            }
        }
        if evidence.is_empty() {
            return prep_reject("no valid certificate from a trusted writer (a published group needs one)");
        }
        if target_home.is_none() {
            if let Some(cfg) = &federation {
                let origin_index = evidence.iter().position(|(_, value)| Cert::from_bytes(value).ok().is_some_and(|cert| {
                    cfg.members.values().any(|member| member.replica == cert.body.replica
                        && member.verify_writer_path(IMPORT_RELAXED, &st.ring, &cert.body.writer, &cert.id(), &cert.sig)
                        && std::iter::once(&member.authority).chain(&member.job_issuers).any(|key| import_verify(key, &job.id(), &job.sig)))
                }));
                let Some(origin_index) = origin_index else { return prep_reject("job issuer has no matching origin publication certificate"); };
                evidence.swap(0, origin_index);
            }
        }
        let base = st.marker_base(&g).await?;
        // A batch member is new here: the batch record was absent (T13 rechecks).
        if ctx.is_some() && base.is_some() {
            return prep_reject("a batch member is already published here");
        }
        let author_cert = evidence.iter().filter_map(|(_, value)| Cert::from_bytes(value).ok())
            .find(|cert| {
                let Some(public) = st.ring.signing_writer_key_path(IMPORT_RELAXED, &cert.body.writer, &cert.id(), &cert.sig) else { return false };
                let author_bound = st.ring.agent_keys.iter().any(|grant| grant.parts().is_some_and(|(agent, workspace, key, _)|
                    agent == m.author && workspace == cert.body.writer && key == public && grant.verify()));
                author_bound && target_home.as_ref().is_none_or(|home| federation.as_ref().is_some_and(|cfg|
                    cfg.members[home].replica == cert.body.replica && cfg.members[home].verify_writer_path(IMPORT_RELAXED, &st.ring, &cert.body.writer, &cert.id(), &cert.sig)))
            });
        // A property of this item, like every other evidence check: rejecting it lets
        // the exchange go on. An error would stall the source's queue at this event.
        let Some(author_cert) = author_cert else {
            if cfg!(feature = "mutate-author-cert-error") {
                return Err(StoreError::Invalid("origin author certificate missing".into()));
            }
            return prep_reject("no certificate from the origin author's registered key");
        };
        let author_writer = author_cert.body.writer;
        let Some(author_public) = st.ring.signing_writer_key_path(IMPORT_RELAXED, &author_writer, &author_cert.id(), &author_cert.sig) else {
            return prep_reject("origin author certificate key untrusted");
        };
        let variant = base.as_ref().is_some_and(|(local, _)| *local != mid);
        if let Some((local, existing)) = &base {
            let same_lineage = existing.group == m.group && existing.revisions == m.revisions
                && existing.lineage_keys == m.lineage_keys && existing.author == m.author;
            if (!same_lineage || (variant && cfg!(feature = "mutate-position-receive-conflict")))
                && !cfg!(feature = "mutate-receive-overwrite-marker") {
                return Ok(Prep::Out(Outcome::Conflict { group: g, local: *local, remote: mid }));
            }
        }
        let group_bytes = st.s3.get(Kind::Group, &g).await?;
        let chunk_index = group_bytes.as_ref().map(|bytes| unique_chunks(Kind::Group.domain().strip(bytes)?)).transpose()?.flatten();
        let mut required = needs_of_group(&m, &revs);
        if let Some(chunks) = &chunk_index { required.extend(chunks.keys().map(|id| (Kind::Chunk, *id))); }
        required.sort(); required.dedup();
        for (kind, id) in required {
            if st.s3.get_acked(kind, &id).await?.is_none() && !cfg!(feature = "mutate-receive-no-payload-ack") {
                return Ok(Prep::Out(Outcome::Deferred(format!("{} {id:?} not acknowledged here", kind.name()))));
            }
        }
        if let Some(chunks) = &chunk_index {
            for (id, length) in chunks {
                let Some((_, bytes)) = st.s3.get_acked(Kind::Chunk, id).await? else { return Ok(Prep::Out(Outcome::Deferred(format!("chunk {id:?} not acknowledged here")))); };
                if bytes.len() as u64 != *length { return prep_reject(format!("chunk {id:?} has length different from group manifest")); }
            }
        }
        // T1's dependency guard: the job's dependency capsules name groups T9 must
        // find published and certified here. A capsule not yet copied here waits.
        let dep_groups = match crate::writer::dependency_groups(st, &job).await {
            Ok(groups) => groups,
            Err(StoreError::Missing { kind, id }) => return Ok(Prep::Out(Outcome::Deferred(format!("{kind} {id:?} not here")))),
            Err(StoreError::Guard(g)) => return prep_reject(g),
            Err(StoreError::Invalid(why)) => return prep_reject(why),
            Err(e) => return Err(e),
        };
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
            (if variant { st.meta.keys.variant_cert(&g, &mid, &w.id) } else { st.meta.keys.cert(&g, &w.id) }, mine.to_bytes())
        };
        let args = ReceiveGroupArgs {
            group: g,
            marker_id: mid,
            author: m.author,
            author_writer,
            author_public,
            author_replica: author_cert.body.replica,
            ring: st.ring.clone(),
            marker_value: st.stage_value(mid, m.preimage()).await?,
            revisions: rv,
            receipt_id: receipt.id(),
            receipt_value: receipt.to_bytes(),
            validator_key: receipt.body.validator_key,
            job_id: job.id(),
            job_value: job.to_bytes(),
            local_issuers: std::iter::once(st.ring.authority).chain(st.ring.job_issuers.iter().copied()).collect(),
            job,
            dep_groups,
            replica: st.replica,
            cert: mine_kv,
            evidence,
            chunk_index: chunk_index.map(|m| m.into_iter().collect()),
            variant,
            target_home,
        };
    Ok(Prep::Ready(args))
}

/// Check a received tombstone as T10's caller does. In a batch its target may be an
/// earlier member, held in `ctx`.
async fn prepare_tombstone(w: &Writer, tombstone: &[u8], certs: &[Vec<u8>], controller_grant: &Option<Vec<u8>>,
    ctx: Option<&BatchContext>) -> Result<Prep<ReceiveTombstoneArgs>> {
    let st = &w.store;
        let controller_grant: Option<crate::authority::ControllerDeleteGrant> = controller_grant.as_ref()
            .map(|bytes| serde_json::from_slice(bytes).map_err(|_| StoreError::Invalid("bad controller deletion grant".into())))
            .transpose()?;
        let Ok(t) = Tombstone::from_preimage(tombstone) else { return prep_reject("tombstone does not decode") };
        let tid = t.id();
        let federation = st.ae_federation().await?;
        let mut evidence = Vec::new();
        let mut certifiers = Vec::new();
        for c in certs {
            let Ok(c) = TombstoneCert::from_bytes(c) else { continue };
            let source_bound = federation.as_ref().is_none_or(|cfg| cfg.members.values().any(|member|
                member.replica == c.body.replica && member.verify_writer_path(IMPORT_RELAXED, &st.ring, &c.body.writer, &c.id(), &c.sig)));
            let signer = st.ring.signing_writer_key_path(IMPORT_RELAXED, &c.body.writer, &c.id(), &c.sig);
            if let (true, Some(public)) = (c.body.tombstone == tid && c.body.target == t.target && source_bound, signer) {
                certifiers.push((c.body.writer, public, c.body.replica));
                evidence.push((st.meta.keys.xcertv("tcert", &tid, &c.id()), c.to_bytes()));
            }
        }
        if evidence.is_empty() {
            return prep_reject("no valid tombstone certificate from a trusted writer");
        }
        if st.s3.get_acked(Kind::StagedTombstone, &tid).await?.is_none() {
            return Ok(Prep::Out(Outcome::Deferred("tombstone copy not acknowledged here".into())));
        }
        // In a batch the target may be an earlier member, written by the same T13.
        let earlier = ctx.and_then(|c| c.markers.iter()
            .find(|(m, _)| m.group == t.target && t.position.is_none_or(|p| p == m.id())).cloned());
        let target = match (&earlier, t.position) {
            (Some((m, _)), _) => Some((m.id(), m.clone())),
            (None, Some(position)) => st.marker_variant(&t.target, &position).await?.map(|m| (position, m)),
            (None, None) => st.marker_base(&t.target).await?,
        };
        let Some((_, m)) = target else {
            return Ok(Prep::Out(Outcome::Deferred(format!("target {:?} not published here", t.target))));
        };
        let (mut names, mut workspaces) = (Vec::new(), Vec::new());
        match &earlier {
            Some((_, revs)) => for r in revs {
                names.push(r.name.clone());
                workspaces.push(r.workspace);
            },
            None => for rid in &m.revisions {
                let r = st.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?;
                names.push(r.name);
                workspaces.push(r.workspace);
            },
        }
        // The deleter is a certifier who is the target's author workspace (T8 wrote its
        // certificate); receivers' certificates do not make them deleters.
        let (deleter, deleter_public, deleter_replica) = certifiers.iter().find(|(writer, _, _)| workspaces.contains(writer)).copied().unwrap_or(certifiers[0]);
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
            deleter_public,
            deleter_replica,
            ring: st.ring.clone(),
            controller_grant,
            cert: (st.meta.keys.tcert(&tid, &w.id), mine.to_bytes()),
            evidence,
        };
    Ok(Prep::Ready(args))
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

/// The published state another deployment can converge to: [`published_set`] without the
/// groups whose receipt binds target epochs. Those are published only through T1 at their
/// home deployment and never received elsewhere (their envelopes fail every other
/// deployment's staging rule). Rendering reads only carried fields, so dropping them from
/// the rendered files leaves the other groups' order unchanged.
pub async fn exchangeable_set(store: &Store) -> Result<PublishedSet> {
    let mut s = published_set(store).await?;
    let mut home = BTreeSet::new();
    for (g, _) in s.groups.iter() {
        if let Some((_, m)) = store.marker(g).await? {
            if let Some(r) = store.receipt(&m.receipt).await? {
                if r.body.target.is_some() {
                    home.insert(*g);
                }
            }
        }
    }
    s.groups.retain(|g, _| !home.contains(g));
    for f in s.files.values_mut() {
        f.retain(|g| !home.contains(g));
    }
    s.files.retain(|_, f| !f.is_empty());
    Ok(s)
}

/// Every anti-entropy import signature (group and tombstone certificates, under current or
/// retired writer keys, and the federated job issuer) verifies at this one path.
const IMPORT_RELAXED: bool = cfg!(feature = "mutate-relaxed-import-sig");

fn import_verify(key: &[u8; 32], id: &Id, sig: &[u8]) -> bool {
    crate::sign::verify_path(IMPORT_RELAXED, key, id, sig)
}

pub async fn published_set(store: &Store) -> Result<PublishedSet> {
    let d = discover(store).await?;
    Ok(PublishedSet {
        groups: d.groups.iter().map(|(g, p)| (*g, p.marker_id)).collect(),
        tombstones: d.tombstones.keys().copied().collect(),
        files: d.files,
    })
}
