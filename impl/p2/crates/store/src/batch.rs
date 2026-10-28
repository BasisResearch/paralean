//! Atomic multi-group publication (docs/atomic-pub-log.md; store.md T12 and T13).
//!
//! A batch publishes several groups and tombstones, possibly by several workspaces, all or
//! none. A controller (or job issuer) signs a [`BatchIntent`] (`v0/batch`) naming every
//! member in commit order. Each member's job envelope or tombstone carries the intent ID
//! (`batch`), so T1, T8, T9 and T10 refuse it: a member is published only by its batch.
//!
//! T12 is one FoundationDB transaction. It runs, for each member in order, the unchanged
//! body of T1 (publication) or T8 (tombstone), so every per-member guard is checked: the
//! receipt for exactly that group and envelope; owner, epoch and head of every target name;
//! the publisher's certificate and agent key; revocation, cancellation, dependency and
//! ancestry reads; W3's tombstone rules. Reads see the members before (FDB read-your-
//! writes), so a member may depend on, revise or delete an earlier member: the batch is a
//! sequence of single publications taken at one commit version (Veil `AtomicBatch`). One
//! failing guard aborts the transaction, so nothing of the batch is written. The batch is
//! idempotent as a whole: its record `batch/<id>` is read first.
//!
//! A batch must fit one transaction: at most [`MAX_BATCH_MEMBERS`] members and
//! [`MAX_BATCH_BYTES`] of written values, checked before any payload is written. That
//! keeps T12 well inside FDB's 10 MB / 5 s limits and its anti-entropy event inside the
//! receiver's caps (`ae.rs`). FDB itself aborts an over-large or over-long transaction as a
//! whole, so the bound is about availability, never safety. The staged protocol for larger
//! batches is designed and model-checked (`AtomicBatch.tla`, `Staged = TRUE`), not
//! implemented.
//!
//! Readers spanning several transactions close their view under batches: discovery adds
//! every member of a batch one of whose members it found (`recovery::discover`), a batch
//! travels by anti-entropy as one event applied by one T13 transaction, and a working copy
//! loads batch members only once its batch file is present.

use std::collections::BTreeSet;
use std::sync::Arc;

use foundationdb::tuple::{Bytes, Subspace};
use foundationdb::Transaction;

use crate::ae::{append_event, AeKind};
use crate::authority::ControllerDeleteGrant;
use crate::error::{GuardFailure, Result, StoreError};
use crate::faults::Txn;
use crate::group_chunks::unique_chunks;
use crate::id::{Domain, Id, Kind, WorkspaceId};
use crate::meta::{get, t1_body, t8_body, Keys, Mode, PublishArgs, Step, TombstoneArgs};
use crate::objects::*;
use crate::pce::{DResult, Dec, DecodeError, Enc, Pce};
use crate::sign::KeyRing;
use crate::store::Store;
use crate::writer::{check_package, dependency_groups, Package, Writer};

/// Members per batch. Every member's T1/T8 body runs inside one transaction, about 25
/// point reads each, so this keeps the transaction far below FDB's 5 s limit.
pub const MAX_BATCH_MEMBERS: usize = 128;
/// Values written by one batch (markers, revisions, receipts, envelopes, certificates,
/// tombstones, the record): a fifth of FDB's 10 MB transaction limit, and a quarter of the
/// receiver's 8 MiB inline cap per anti-entropy event.
pub const MAX_BATCH_BYTES: usize = 2 * 1024 * 1024;
/// Payload object references of one batch event, under the receiver's 8192 parts.
pub const MAX_BATCH_OBJECTS: usize = 4096;

const FORMAT: u64 = 0;

fn put_format(e: &mut Enc) {
    e.uvarint(FORMAT);
}
fn get_format(d: &mut Dec<'_>) -> DResult<()> {
    match d.uvarint()? {
        FORMAT => Ok(()),
        f => Err(DecodeError::Format(f)),
    }
}

/// One member of a batch intent, in commit order.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BatchMember {
    /// Publish `group`; its job envelope names this batch and `writer` signs it.
    Publish { group: Id, writer: WorkspaceId },
    /// Delete a position of `target` (`position`: the marker ID, as in a W3 tombstone).
    Tombstone { target: Id, position: Option<Id>, writer: WorkspaceId },
}

impl Pce for BatchMember {
    fn encode(&self, e: &mut Enc) {
        match self {
            BatchMember::Publish { group, writer } => {
                e.byte(0);
                group.encode(e);
                writer.encode(e);
            }
            BatchMember::Tombstone { target, position, writer } => {
                e.byte(1);
                target.encode(e);
                e.option(position, |e, x| x.encode(e));
                writer.encode(e);
            }
        }
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(match d.byte()? {
            0 => BatchMember::Publish { group: Id::decode(d)?, writer: WorkspaceId::decode(d)? },
            1 => BatchMember::Tombstone {
                target: Id::decode(d)?,
                position: d.option(Id::decode)?,
                writer: WorkspaceId::decode(d)?,
            },
            tag => return Err(DecodeError::UnknownTag { what: "batch member", tag }),
        })
    }
}

/// `v0/batch`: the members of one atomic publication, signed by the controller or by a
/// job issuer (target-free batches only, as for job envelopes).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BatchIntent {
    /// The coordinator's request ID (deduplication); it makes each intent distinct.
    pub request: Vec<u8>,
    pub members: Vec<BatchMember>,
}

impl Pce for BatchIntent {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        e.bytes(&self.request);
        e.list(&self.members, |e, m| m.encode(e));
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(BatchIntent { request: d.bytes()?.to_vec(), members: d.list(BatchMember::decode)? })
    }
}
impl Object for BatchIntent {
    const DOMAIN: Domain = Domain::Batch;
}

pub type SignedBatch = Signed<BatchIntent>;

impl SignedBatch {
    /// Signed by the controller or a configured job issuer, through W2's strict verifier.
    pub fn issued_by(&self, ring: &KeyRing) -> bool {
        let relaxed = cfg!(feature = "mutate-relaxed-batch-sig");
        crate::sign::verify_path(relaxed, &ring.authority, &self.id(), &self.sig)
            || ring.job_issuers.iter().any(|k| crate::sign::verify_path(relaxed, k, &self.id(), &self.sig))
    }
    pub fn issued_by_controller(&self, ring: &KeyRing) -> bool {
        crate::sign::verify_path(cfg!(feature = "mutate-relaxed-batch-sig"), &ring.authority, &self.id(), &self.sig)
    }
}

/// One committed member: what it published and the certificate that published it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BatchEntry {
    pub member: BatchMember,
    /// The marker ID of a publication, the tombstone ID of a deletion.
    pub object: Id,
    /// The member writer's publisher (or tombstone) certificate.
    pub cert: Id,
}

impl Pce for BatchEntry {
    fn encode(&self, e: &mut Enc) {
        self.member.encode(e);
        self.object.encode(e);
        self.cert.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(BatchEntry { member: BatchMember::decode(d)?, object: Id::decode(d)?, cert: Id::decode(d)? })
    }
}

/// `batch/<intent id>`: the signed intent and its committed members, written by the T12
/// (or T13) transaction that writes the members, never otherwise.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct BatchRecord {
    pub intent: SignedBatch,
    pub entries: Vec<BatchEntry>,
}

impl BatchRecord {
    pub fn encode_value(&self) -> Vec<u8> {
        let mut e = Enc::new();
        put_format(&mut e);
        e.bytes(&self.intent.to_bytes());
        e.list(&self.entries, |e, x| x.encode(e));
        e.out
    }
    pub fn decode_value(v: &[u8]) -> Result<BatchRecord> {
        let mut d = Dec::new(v);
        get_format(&mut d)?;
        let intent = SignedBatch::from_bytes(d.bytes()?)?;
        let entries = d.list(BatchEntry::decode)?;
        d.end()?;
        Ok(BatchRecord { intent, entries })
    }
    pub fn id(&self) -> Id {
        self.intent.id()
    }
    /// The marker IDs and tombstone IDs of the members.
    pub fn markers(&self) -> impl Iterator<Item = (Id, Id)> + '_ {
        self.entries.iter().filter_map(|e| match e.member {
            BatchMember::Publish { group, .. } => Some((group, e.object)),
            _ => None,
        })
    }
    pub fn tombstones(&self) -> impl Iterator<Item = Id> + '_ {
        self.entries.iter().filter_map(|e| match e.member {
            BatchMember::Tombstone { .. } => Some(e.object),
            _ => None,
        })
    }
}

impl Keys {
    /// `batch/<intent id>`: a committed batch (grow-only, like markers and certificates).
    pub fn batch(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("batch", Bytes::from(&id.0[..])))
    }
    pub fn batches(&self) -> Subspace {
        self.sub("batch")
    }
}

// ---------------------------------------------------------------- the intent check

/// What a T12 member is, for the pure intent check.
pub(crate) enum MemberArgs {
    Publish(PublishArgs),
    Tombstone(TombstoneArgs),
}

impl MemberArgs {
    fn as_member(&self) -> BatchMember {
        match self {
            MemberArgs::Publish(p) => BatchMember::Publish { group: p.group, writer: p.writer },
            MemberArgs::Tombstone(t) => BatchMember::Tombstone {
                target: t.tombstone.target, position: t.tombstone.position, writer: t.writer,
            },
        }
    }
    fn bytes(&self) -> usize {
        match self {
            MemberArgs::Publish(p) => {
                p.marker_value.len() + p.revisions.iter().map(|(_, _, v)| v.len()).sum::<usize>()
                    + p.receipt_value.len() + 2 * p.job.to_bytes().len() + p.cert_value.len()
                    + p.chunk_index.as_ref().map_or(0, |c| c.len() * 48)
            }
            MemberArgs::Tombstone(t) => {
                t.value.len() + t.cert_value.len() + t.controller_grant.as_ref().map_or(0, |g| g.encoded().len())
            }
        }
    }
}

/// The intent is genuine and names exactly these members, in this order: signed by the
/// controller (or a job issuer when no member binds a target name), with no repeated
/// subject, within the transaction budget.
pub(crate) fn check_intent(intent: &SignedBatch, members: &[MemberArgs], ring: &KeyRing) -> Result<()> {
    let fail = |s: &str| Err(StoreError::Guard(GuardFailure::BatchIntent(s.into())));
    if !cfg!(feature = "mutate-batch-unsigned-intent") {
        if !intent.issued_by(ring) {
            return fail("not signed by the controller or a job issuer");
        }
        let targets = members.iter().any(|m| matches!(m, MemberArgs::Publish(p) if !p.job.body.targets.is_empty()));
        if targets && !intent.issued_by_controller(ring) {
            return fail("a batch binding target names must be signed by the controller");
        }
    }
    if members.is_empty() || members.len() > MAX_BATCH_MEMBERS {
        return Err(GuardFailure::BatchTooLarge(format!("{} members (1 to {MAX_BATCH_MEMBERS})", members.len())).into());
    }
    if !cfg!(feature = "mutate-batch-unchecked-members") {
        let named: Vec<BatchMember> = members.iter().map(MemberArgs::as_member).collect();
        if named != intent.body.members {
            return fail("members differ from the signed intent");
        }
    }
    let mut subjects = BTreeSet::new();
    for m in &intent.body.members {
        let subject = match m {
            BatchMember::Publish { group, .. } => (0u8, *group, None),
            BatchMember::Tombstone { target, position, .. } => (1u8, *target, *position),
        };
        if !subjects.insert(subject) {
            return fail("a member is named twice");
        }
    }
    let bytes: usize = members.iter().map(MemberArgs::bytes).sum();
    if bytes > MAX_BATCH_BYTES {
        return Err(GuardFailure::BatchTooLarge(format!("{bytes} bytes of metadata (at most {MAX_BATCH_BYTES})")).into());
    }
    Ok(())
}

// ---------------------------------------------------------------- T12

pub(crate) struct BatchArgs {
    pub intent: SignedBatch,
    pub members: Vec<MemberArgs>,
    pub record_value: Vec<u8>,
    pub ring: Arc<KeyRing>,
}

/// The effect of a batch publication.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BatchOutcome {
    pub batch: Id,
    /// False when the batch was already committed (a retry after an unknown outcome).
    pub fresh: bool,
    pub record: BatchRecord,
}

async fn t12_body(trx: &Transaction, k: &Keys, a: &BatchArgs) -> Result<Step<bool>> {
    let id = a.intent.id();
    let bk = k.batch(&id);
    if let Some(v) = get(trx, &bk).await? {
        if v == a.record_value {
            return Ok(Step::Done(false));
        }
        return Err(GuardFailure::BatchConflict(id).into());
    }
    check_intent(&a.intent, &a.members, &a.ring)?;
    // Each member's own guards, in order, in this transaction. A failure aborts it.
    for (i, m) in a.members.iter().enumerate() {
        let r = match m {
            MemberArgs::Publish(p) => t1_body(trx, k, p, Mode::Batch(id)).await.map(|_| ()),
            MemberArgs::Tombstone(t) => t8_body(trx, k, t, Mode::Batch(id)).await.map(|_| ()),
        };
        if let Err(e) = r {
            if cfg!(feature = "mutate-batch-partial-commit") && i > 0 && e.guard().is_some() {
                // The mutant commits the members that passed.
                trx.set(&bk, &a.record_value);
                return Ok(Step::Commit(true));
            }
            return Err(e);
        }
    }
    trx.set(&bk, &a.record_value);
    append_event(trx, k, &AeKind::Batch { id }, 0);
    Ok(Step::Commit(true))
}

// ---------------------------------------------------------------- the writer

/// A member of a batch to publish, with its writer's own certificate. The coordinator
/// holds no member key: each participant signs its certificate with
/// [`Writer::sign_batch_publication`] or [`Writer::sign_batch_tombstone`].
#[derive(Clone, Debug)]
pub enum BatchItem {
    Publish { package: Package, writer: WorkspaceId, cert: Cert },
    Tombstone { tombstone: Tombstone, writer: WorkspaceId, cert: TombstoneCert, grant: Option<ControllerDeleteGrant> },
}

#[derive(Clone, Debug)]
pub struct BatchPackage {
    pub intent: SignedBatch,
    pub items: Vec<BatchItem>,
}

impl Writer {
    /// This workspace's publisher certificate for a batch member it authored.
    pub fn sign_batch_publication(&self, p: &Package) -> Cert {
        Cert::sign(CertBody { replica: self.store.replica, marker: p.marker.id(), group: p.group.id(), writer: self.id }, self.signer())
    }
    /// This workspace's tombstone certificate for a deletion in a batch.
    pub fn sign_batch_tombstone(&self, t: &Tombstone) -> TombstoneCert {
        TombstoneCert::sign(
            TombstoneCertBody { replica: self.store.replica, tombstone: t.id(), target: t.target, writer: self.id },
            self.signer(),
        )
    }
}

impl Store {
    /// Publish a batch: every member's payloads and staged copies first, then T12, which
    /// writes every member and the batch record atomically, or nothing.
    pub async fn publish_batch(&self, b: &BatchPackage) -> Result<BatchOutcome> {
        self.publish_batch_checked(b, true).await
    }

    /// Adversarial tests only: publish without the worker-side staging check, so that
    /// T12's own per-member guards are what stand between the batch and publication.
    #[cfg(feature = "adversary")]
    pub async fn publish_batch_skipping_staging_check(&self, b: &BatchPackage) -> Result<BatchOutcome> {
        self.publish_batch_checked(b, false).await
    }

    async fn publish_batch_checked(&self, b: &BatchPackage, staging_check: bool) -> Result<BatchOutcome> {
        let id = b.intent.id();
        if b.items.is_empty() || b.items.len() > MAX_BATCH_MEMBERS {
            return Err(GuardFailure::BatchTooLarge(format!("{} members (1 to {MAX_BATCH_MEMBERS})", b.items.len())).into());
        }
        // Payloads of every member first, so a member's job may name an earlier member's
        // capsule as a dependency.
        let mut objects = 0usize;
        for item in &b.items {
            if let BatchItem::Publish { package: p, .. } = item {
                if staging_check {
                    check_package(self, p)?;
                }
                if p.job.body.batch != Some(id) {
                    return Err(GuardFailure::BatchBinding(p.group.id()).into());
                }
                for c in &p.chunks {
                    self.s3.put_opaque(c).await?;
                }
                self.s3.put_opaque(&p.group).await?;
                self.s3.put_opaque(&p.capsule).await?;
                objects += 2 + p.chunks.len();
            }
        }
        if objects > MAX_BATCH_OBJECTS {
            return Err(GuardFailure::BatchTooLarge(format!("{objects} payload objects (at most {MAX_BATCH_OBJECTS})")).into());
        }
        self.faults.point("batch:after-payload")?;
        let mut members = Vec::with_capacity(b.items.len());
        let mut entries = Vec::with_capacity(b.items.len());
        for (i, item) in b.items.iter().enumerate() {
            match item {
                BatchItem::Publish { package: p, writer, cert } => {
                    let g = p.group.id();
                    let chunk_index = unique_chunks(&p.group.pce)?;
                    if let Some(refs) = &chunk_index {
                        for (cid, length) in refs {
                            let Some((_, bytes)) = self.s3.get_acked(Kind::Chunk, cid).await? else {
                                return Err(GuardFailure::NotAcknowledged { kind: Kind::Chunk, id: *cid }.into());
                            };
                            if bytes.len() as u64 != *length {
                                return Err(GuardFailure::BadPackage("acknowledged chunk length differs from manifest".into()).into());
                            }
                        }
                    }
                    let mid = p.marker.id();
                    self.s3.put(Kind::StagedMarker, &p.marker.preimage()).await?;
                    let marker_value = self.stage_value(mid, p.marker.preimage()).await?;
                    let mut revisions = Vec::new();
                    for r in &p.revisions {
                        let rid = r.id();
                        revisions.push((rid, r.clone(), self.stage_value(rid, r.preimage()).await?));
                    }
                    if cert.body.group != g || cert.body.marker != mid || cert.body.writer != *writer
                        || cert.body.replica != self.replica {
                        return Err(GuardFailure::BadPackage("member certificate does not bind its marker and writer".into()).into());
                    }
                    entries.push(BatchEntry {
                        member: BatchMember::Publish { group: g, writer: *writer },
                        object: mid,
                        cert: cert.id(),
                    });
                    members.push(MemberArgs::Publish(PublishArgs {
                        writer: *writer,
                        group: g,
                        marker_id: mid,
                        author: p.marker.author,
                        marker_value,
                        revisions,
                        receipt_id: p.receipt.id(),
                        receipt_value: p.receipt.to_bytes(),
                        receipt: p.receipt.clone(),
                        job: p.job.clone(),
                        ring: self.ring.clone(),
                        dep_groups: dependency_groups(self, &p.job).await?,
                        replica: self.replica,
                        targets: p.targets.clone(),
                        cert_value: cert.to_bytes(),
                        chunk_index: chunk_index.map(|m| m.into_iter().collect()),
                    }));
                }
                BatchItem::Tombstone { tombstone: t, writer, cert, grant } => {
                    if let Err(e) = t.check() {
                        return Err(GuardFailure::BadPackage(format!("tombstone file path: {e}")).into());
                    }
                    if t.batch != Some(id) {
                        return Err(GuardFailure::BatchBinding(t.id()).into());
                    }
                    // The target is an earlier member or already published here. T8 reads
                    // the stored marker in the transaction either way.
                    let earlier = b.items[..i].iter().find_map(|x| match x {
                        BatchItem::Publish { package, .. } if package.group.id() == t.target
                            && t.position.is_none_or(|pos| pos == package.marker.id()) =>
                            Some((package.marker.clone(), package.revisions.clone())),
                        _ => None,
                    });
                    let (m, revisions) = match earlier {
                        Some(found) => found,
                        None => {
                            let m = match t.position {
                                Some(position) => self.marker_variant(&t.target, &position).await?,
                                None => self.marker_base(&t.target).await?.map(|(_, m)| m),
                            }.ok_or(GuardFailure::NotPublished(t.target))?;
                            let mut revs = Vec::new();
                            for rid in &m.revisions {
                                revs.push(self.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?);
                            }
                            (m, revs)
                        }
                    };
                    let tid = t.id();
                    if cert.body.tombstone != tid || cert.body.target != t.target || cert.body.writer != *writer
                        || cert.body.replica != self.replica {
                        return Err(GuardFailure::BadPackage("member tombstone certificate does not bind its writer".into()).into());
                    }
                    self.s3.put(Kind::StagedTombstone, &t.preimage()).await?;
                    let value = self.stage_value(tid, t.preimage()).await?;
                    entries.push(BatchEntry {
                        member: BatchMember::Tombstone { target: t.target, position: t.position, writer: *writer },
                        object: tid,
                        cert: cert.id(),
                    });
                    members.push(MemberArgs::Tombstone(TombstoneArgs {
                        writer: *writer,
                        tombstone: t.clone(),
                        tombstone_id: tid,
                        value,
                        cert_value: cert.to_bytes(),
                        target_marker: m,
                        target_names: revisions.iter().map(|r| r.name.clone()).collect(),
                        target_workspaces: revisions.iter().map(|r| r.workspace).collect(),
                        ring: self.ring.clone(),
                        controller_grant: grant.clone(),
                    }));
                }
            }
            self.faults.point("batch:after-member")?;
        }
        check_intent(&b.intent, &members, &self.ring)?;
        let record = BatchRecord { intent: b.intent.clone(), entries };
        let record_value = record.encode_value();
        self.faults.point("batch:before-commit")?;
        let args = Arc::new(BatchArgs { intent: b.intent.clone(), members, record_value, ring: self.ring.clone() });
        let k = self.meta.keys.clone();
        let fresh = self.meta.run(Txn::T12PublishBatch, Box::new(move |trx| {
            let (k, args) = (k.clone(), args.clone());
            Box::pin(async move { t12_body(trx, &k, &args).await })
        })).await?;
        Ok(BatchOutcome { batch: id, fresh, record })
    }

    /// A committed batch, if any.
    pub async fn batch(&self, id: &Id) -> Result<Option<BatchRecord>> {
        match self.meta.get(self.meta.keys.batch(id)).await? {
            None => Ok(None),
            Some(v) => {
                let r = BatchRecord::decode_value(&v)?;
                if r.id() != *id {
                    return Err(StoreError::Invalid("batch key holds another intent".into()));
                }
                Ok(Some(r))
            }
        }
    }

    /// Every committed batch (a paginated scan; the key space only grows).
    pub async fn batch_records(&self) -> Result<Vec<BatchRecord>> {
        let rows = self.meta.scan(&self.meta.keys.batches(), 256, |_| None).await?;
        rows.into_iter().map(|(_, v)| BatchRecord::decode_value(&v)).collect()
    }
}

// ---------------------------------------------------------------- T13

/// Anti-entropy receive of a committed batch: every member's T9 or T10 body in order (a
/// member is admitted only with its batch), this deployment's copy of the record and one
/// relay event, in one transaction.
pub(crate) async fn t13_receive_batch(
    st: &Store, id: Id, members: Vec<crate::antientropy::Prepared>, record: Vec<u8>,
) -> Result<bool> {
    let k = st.meta.keys.clone();
    let members = Arc::new(members);
    let record = Arc::new(record);
    st.meta.run(Txn::T13ReceiveBatch, Box::new(move |trx| {
        let (k, members, record) = (k.clone(), members.clone(), record.clone());
        Box::pin(async move {
            let bk = k.batch(&id);
            if let Some(v) = get(trx, &bk).await? {
                if v == *record {
                    return Ok(Step::Done(false));
                }
                return Err(GuardFailure::BatchConflict(id).into());
            }
            for (i, m) in members.iter().enumerate() {
                let r = match m {
                    crate::antientropy::Prepared::Group(a) => crate::meta::t9_body(trx, &k, a, Mode::Batch(id)).await.map(|_| ()),
                    crate::antientropy::Prepared::Tombstone(a) => crate::meta::t10_body(trx, &k, a, Mode::Batch(id)).await.map(|_| ()),
                };
                if let Err(e) = r {
                    if cfg!(feature = "mutate-batch-ae-partial") && i > 0 && e.guard().is_some() {
                        // The mutant applies the members received so far.
                        return Ok(Step::Commit(true));
                    }
                    return Err(e);
                }
            }
            trx.set(&bk, &record);
            append_event(trx, &k, &AeKind::Batch { id }, 0);
            Ok(Step::Commit(true))
        })
    })).await
}
