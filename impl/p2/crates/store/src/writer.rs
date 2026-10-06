//! Writer workflows: publication (payload, staged marker, T1), certificates (T2, T6),
//! catalogue writes (T5), checkpoint commit, the controller's T3/T4, and repair (T7).
//!
//! Write order everywhere: payload first, acknowledged by S3 with its checksum, then the
//! metadata transaction that names it. Named crash points (`Faults::point`) sit between
//! the steps so tests can kill a writer between payload and metadata.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::error::{GuardFailure, Result, StoreError};
use crate::id::{Id, Kind, WorkspaceId};
use crate::meta::{CommitArgs, PreparedTarget, PublishArgs, PublishOutcome, ValueKind};
use crate::objects::*;
use crate::s3::Acked;
use crate::sign::Signer;
use crate::store::Store;

/// Everything a publication names. The receipt must admit the group (§6).
#[derive(Clone, Debug)]
pub struct Package {
    pub group: Opaque,
    pub chunks: Vec<Opaque>,
    pub capsule: Opaque,
    pub receipt: Receipt,
    pub revisions: Vec<Revision>,
    pub marker: Marker,
    /// Target names the group declares, each with the epoch and head read by the preparer.
    pub targets: Vec<PreparedTarget>,
}

/// A checkpoint to commit: the snapshot, its export manifests and the catalogue chain.
#[derive(Clone, Debug)]
pub struct Checkpoint {
    pub snapshot: Snapshot,
    pub source_root: Manifest,
    pub build_receipt: Manifest,
    pub predecessor: Option<Id>,
    pub token: TokenRef,
}

#[derive(Clone)]
pub struct Writer {
    pub store: Store,
    pub id: WorkspaceId,
    signer: Signer,
}

impl Writer {
    pub fn new(store: Store, id: WorkspaceId, signer: Signer) -> Writer {
        Writer { store, id, signer }
    }

    pub fn with_store(&self, store: Store) -> Writer {
        Writer { store, ..self.clone() }
    }

    /// The preparer's single linearizable read of a target record (§7).
    pub async fn prepare_target(&self, name: &Name) -> Result<PreparedTarget> {
        let rec = self.store.target(name).await?.ok_or_else(|| GuardFailure::NoTargetRecord(name.clone()))?;
        if rec.owner != self.id {
            return Err(GuardFailure::NotOwner { name: name.clone() }.into());
        }
        Ok(PreparedTarget { name: name.clone(), epoch: rec.epoch, head: rec.head })
    }

    fn check_package(&self, p: &Package) -> Result<Id> {
        let bad = |s: &str| Err(StoreError::Guard(GuardFailure::BadPackage(s.into())));
        if p.group.kind != Kind::Group || p.capsule.kind != Kind::Capsule || p.chunks.iter().any(|c| c.kind != Kind::Chunk) {
            return bad("object kinds");
        }
        let g = p.group.id();
        if p.marker.group != g {
            return bad("marker names another group");
        }
        let ids: BTreeSet<Id> = p.revisions.iter().map(|r| r.id()).collect();
        if ids.len() != p.revisions.len() || p.marker.revisions != ids.iter().copied().collect::<Vec<_>>() {
            return bad("marker revisions differ from the package's");
        }
        if p.revisions.iter().any(|r| r.group != g || r.capsule != p.capsule.id()) {
            return bad("revision names another group or capsule");
        }
        if p.marker.receipt != p.receipt.id() {
            return bad("marker names another receipt");
        }
        if !p.receipt.admits(&g, &self.store.ring) {
            return Err(GuardFailure::ReceiptRejected(g).into());
        }
        Ok(g)
    }

    /// Publish a group: S3 objects, the acknowledged marker copy, then T1, which writes the
    /// marker, revisions, receipt, target heads and this writer's certificate atomically,
    /// conditional on each target record's owner, epoch and head.
    pub async fn publish(&self, p: &Package) -> Result<PublishOutcome> {
        let g = self.check_package(p)?;
        self.store.s3.put_opaque(&p.group).await?;
        for c in &p.chunks {
            self.store.s3.put_opaque(c).await?;
        }
        self.store.s3.put_opaque(&p.capsule).await?;
        self.store.faults.point("publish:after-payload")?;
        let mid = p.marker.id();
        self.store.s3.put(Kind::StagedMarker, &p.marker.preimage()).await?;
        self.store.faults.point("publish:after-staged-marker")?;
        let marker_value = self.store.stage_value(mid, p.marker.preimage()).await?;
        let mut revisions = Vec::new();
        for r in &p.revisions {
            let rid = r.id();
            revisions.push((rid, r.clone(), self.store.stage_value(rid, r.preimage()).await?));
        }
        let cert = Cert::sign(CertBody { replica: self.store.replica, marker: mid, group: g, writer: self.id }, &self.signer);
        let args = PublishArgs {
            writer: self.id,
            group: g,
            marker_id: mid,
            marker_value,
            revisions,
            receipt_id: p.receipt.id(),
            receipt_value: p.receipt.to_bytes(),
            targets: p.targets.clone(),
            cert_value: cert.to_bytes(),
        };
        let _ = &cert;
        let out = self.store.meta.t1_publish(Arc::new(args)).await?;
        if cfg!(feature = "mutate-cert-outside-publish") {
            // The lagging design (TLA `AtomicCert = FALSE`): certify in a later transaction.
            self.store.faults.point("publish:before-cert")?;
            let v = cert.to_bytes();
            self.store.meta.t2_raw_cert(g, self.id, v).await?;
        }
        Ok(out)
    }

    /// T2: certify a group already published (and certified by someone).
    pub async fn certify(&self, group: &Id) -> Result<bool> {
        let (mid, _) = self.store.marker(group).await?.ok_or(GuardFailure::NotPublished(*group))?;
        let cert = Cert::sign(CertBody { replica: self.store.replica, marker: mid, group: *group, writer: self.id }, &self.signer);
        self.store.meta.t2_certify(*group, self.id, mid, cert.to_bytes()).await
    }

    /// T6: certify an object this process has seen acknowledged.
    pub async fn certify_object(&self, acked: Acked) -> Result<bool> {
        let oc = ObjectCert::sign(
            ObjectCertBody { replica: self.store.replica, kind: acked.kind(), id: acked.id(), writer: self.id },
            &self.signer,
        );
        self.store.meta.t6_object(acked.kind(), acked.id(), oc.to_bytes()).await
    }

    /// A verified read of an S3 object, then T6.
    pub async fn certify_existing(&self, kind: Kind, id: &Id) -> Result<Acked> {
        let (acked, _) = self
            .store
            .s3
            .get_acked(kind, id)
            .await?
            .ok_or(GuardFailure::NotAcknowledged { kind, id: *id })?;
        self.certify_object(acked).await?;
        Ok(acked)
    }

    pub fn sign_record(&self, snapshot: Id, predecessor: Option<Id>, token: TokenRef) -> SignedRecord {
        SignedRecord::sign(CatalogRecord { workspace: self.id, snapshot, predecessor, token }, &self.signer)
    }

    fn commit_args(&self, rec: &SignedRecord) -> Arc<CommitArgs> {
        let rc = CommitCert::sign(
            CommitCertBody { replica: self.store.replica, catalog: rec.id(), token: rec.body.token },
            &self.signer,
        );
        Arc::new(CommitArgs { record: rec.clone(), record_value: rec.to_bytes(), rcert_value: rc.to_bytes() })
    }

    /// T5 (staging form): fenced first write of the record's bytes, no commit certificate.
    pub async fn stage_record(&self, rec: &SignedRecord) -> Result<bool> {
        self.store.meta.t5_stage(self.commit_args(rec)).await
    }

    /// T5: fenced write of the record and its commit certificate; parents must be committed
    /// and the record's snapshot certified.
    pub async fn commit_record(&self, rec: &SignedRecord) -> Result<bool> {
        self.store.meta.t5_commit(self.commit_args(rec)).await
    }

    /// Commit a checkpoint: own certificates for every group (T2), object certificates for
    /// every payload (T6, after a verified read), the manifests and snapshot (S3, then T6),
    /// then the fenced record and commit certificate (T5). Returns the record's ID.
    pub async fn commit_checkpoint(&self, cp: &Checkpoint) -> Result<Id> {
        let st = &self.store;
        let mut payloads: Vec<(Kind, Id)> = Vec::new();
        for rid in &cp.snapshot.contents {
            let rev = st.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?;
            if !st.has_cert(&rev.group, &self.id).await? {
                self.certify(&rev.group).await?;
            }
            payloads.push((Kind::Group, rev.group));
            payloads.push((Kind::Capsule, rev.capsule));
        }
        payloads.sort();
        payloads.dedup();
        for (kind, id) in &payloads {
            if st.valid_ocert(*kind, id).await?.is_none() {
                self.certify_existing(*kind, id).await?;
            }
        }
        for m in [&cp.source_root, &cp.build_receipt] {
            let a = st.s3.put_object(Kind::Manifest, m).await?;
            self.certify_object(a).await?;
        }
        st.faults.point("checkpoint:before-snapshot")?;
        let snap = st.s3.put_object(Kind::Snapshot, &cp.snapshot).await?;
        // Monotone check before certifying the snapshot: every payload certificate exists.
        for (kind, id) in &payloads {
            if st.valid_ocert(*kind, id).await?.is_none() {
                return Err(GuardFailure::NotAcknowledged { kind: *kind, id: *id }.into());
            }
        }
        self.certify_object(snap).await?;
        st.faults.point("checkpoint:before-record")?;
        let rec = self.sign_record(snap.id(), cp.predecessor, cp.token);
        self.commit_record(&rec).await?;
        Ok(rec.id())
    }

    /// T7: copy an existing certificate from `source` (another replica or deployment holding
    /// the same abstract replica's certificates) to this store. Unconditional and unfenced;
    /// accepted only if the copy verifies under its signer's key and the certified object's
    /// bytes already exist here (repair means existing bytes).
    pub async fn repair_cert(&self, source: &Store, key: CertKey) -> Result<bool> {
        let st = &self.store;
        let (src_key, dst_key) = match &key {
            CertKey::Publication { group, writer } => (source.meta.keys.cert(group, writer), st.meta.keys.cert(group, writer)),
            CertKey::Commit { catalog } => (source.meta.keys.rcert(catalog), st.meta.keys.rcert(catalog)),
            CertKey::Object { kind, id } => (source.meta.keys.ocert(*kind, id), st.meta.keys.ocert(*kind, id)),
        };
        let v = source.meta.get(src_key).await?.ok_or(GuardFailure::RepairSourceMissing)?;
        let invalid = |s: &str| StoreError::Guard(GuardFailure::RepairInvalid(s.into()));
        let requires = match &key {
            CertKey::Publication { group, writer } => {
                let c = Cert::from_bytes(&v)?;
                if c.body.group != *group || c.body.writer != *writer || !st.ring.verify_writer(writer, &c.id(), &c.sig) {
                    return Err(invalid("publication certificate does not verify"));
                }
                Some((st.meta.keys.marker(group), c.body.marker, ValueKind::Envelope))
            }
            CertKey::Commit { catalog } => {
                let rc = CommitCert::from_bytes(&v)?;
                if rc.body.catalog != *catalog || !st.ring.verify_writer(&rc.body.token.holder, &rc.id(), &rc.sig) {
                    return Err(invalid("commit certificate does not verify"));
                }
                Some((st.meta.keys.catalog(catalog), *catalog, ValueKind::SignedRecord))
            }
            CertKey::Object { kind, id } => {
                let oc = ObjectCert::from_bytes(&v)?;
                if oc.body.kind != *kind || oc.body.id != *id || !st.ring.verify_writer(&oc.body.writer, &oc.id(), &oc.sig) {
                    return Err(invalid("object certificate does not verify"));
                }
                if st.s3.get(*kind, id).await?.is_none() {
                    return Err(GuardFailure::RepairNoExistingBytes.into());
                }
                None
            }
        };
        st.meta.t7_repair(dst_key, v, requires).await
    }

    /// A repair copy of S3 bytes (re-PUT of verified bytes from any source). Allowed at any
    /// fence; content addressing fixes the bytes, and it has no catalogue effect.
    pub async fn repair_object(&self, source: &Store, kind: Kind, id: &Id) -> Result<Acked> {
        let bytes = source.s3.get(kind, id).await?.ok_or(StoreError::Missing { kind: kind.name(), id: *id })?;
        self.store.s3.put(kind, &bytes).await
    }
}

/// A certificate key (T7).
#[derive(Clone, Debug)]
pub enum CertKey {
    Publication { group: Id, writer: WorkspaceId },
    Commit { catalog: Id },
    Object { kind: Kind, id: Id },
}

/// The controller: the fence authority (T3) and target assignment (T4).
#[derive(Clone)]
pub struct Controller {
    pub store: Store,
    signer: Signer,
}

impl Controller {
    pub fn new(store: Store, authority: Signer) -> Controller {
        Controller { store, signer: authority }
    }
    pub fn with_store(&self, store: Store) -> Controller {
        Controller { store, ..self.clone() }
    }
    /// T3: issue the next rank to `holder`.
    pub async fn rotate(&self, holder: WorkspaceId, request: &[u8]) -> Result<TokenRef> {
        self.store.meta.t3_rotate(request.to_vec(), holder, self.signer.clone()).await
    }
    /// T4: assign (first call) or reassign a target name; returns the new epoch.
    pub async fn reassign(&self, name: &Name, owner: WorkspaceId, request: &[u8]) -> Result<u64> {
        self.store.meta.t4_reassign(name.clone(), owner, request.to_vec()).await
    }
}
