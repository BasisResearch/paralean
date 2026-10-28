//! Writer workflows: publication (payload, staged marker, T1), certificates (T2, T6),
//! catalogue writes (T5), checkpoint commit, the controller's T3/T4, and repair (T7).
//!
//! Write order everywhere: payload first, acknowledged by S3 with its checksum, then the
//! metadata transaction that names it. Named crash points (`Faults::point`) sit between
//! the steps so tests can kill a writer between payload and metadata.

use std::collections::BTreeSet;
use std::sync::Arc;

use crate::error::{GuardFailure, Result, StoreError};
use crate::group_chunks::unique_chunks;
use crate::id::{Id, Kind, WorkspaceId};
use crate::meta::{CommitArgs, PreparedTarget, PublishArgs, PublishOutcome, TombstoneArgs, ValueKind};
use crate::objects::*;
use crate::s3::Acked;
use crate::sign::Signer;
use crate::store::Store;

/// Everything a publication names. The receipt must admit the group (§6) and be bound to
/// `job`, the controller-signed envelope it answers (receipt.rs).
#[derive(Clone, Debug)]
pub struct Package {
    pub group: Opaque,
    pub chunks: Vec<Opaque>,
    pub capsule: Opaque,
    pub receipt: Receipt,
    pub job: crate::receipt::SignedJob,
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

/// The groups a job's dependency capsules name. P3 job dependencies are capsule IDs:
/// each is resolved through a hash-verified S3 read, and the P1 capsule's `declId` field
/// identifies the group that T1 (or T9, for a received group) must find published and
/// certified here. Old opaque capsules without `declId` fail closed when named as job
/// dependencies. P2-only fixtures have no job deps.
pub(crate) async fn dependency_groups(store: &Store, job: &crate::receipt::SignedJob) -> Result<Vec<Id>> {
    let mut dep_groups = BTreeSet::new();
    for cap in &job.body.deps {
        let pre = store.s3.get(Kind::Capsule, cap).await?
            .ok_or(StoreError::Missing { kind: "dependency capsule", id: *cap })?;
        let bytes = Kind::Capsule.domain().strip(&pre)?;
        let meta: serde_json::Value = serde_json::from_slice(bytes)
            .map_err(|e| StoreError::Invalid(format!("dependency capsule {}: {e}", cap.short())))?;
        let decl = meta.get("declId").and_then(|v| v.as_str()).and_then(Id::from_hex)
            .ok_or_else(|| GuardFailure::BadPackage(format!("dependency capsule {} has no declaration ID", cap.short())))?;
        dep_groups.insert(decl);
    }
    Ok(dep_groups.into_iter().collect())
}

/// The worker-side package checks (§6 staging rule, marker/revision consistency).
pub(crate) fn check_package(store: &Store, p: &Package) -> Result<Id> {
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
    // W2 A-6: every syncing copy writes a file at the marker's path; receivers refuse
    // to decode one that breaks the relative-path rule, so it is never published.
    if !cfg!(feature = "mutate-unchecked-publish-path") {
        if let Err(e) = p.marker.check() {
            return bad(&format!("marker file path: {e}"));
        }
    }
    // The staging rule: a worker stages only while holding a bound receipt (§6, P3).
    crate::receipt::check(&p.receipt, &p.job, &g, &p.targets, &store.ring)?;
    if let Some(refs) = unique_chunks(&p.group.pce)? {
        let provided: BTreeSet<Id> = p.chunks.iter().map(Opaque::id).collect();
        if provided.len() != p.chunks.len() || provided != refs.keys().copied().collect() {
            return bad("chunked group references do not equal Package.chunks");
        }
        for chunk in &p.chunks {
            if chunk.preimage().len() as u64 != refs[&chunk.id()] {
                return bad("chunk length differs from hashed group manifest");
            }
        }
    }
    Ok(g)
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

    /// Workspace signing key for authenticated worker control-plane calls.
    pub fn signer(&self) -> &Signer {
        &self.signer
    }

    /// The preparer's single linearizable read of a target record (§7).
    pub async fn prepare_target(&self, name: &Name) -> Result<PreparedTarget> {
        if let Some(cfg) = self.store.ae_federation().await? {
            if cfg.target_homes.get(name) != Some(&cfg.deployment) {
                return Err(GuardFailure::ForeignTarget(name.clone()).into());
            }
        }
        let rec = self.store.target(name).await?.ok_or_else(|| GuardFailure::NoTargetRecord(name.clone()))?;
        if rec.owner != self.id {
            return Err(GuardFailure::NotOwner { name: name.clone() }.into());
        }
        Ok(PreparedTarget { name: name.clone(), epoch: rec.epoch, head: rec.head })
    }

    fn check_package(&self, p: &Package) -> Result<Id> {
        check_package(&self.store, p)
    }

    /// Publish a group: S3 objects, the acknowledged marker copy, then T1, which writes the
    /// marker, revisions, receipt, target heads and this writer's certificate atomically,
    /// conditional on each target record's owner, epoch and head.
    pub async fn publish(&self, p: &Package) -> Result<PublishOutcome> {
        let g = self.check_package(p)?;
        self.publish_checked(p, g).await
    }

    /// Adversarial tests only: publish without the worker-side staging check, so that T1's
    /// own receipt check is what stands between the package and publication.
    #[cfg(feature = "adversary")]
    pub async fn publish_skipping_staging_check(&self, p: &Package) -> Result<PublishOutcome> {
        self.publish_checked(p, p.group.id()).await
    }

    async fn publish_checked(&self, p: &Package, g: Id) -> Result<PublishOutcome> {
        let dep_groups = dependency_groups(&self.store, &p.job).await?;
        for c in &p.chunks {
            self.store.s3.put_opaque(c).await?;
        }
        self.store.s3.put_opaque(&p.group).await?;
        let chunk_index = unique_chunks(&p.group.pce)?;
        if let Some(refs) = &chunk_index {
            for (id, length) in refs {
                let Some((_, bytes)) = self.store.s3.get_acked(Kind::Chunk, id).await? else {
                    return Err(GuardFailure::NotAcknowledged { kind: Kind::Chunk, id: *id }.into());
                };
                if bytes.len() as u64 != *length { return Err(GuardFailure::BadPackage("acknowledged chunk length differs from manifest".into()).into()); }
            }
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
            author: p.marker.author,
            marker_value,
            revisions,
            receipt_id: p.receipt.id(),
            receipt_value: p.receipt.to_bytes(),
            receipt: p.receipt.clone(),
            job: p.job.clone(),
            ring: self.store.ring.clone(),
            dep_groups,
            replica: self.store.replica,
            targets: p.targets.clone(),
            cert_value: cert.to_bytes(),
            chunk_index: chunk_index.map(|m| m.into_iter().collect()),
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

    /// Publish a tombstone (§11.4): the acknowledged S3 copy first (as a marker's), then T8,
    /// which writes the tombstone and this writer's tombstone certificate atomically.
    /// Returns false if the tombstone was already published by this writer.
    pub async fn tombstone(&self, t: &Tombstone) -> Result<bool> {
        self.tombstone_authorized(t, None).await
    }

    /// Controller deletion carries a signed, fence-bound grant for this exact tombstone.
    pub async fn tombstone_authorized(&self, t: &Tombstone, grant: Option<crate::authority::ControllerDeleteGrant>) -> Result<bool> {
        let st = &self.store;
        if let Err(e) = t.check() {
            return Err(StoreError::Guard(GuardFailure::BadPackage(format!("tombstone file path: {e}"))));
        }
        // T8 compares this target against immutable marker/<group> (or the position's
        // variant), while receipt-only variants can have a lower canonical ID. Their
        // carried revisions are identical.
        let m = match t.position {
            Some(position) => st.marker_variant(&t.target, &position).await?,
            None => st.marker_base(&t.target).await?.map(|(_, m)| m),
        }.ok_or(GuardFailure::NotPublished(t.target))?;
        let (mut names, mut workspaces) = (Vec::new(), Vec::new());
        for rid in &m.revisions {
            let r = st.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?;
            names.push(r.name);
            workspaces.push(r.workspace);
        }
        let tid = t.id();
        st.s3.put(Kind::StagedTombstone, &t.preimage()).await?;
        st.faults.point("tombstone:after-staged")?;
        let value = st.stage_value(tid, t.preimage()).await?;
        let cert = TombstoneCert::sign(
            TombstoneCertBody { replica: st.replica, tombstone: tid, target: t.target, writer: self.id },
            &self.signer,
        );
        let args = TombstoneArgs {
            writer: self.id,
            tombstone: t.clone(),
            tombstone_id: tid,
            value,
            cert_value: cert.to_bytes(),
            target_marker: m,
            target_names: names,
            target_workspaces: workspaces,
            ring: st.ring.clone(),
            controller_grant: grant,
        };
        let fresh = st.meta.t8_tombstone(Arc::new(args)).await?;
        st.faults.point("tombstone:before-cert")?;
        #[cfg(feature = "mutate-tombstone-cert-outside")]
        st.meta.t8_raw_cert(st.meta.keys.tcert(&tid, &self.id), cert.to_bytes()).await?;
        Ok(fresh)
    }

    /// Reinsert a group's position after a certified position tombstone. The
    /// marker keeps the same receipt, revisions and lineage keys; only placement
    /// and Lamport fields change. Concurrent moves remain separate certified
    /// positions and recovery chooses a deterministic live one.
    pub async fn move_position(&self, marker: &Marker, old: &Tombstone) -> Result<bool> {
        let old_id = old.position.ok_or_else(|| GuardFailure::BadPackage("move requires position tombstone".into()))?;
        let old_marker = self.store.marker_variant(&old.target, &old_id).await?
            .ok_or(GuardFailure::NotPublished(old.target))?;
        if marker.group != old.target || (!cfg!(feature = "mutate-position-cross-file") && marker.file_path != old.file_path)
            || marker.author != old_marker.author || (!cfg!(feature = "mutate-position-author") && marker.author != old.author)
            || (!cfg!(feature = "mutate-position-lineage")
                && (marker.revisions != old_marker.revisions || marker.receipt != old_marker.receipt
                    || marker.lineage_keys != old_marker.lineage_keys)) || marker.lamport <= old.lamport
            || (!cfg!(feature = "mutate-position-bad-root")
                && marker.root_path.last() != Some(&(marker.group, marker.lamport, marker.author))) {
            return Err(GuardFailure::BadPackage("move changes lineage or has invalid placement".into()).into());
        }
        let Some(t) = self.store.tombstone(&old.id()).await? else {
            return Err(GuardFailure::BadPackage("move tombstone absent".into()).into());
        };
        if t != *old || (!cfg!(feature = "mutate-position-no-tombstone-guard")
            && !self.store.tcerts(&old.id()).await?.iter().any(|c| c.body.writer == self.id)) {
            return Err(GuardFailure::BadPackage("move tombstone uncertified".into()).into());
        }
        let anchor_marker = if cfg!(feature = "mutate-position-no-anchor") { None } else { match marker.anchor {
            Anchor::FileStart => None,
            Anchor::After(group) => {
                if group == marker.group || marker.root_path.len() < 2 {
                    return Err(GuardFailure::BadPackage("move anchor is cyclic or path is short".into()).into());
                }
                let d = crate::recovery::discover(&self.store).await?;
                let prefix = &marker.root_path[..marker.root_path.len() - 1];
                d.positions.iter().filter(|((g, _), p)| *g == group
                    && p.marker.file_path == marker.file_path && p.marker.root_path == prefix)
                    .map(|(_, p)| p.marker.clone()).next()
                    .ok_or_else(|| GuardFailure::BadPackage("move anchor position is not certified".into()))?
                    .into()
            }
        }};
        let mid = marker.id();
        self.store.s3.put(Kind::StagedMarker, &marker.preimage()).await?;
        let value = self.store.stage_value(mid, marker.preimage()).await?;
        let cert = Cert::sign(CertBody { replica: self.store.replica, marker: mid,
            group: marker.group, writer: self.id }, &self.signer);
        self.store.meta.t11_move_position(marker.clone(), old_marker, anchor_marker, old.clone(), value, cert.to_bytes(), self.id, self.store.ring.clone()).await
    }

    /// T2: certify a group already published (and certified by someone).
    pub async fn certify(&self, group: &Id) -> Result<bool> {
        // T2 signs the immutable marker/<group> value; canonical receipt-only variants
        // live under mvariant and are certified by their receive transaction.
        let (mid, _) = self.store.marker_base(group).await?.ok_or(GuardFailure::NotPublished(*group))?;
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

    fn commit_args(&self, rec: &SignedRecord, snapshot: Option<Snapshot>) -> Arc<CommitArgs> {
        let rc = CommitCert::sign(
            CommitCertBody { replica: self.store.replica, catalog: rec.id(), token: rec.body.token },
            &self.signer,
        );
        Arc::new(CommitArgs { record: rec.clone(), record_value: rec.to_bytes(), rcert_value: rc.to_bytes(), snapshot, ring: self.store.ring.clone(), replica: self.store.replica })
    }

    /// T5 (staging form): fenced first write of the record's bytes, no commit certificate.
    pub async fn stage_record(&self, rec: &SignedRecord) -> Result<bool> {
        self.store.meta.t5_stage(self.commit_args(rec, None)).await
    }

    /// T5: fenced write of the record and its commit certificate; parents must be committed
    /// and the record's snapshot certified.
    pub async fn commit_record(&self, rec: &SignedRecord) -> Result<bool> {
        let snapshot = self.store.s3.get_object::<Snapshot>(Kind::Snapshot, &rec.body.snapshot).await?;
        self.store.meta.t5_commit(self.commit_args(rec, snapshot)).await
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
    /// accepted only if the copy verifies under its signer's key, names this store's
    /// abstract replica σ (a replacement of σ, never another deployment: that would certify
    /// on its behalf), and the certified object's bytes already exist here (repair means
    /// existing bytes).
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
                if c.body.replica != st.replica {
                    return Err(invalid("certificate names another replica"));
                }
                Some((st.meta.keys.marker(group), c.body.marker, ValueKind::Envelope))
            }
            CertKey::Commit { catalog } => {
                let rc = CommitCert::from_bytes(&v)?;
                if rc.body.catalog != *catalog || !st.ring.verify_writer(&rc.body.token.holder, &rc.id(), &rc.sig) {
                    return Err(invalid("commit certificate does not verify"));
                }
                if rc.body.replica != st.replica {
                    return Err(invalid("certificate names another replica"));
                }
                Some((st.meta.keys.catalog(catalog), *catalog, ValueKind::SignedRecord))
            }
            CertKey::Object { kind, id } => {
                let oc = ObjectCert::from_bytes(&v)?;
                if oc.body.kind != *kind || oc.body.id != *id || !st.ring.verify_writer(&oc.body.writer, &oc.id(), &oc.sig) {
                    return Err(invalid("object certificate does not verify"));
                }
                if oc.body.replica != st.replica {
                    return Err(invalid("certificate names another replica"));
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
    pub async fn deletion_grant(&self, tombstone: &Tombstone) -> Result<crate::authority::ControllerDeleteGrant> {
        if self.signer.public() != self.store.ring.authority { return Err(StoreError::Invalid("controller key is not this deployment's authority".into())); }
        if tombstone.author != crate::authority::controller_agent_id(&self.signer.public()) {
            return Err(GuardFailure::ControllerDeleteDenied.into());
        }
        let fence = self.store.meta.fence().await?;
        Ok(crate::authority::ControllerDeleteGrant::sign(tombstone.id(), fence, &self.signer))
    }
    pub async fn register_agent_key(&self, agent: crate::id::AgentId, workspace: WorkspaceId, public: [u8; 32]) -> Result<bool> {
        if self.signer.public() != self.store.ring.authority { return Err(StoreError::Invalid("controller key is not this deployment's authority".into())); }
        let grant = crate::authority::AgentKeyGrant::sign(agent, workspace, public, &self.signer);
        self.store.meta.register_agent_key(grant, self.store.ring.authority).await
    }
    pub async fn revoke_agent_key(&self, public: [u8; 32]) -> Result<bool> {
        if self.signer.public() != self.store.ring.authority { return Err(StoreError::Invalid("controller key is not this deployment's authority".into())); }
        let revocation = crate::authority::AgentKeyRevocation::sign(public, &self.signer);
        self.store.meta.revoke_agent_key(revocation, self.store.ring.authority).await
    }
    /// T4: assign (first call) or reassign a target name; returns the new epoch.
    pub async fn reassign(&self, name: &Name, owner: WorkspaceId, request: &[u8]) -> Result<u64> {
        self.store.meta.t4_reassign(name.clone(), owner, request.to_vec()).await
    }
    /// Pin the statement hash (P1 `typeHash`) every published proof of `name` must have
    /// (W2 A-4). Write-once. A controller issuing a job for the name stamps this value
    /// instead of the worker's, and T1 compares the job's binding with it.
    pub async fn pin_statement(&self, name: &Name, statement: &[u8]) -> Result<bool> {
        self.store.meta.pin_target_statement(name.clone(), statement.to_vec()).await
    }
}
