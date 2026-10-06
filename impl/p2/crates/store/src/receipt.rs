//! Receipt binding (P3; resolves OPEN-7 of p0-interfaces.md §6, §10, §13).
//!
//! This module is the receipt format and the staging rule that P3 workers, the publication
//! transaction T1 and `remote%` consumers share. The receipt body itself is §6's
//! `ReceiptBody` (`objects.rs`), unchanged in shape: P3 fixes the contents of three slots.
//!
//! | §6 slot | P3 contents |
//! |---|---|
//! | `validatorBin` | ID of a [`CheckerVersion`] (domain `v0/checker`): the Lean commit, the SHA-256 of the checker binary and its mode (stock or fork validator) |
//! | `requestID` | ID of the [`JobEnvelope`] (domain `v0/job`) that asked for the check; required |
//! | `targetID` | PCE `set` of [`TargetBinding`] `{name, epoch, statement}`; `None` iff the job names no target |
//!
//! A job envelope is immutable and signed by the controller (the fence authority key of the
//! [`KeyRing`]). It names the content-addressed group, its capsule and the capsules of its
//! exact dependency closure, the base, the policy, the checker version, the requesting
//! workspace, each target with the owner epoch the controller read when it issued the job,
//! a deadline and a memory limit. The validator signs (Ed25519) a receipt whose
//! `requestID` is the envelope's ID and whose other slots repeat the envelope's fields, so
//! the receipt binds group, policy, checker version, request, epoch and target.
//!
//! [`check`] is the staging rule: a worker stages, and T1 publishes, a group `g` only with
//! a receipt that (1) verifies under a configured validator key, (2) is accepted, (3) names
//! `g`, (4) carries a controller-signed envelope whose ID is the receipt's `requestID` and
//! whose group, base, policy, checker and targets equal the receipt's, (5) uses a pinned
//! policy and checker, and (6) binds exactly the target names and epochs the publication was
//! prepared under. T1 additionally reads, in its own transaction, the revocation key of the
//! validator (`vrevoke/<key>`) and the cancellation key of the request (`jobcancel/<request>`),
//! so revocation and cancellation are linearizable with publication.
//!
//! Envelopes are signed by the authority key or, for target-free jobs only, by a configured
//! job-issuer key (`KeyRing::job_issuers`): working copies hold an issuer seed, never the
//! authority seed, which also signs fence tokens and revocations.
//!
//! Key rotation and revocation are minimal: the configured validator set ([`KeyRing`]
//! `validators`) may hold several keys at once, so a new key is added before validators
//! switch to it; a key is retired by removing it from the configuration, and revoked
//! immediately and globally by a signed [`Revocation`] in the store. A revoked key's
//! receipts no longer stage or publish anything; groups it already published stay published
//! (publication is monotone) and the audit lists them as suspect.

use std::sync::Arc;

use crate::error::{GuardFailure, Result};
use crate::faults::Txn;
use crate::id::{Domain, Id, WorkspaceId};
use crate::meta::{Keys, Meta, PreparedTarget, Step};
use crate::objects::*;
use crate::pce::{DResult, Dec, Enc, Pce};
use crate::sign::KeyRing;

/// The axioms policy v1 allows (§6).
pub const ALLOWED_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

fn put_format(e: &mut Enc) {
    e.uvarint(FORMAT);
}
fn get_format(d: &mut Dec<'_>) -> DResult<()> {
    match d.uvarint()? {
        FORMAT => Ok(()),
        f => Err(crate::pce::DecodeError::Format(f)),
    }
}

// ---------------------------------------------------------------- policy and checker

/// The checking policy a receipt names (`policyID = H("v0/policy", Policy)`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Policy {
    /// Axioms a group's members may depend on transitively. Any other axiom rejects,
    /// including `sorryAx` and the `native_decide` auxiliary axioms.
    pub allowed_axioms: Vec<Name>,
    /// A pinned target's statement hash must equal the one the validator re-derives.
    pub check_target_statements: bool,
}

impl Policy {
    pub fn v1() -> Policy {
        let mut allowed_axioms: Vec<Name> = ALLOWED_AXIOMS.iter().map(|a| Name::parse(a)).collect();
        allowed_axioms.sort_by_key(|n| n.to_pce());
        Policy { allowed_axioms, check_target_statements: true }
    }
}

impl Pce for Policy {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        e.set(&self.allowed_axioms, |e, n| n.encode(e));
        e.bool(self.check_target_statements);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(Policy { allowed_axioms: d.set(Name::decode)?, check_target_statements: d.bool()? })
    }
}
impl Object for Policy {
    const DOMAIN: Domain = Domain::Policy;
}

/// What checked a group (the contents of the receipt's `validatorBin` slot are this ID).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CheckerVersion {
    /// `lean --githash` of the toolchain the checker loads.
    pub lean_githash: String,
    /// SHA-256 of the checker binary (impl/p1's `paralean`, or the fork build of it).
    pub checker_sha256: Vec<u8>,
    /// `stock` (stock kernel) or `fork` (the Paralean fork in validator mode).
    pub mode: String,
}

impl CheckerVersion {
    /// The checker version the synthetic test fixtures name.
    pub fn fixture() -> CheckerVersion {
        CheckerVersion {
            lean_githash: "193c3589a4fc16c4059261ab38cfa365eb24f323".into(),
            checker_sha256: crate::id::sha256(b"paralean-fixture-checker").to_vec(),
            mode: "stock".into(),
        }
    }
}

impl Pce for CheckerVersion {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        e.string(&self.lean_githash).bytes(&self.checker_sha256).string(&self.mode);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(CheckerVersion { lean_githash: d.string()?, checker_sha256: d.bytes()?.to_vec(), mode: d.string()? })
    }
}
impl Object for CheckerVersion {
    const DOMAIN: Domain = Domain::Checker;
}

// ---------------------------------------------------------------- targets

/// One target a job (and so its receipt) is bound to.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct TargetBinding {
    pub name: Name,
    /// The owner epoch of the target record when the controller issued the job.
    pub epoch: u64,
    /// The pinned statement hash (P1 `typeHash`, 32 bytes), or empty for none.
    pub statement: Vec<u8>,
}

impl Pce for TargetBinding {
    fn encode(&self, e: &mut Enc) {
        self.name.encode(e);
        e.uvarint(self.epoch).bytes(&self.statement);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(TargetBinding { name: Name::decode(d)?, epoch: d.uvarint()?, statement: d.bytes()?.to_vec() })
    }
}

/// Canonical order of a binding set (PCE `set`: sorted by encoded bytes, no duplicates).
pub fn sort_targets(ts: &mut Vec<TargetBinding>) {
    ts.sort_by_key(|t| t.to_pce());
    ts.dedup();
}

/// The receipt's `targetID` slot for a binding set: `None` for no target.
pub fn target_slot(ts: &[TargetBinding]) -> Option<Vec<u8>> {
    if ts.is_empty() {
        return None;
    }
    let mut e = Enc::new();
    e.set(ts, |e, t| t.encode(e));
    Some(e.out)
}

/// Decode a `targetID` slot.
pub fn decode_target_slot(slot: &Option<Vec<u8>>) -> DResult<Vec<TargetBinding>> {
    match slot {
        None => Ok(vec![]),
        Some(b) => {
            let mut d = Dec::new(b);
            let v = d.set(TargetBinding::decode)?;
            d.end()?;
            Ok(v)
        }
    }
}

// ---------------------------------------------------------------- job envelope (§10, OPEN-11)

/// An immutable job envelope (`v0/job`), signed by the controller.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JobEnvelope {
    /// The client's request ID: the key of retry deduplication and cancellation.
    pub request: Vec<u8>,
    /// The content-addressed group to check (`group:…`).
    pub group: Id,
    /// The group's capsule (P1 group metadata: capsule text, members, dependency pins).
    pub capsule: Id,
    /// Capsules of the group's exact dependency closure, dependencies first. Every one
    /// names a group that is already published with a receipt.
    pub deps: Vec<Id>,
    pub base: Id,
    pub policy: Id,
    pub checker: Id,
    /// The requesting workspace (the target owner, for a target job).
    pub worker: WorkspaceId,
    /// Sorted, distinct.
    pub targets: Vec<TargetBinding>,
    /// Wall-clock budget for the check; past it the validator gives no verdict.
    pub deadline_ms: u64,
    /// Address-space limit of the checking process, in MiB (0: the validator default).
    pub memory_mb: u64,
}

impl Pce for JobEnvelope {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        e.bytes(&self.request);
        self.group.encode(e);
        self.capsule.encode(e);
        e.list(&self.deps, |e, x| x.encode(e));
        self.base.encode(e);
        self.policy.encode(e);
        self.checker.encode(e);
        self.worker.encode(e);
        e.set(&self.targets, |e, t| t.encode(e));
        e.uvarint(self.deadline_ms).uvarint(self.memory_mb);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(JobEnvelope {
            request: d.bytes()?.to_vec(),
            group: Id::decode(d)?,
            capsule: Id::decode(d)?,
            deps: d.list(Id::decode)?,
            base: Id::decode(d)?,
            policy: Id::decode(d)?,
            checker: Id::decode(d)?,
            worker: WorkspaceId::decode(d)?,
            targets: d.set(TargetBinding::decode)?,
            deadline_ms: d.uvarint()?,
            memory_mb: d.uvarint()?,
        })
    }
}
impl Object for JobEnvelope {
    const DOMAIN: Domain = Domain::Job;
}

pub type SignedJob = Signed<JobEnvelope>;

impl SignedJob {
    /// A pure signature check: Ed25519 over the envelope ID under the authority key or any
    /// configured job-issuer key.
    pub fn issued_by(&self, ring: &KeyRing) -> bool {
        self.verify(&ring.authority) || ring.job_issuers.iter().any(|k| self.verify(k))
    }
    /// Signed by the controller (the authority key) itself.
    pub fn issued_by_controller(&self, ring: &KeyRing) -> bool {
        self.verify(&ring.authority)
    }
}

// ---------------------------------------------------------------- revocation

/// `vrevoke/<key>`: a validator key the controller revoked. Signed by the authority.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Revocation {
    pub key: [u8; 32],
    pub reason: String,
}

impl Pce for Revocation {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        e.bytes(&self.key).string(&self.reason);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(Revocation { key: d.fixed::<32>("key")?, reason: d.string()? })
    }
}
impl Object for Revocation {
    const DOMAIN: Domain = Domain::Revocation;
}

pub type SignedRevocation = Signed<Revocation>;

// ---------------------------------------------------------------- pins

/// Policies and checker versions a publisher accepts. Empty means none: fail closed.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct Pins {
    pub policies: Vec<Id>,
    pub checkers: Vec<Id>,
}

// ---------------------------------------------------------------- the staging rule

/// Which part of the binding failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingFault {
    /// The envelope does not verify under the controller's key.
    JobNotIssued,
    /// The receipt has no `requestID`, or it is not the envelope's ID.
    Request,
    /// The receipt or the envelope names another group.
    Group,
    Base,
    Policy,
    Checker,
    /// The receipt's `targetID` is not the envelope's target set.
    Target,
    /// The publication's target names or epochs differ from the envelope's.
    Epoch,
    PolicyNotPinned,
    CheckerNotPinned,
}

/// The P3 staging rule over signed bytes alone (no store reads; T1 adds the revocation and
/// cancellation reads). `targets` are the target names the publication was prepared under,
/// with their epochs.
pub fn check(
    receipt: &Receipt,
    job: &SignedJob,
    group: &Id,
    targets: &[PreparedTarget],
    ring: &KeyRing,
) -> std::result::Result<(), GuardFailure> {
    check_bound(receipt, job, group, targets, ring)?;
    if receipt.body.verdict != Verdict::Accepted {
        return Err(GuardFailure::ReceiptNotAccepted(*group));
    }
    Ok(())
}

/// Every part of [`check`] but the verdict: the receipt is a genuine answer to `job` about
/// `group`, accepted or rejected. The controller checks this on every receipt it records.
pub fn check_bound(
    receipt: &Receipt,
    job: &SignedJob,
    group: &Id,
    targets: &[PreparedTarget],
    ring: &KeyRing,
) -> std::result::Result<(), GuardFailure> {
    let b = &receipt.body;
    let fault = |f| Err(GuardFailure::ReceiptBinding(f));
    // (1) and (3): §6's rule.
    if b.group != *group || !ring.is_validator(&b.validator_key) || !receipt.verify(&b.validator_key) {
        return Err(GuardFailure::ReceiptRejected(*group));
    }
    // (4): the envelope and the receipt agree. An envelope binding a target must come from
    // the controller, which stamps it from the target record; issuer keys sign only
    // target-free envelopes.
    if !job.issued_by(ring) {
        return fault(BindingFault::JobNotIssued);
    }
    let j = &job.body;
    if !j.targets.is_empty() && !job.issued_by_controller(ring) && !cfg!(feature = "mutate-issuer-signs-targets") {
        return fault(BindingFault::JobNotIssued);
    }
    if b.request.as_deref() != Some(&job.id().0[..]) {
        return fault(BindingFault::Request);
    }
    if j.group != *group {
        return fault(BindingFault::Group);
    }
    if b.base != j.base {
        return fault(BindingFault::Base);
    }
    if b.policy != j.policy {
        return fault(BindingFault::Policy);
    }
    if b.validator_bin != j.checker.0 {
        return fault(BindingFault::Checker);
    }
    if b.target != target_slot(&j.targets) {
        return fault(BindingFault::Target);
    }
    // (5): pins.
    if !ring.pins.policies.contains(&j.policy) {
        return fault(BindingFault::PolicyNotPinned);
    }
    if !ring.pins.checkers.contains(&j.checker) {
        return fault(BindingFault::CheckerNotPinned);
    }
    // (6): exactly the prepared target names, each at the epoch it was prepared under.
    if !cfg!(feature = "mutate-no-epoch-binding") {
        let mut bound: Vec<(Name, u64)> = j.targets.iter().map(|t| (t.name.clone(), t.epoch)).collect();
        let mut prepared: Vec<(Name, u64)> = targets.iter().map(|t| (t.name.clone(), t.epoch)).collect();
        bound.sort();
        prepared.sort();
        if bound != prepared {
            return fault(BindingFault::Epoch);
        }
    }
    Ok(())
}

/// Prepared targets equal to a job's own bindings (for checks after publication, where T1
/// already fenced the epochs).
pub fn prepared_of(job: &SignedJob) -> Vec<PreparedTarget> {
    job.body.targets.iter().map(|t| PreparedTarget { name: t.name.clone(), epoch: t.epoch, head: None }).collect()
}

// ---------------------------------------------------------------- keys

impl Keys {
    /// `job/<envelope id>`: the signed envelope a published receipt names (written by T1).
    pub fn job(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("job", foundationdb::tuple::Bytes::from(&id.0[..])))
    }
    /// `jobreq/<request>`: the envelope the controller issued for a request (deduplication).
    pub fn job_request(&self, request: &[u8]) -> Vec<u8> {
        self.root.pack(&("jobreq", foundationdb::tuple::Bytes::from(request)))
    }
    /// `jobreceipt/<request>`: the receipt a validator returned for a request.
    pub fn job_receipt(&self, request: &[u8]) -> Vec<u8> {
        self.root.pack(&("jobreceipt", foundationdb::tuple::Bytes::from(request)))
    }
    /// `jobcancel/<request>`: present iff the request was cancelled.
    pub fn job_cancel(&self, request: &[u8]) -> Vec<u8> {
        self.root.pack(&("jobcancel", foundationdb::tuple::Bytes::from(request)))
    }
    /// `vrevoke/<validator key>`: a signed revocation.
    pub fn revocation(&self, key: &[u8; 32]) -> Vec<u8> {
        self.root.pack(&("vrevoke", foundationdb::tuple::Bytes::from(&key[..])))
    }
}

// ---------------------------------------------------------------- P3 transactions

/// Outcome of a write-once transaction: the value now stored under the key, and whether
/// this call wrote it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Once {
    pub value: Vec<u8>,
    pub fresh: bool,
}

impl Meta {
    /// Write `value` under `key` unless the key holds a value; idempotent, returns what is
    /// stored. The P3 job records are all write-once:
    ///
    /// | # | Transaction | Key |
    /// |---|---|---|
    /// | J1 | issue an envelope for a request (retry deduplication) | `jobreq/<request>` |
    /// | J2 | record the receipt a validator returned for a request | `jobreceipt/<request>` |
    /// | J3 | cancel a request | `jobcancel/<request>` |
    /// | R1 | revoke a validator key | `vrevoke/<key>` |
    ///
    /// None of them is read by T2–T7; T1 reads J3 and R1 keys in its own transaction.
    pub async fn put_once(&self, key: Vec<u8>, value: Vec<u8>) -> Result<Once> {
        let (key, value) = (Arc::new(key), Arc::new(value));
        self.run(
            Txn::P3Job,
            Box::new(move |trx| {
                let (key, value) = (key.clone(), value.clone());
                Box::pin(async move {
                    if let Some(v) = crate::meta::get(trx, &key).await? {
                        return Ok(Step::Done(Once { value: v, fresh: false }));
                    }
                    trx.set(&key, &value);
                    Ok(Step::Commit(Once { value: (*value).clone(), fresh: true }))
                })
            }),
        )
        .await
    }

    /// J1: the envelope stored for `request`, writing `job` if there is none.
    pub async fn issue_job(&self, job: &SignedJob) -> Result<SignedJob> {
        let o = self.put_once(self.keys.job_request(&job.body.request), job.to_bytes()).await?;
        Ok(SignedJob::from_bytes(&o.value)?)
    }

    /// J2: the receipt stored for `request`, writing `receipt` if there is none.
    pub async fn record_receipt(&self, request: &[u8], receipt: &Receipt) -> Result<Receipt> {
        let o = self.put_once(self.keys.job_receipt(request), receipt.to_bytes()).await?;
        Ok(Receipt::from_bytes(&o.value)?)
    }

    /// J3: cancel `request`. Every later T1 with a receipt bound to it aborts.
    pub async fn cancel_job(&self, request: &[u8]) -> Result<bool> {
        Ok(self.put_once(self.keys.job_cancel(request), vec![1]).await?.fresh)
    }

    /// R1: revoke a validator key. Every later T1 with a receipt by that key aborts.
    pub async fn revoke_validator(&self, r: &SignedRevocation) -> Result<bool> {
        Ok(self.put_once(self.keys.revocation(&r.body.key), r.to_bytes()).await?.fresh)
    }

    pub async fn is_cancelled(&self, request: &[u8]) -> Result<bool> {
        Ok(self.get(self.keys.job_cancel(request)).await?.is_some())
    }

    pub async fn is_revoked(&self, key: &[u8; 32]) -> Result<bool> {
        Ok(self.get(self.keys.revocation(key)).await?.is_some())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sign::Signer;

    #[test]
    fn envelope_roundtrip_and_strictness() {
        let mut targets = vec![
            TargetBinding { name: Name::parse("B.t"), epoch: 3, statement: vec![1; 32] },
            TargetBinding { name: Name::parse("A.t"), epoch: 1, statement: vec![] },
        ];
        sort_targets(&mut targets);
        let j = JobEnvelope {
            request: b"r1".to_vec(),
            group: Id([1; 32]),
            capsule: Id([2; 32]),
            deps: vec![Id([4; 32]), Id([3; 32])],
            base: Id([5; 32]),
            policy: Policy::v1().id(),
            checker: CheckerVersion::fixture().id(),
            worker: WorkspaceId::derive("w"),
            targets: targets.clone(),
            deadline_ms: 1000,
            memory_mb: 512,
        };
        assert_eq!(JobEnvelope::from_pce(&j.to_pce()).unwrap(), j);
        let s = SignedJob::sign(j.clone(), &Signer::derive("authority"));
        assert_eq!(SignedJob::from_bytes(&s.to_bytes()).unwrap(), s);
        assert_eq!(decode_target_slot(&target_slot(&targets)).unwrap(), targets);
        // Unsorted target sets do not decode.
        let mut e = Enc::new();
        e.uvarint(2);
        targets[1].encode(&mut e);
        targets[0].encode(&mut e);
        assert!(decode_target_slot(&Some(e.out)).is_err());
        // Issuer keys: a pure signature check; target envelopes need the authority.
        let issuer = Signer::derive("issuer");
        let mut ring = KeyRing { authority: Signer::derive("authority").public(), ..Default::default() };
        let by_issuer = SignedJob::sign(j.clone(), &issuer);
        assert!(!by_issuer.issued_by(&ring));
        ring.job_issuers.push(issuer.public());
        assert!(by_issuer.issued_by(&ring) && !by_issuer.issued_by_controller(&ring));
        assert!(s.issued_by(&ring) && s.issued_by_controller(&ring));
        // Domains are distinct.
        assert_ne!(Policy::v1().id(), Domain::Job.hash(&Policy::v1().to_pce()));
    }
}
