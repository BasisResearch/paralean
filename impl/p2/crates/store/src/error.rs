//! Errors. A `Guard` error means the transaction's guard rejected it and nothing was written
//! (the abstract "aborted transaction corresponds to no write").

use thiserror::Error;

use crate::id::{Id, Kind};
use crate::objects::Name;
use crate::pce::DecodeError;

/// Why a transaction's guard aborted it. Each variant names the Lean/TLA guard it enforces.
#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum GuardFailure {
    // --- T1 (TargetNames PrepareOk/PublishOk, AckCertificates PublishWrite, §8.2)
    #[error("no target record for {0}")]
    NoTargetRecord(Name),
    #[error("not the owner of {name}")]
    NotOwner { name: Name },
    #[error("stale epoch for {name}: prepared under {prepared}, record has {current}")]
    StaleEpoch { name: Name, prepared: u64, current: u64 },
    #[error("head of {name} moved: prepared against {prepared:?}, record has {current:?}")]
    HeadMoved { name: Name, prepared: Option<Id>, current: Option<Id> },
    #[error("revision for {0} does not revise the recorded head")]
    NotRevisingHead(Name),
    #[error("package has no revision for target name {0}")]
    MissingTargetRevision(Name),
    #[error("the job's statement for target {0} is not the pinned statement")]
    TargetStatement(Name),
    #[error("group {group:?} already published with marker {existing:?}")]
    AlreadyPublished { group: Id, existing: Id },
    #[error("parent revision {0:?} is not admitted (absent from the store)")]
    UnknownParentRevision(Id),
    #[error("package is inconsistent: {0}")]
    BadPackage(String),
    #[error("receipt does not admit group {0:?} (PublicationReceipts staging rule)")]
    ReceiptRejected(Id),
    // --- P3 receipt binding (receipt.rs; OPEN-7)
    #[error("receipt for {0:?} is not an acceptance")]
    ReceiptNotAccepted(Id),
    #[error("receipt binding: {0:?}")]
    ReceiptBinding(crate::receipt::BindingFault),
    #[error("validator key {} is revoked", hex::encode(.0))]
    ValidatorRevoked([u8; 32]),
    #[error("request {} was cancelled", hex::encode(.0))]
    JobCancelled(Vec<u8>),
    #[error("revision names target {0} without a prepared target")]
    UndeclaredTarget(Name),
    // --- T2 (AckCertificates put: writer knows the group as published)
    #[error("group {0:?} is not published")]
    NotPublished(Id),
    #[error("group {0:?} has no live certificate (a raw marker is not discovery evidence)")]
    Uncertified(Id),
    // --- T3/T4
    #[error("rank {0} already issued to another request")]
    RankTaken(u64),
    // --- T5 (CatalogFencing first write, CatalogCertificates CertStep.record)
    #[error("stale token: record rank {rank}, fence {fence}")]
    StaleToken { rank: u64, fence: u64 },
    #[error("token rank {0} was never issued, or names another holder")]
    TokenNotIssued(u64),
    #[error("manifest (snapshot) {0:?} has no object certificate")]
    ManifestUncertified(Id),
    #[error("parent record {0:?} is not committed")]
    ParentUncommitted(Id),
    #[error("checkpoint snapshot {0:?} is missing or corrupt")]
    CheckpointSnapshotMissing(Id),
    #[error("checkpoint selects two groups declaring {0}")]
    CheckpointDuplicateName(Name),
    #[error("checkpoint includes only part of atomic group {0:?}")]
    CheckpointPartialGroup(Id),
    #[error("checkpoint group {group:?} omits dependency capsule {capsule:?}")]
    CheckpointDependencyMissing { group: Id, capsule: Id },
    #[error("checkpoint group {group:?} is not the sole live head for {name}")]
    CheckpointNotCurrent { group: Id, name: Name },
    #[error("checkpoint registry metadata is too large or cannot be decoded in one transaction")]
    CheckpointRegistryUnreadable,
    #[error("catalog key holds different bytes")]
    RecordMismatch,
    // --- T6
    #[error("object {kind:?} {id:?} is not acknowledged by the payload store")]
    NotAcknowledged { kind: Kind, id: Id },
    // --- T8 (tombstone publication, §11.4; Workspaces: a tombstone is a revision of its
    // target, so the target is published and older, in the same file, by its author)
    #[error("tombstone {tombstone:?} already stored without this writer's certificate")]
    TombstoneExists { tombstone: Id },
    #[error("tombstone names file {tombstone} but its target is in {target}")]
    TombstoneFileMismatch { tombstone: String, target: String },
    #[error("tombstone lamport {lamport} does not exceed its target's {target}")]
    TombstoneNotNewer { lamport: u64, target: u64 },
    #[error("tombstone author is not the target's author (OPEN-19 v0 default)")]
    TombstoneNotAuthor,
    #[error("agent {0} has no active controller-registered key for this certificate")]
    AgentKeyNotRegistered(String),
    #[error("agent key {} is revoked", hex::encode(.0))]
    AgentKeyRevoked([u8; 32]),
    #[error("controller deletion grant is invalid or fenced out")]
    ControllerDeleteDenied,
    #[error("target group declares target name {0}; TargetNames has no deletion")]
    TombstoneOfTarget(Name),
    #[error("tombstone names receipt {0:?}, absent from the store")]
    TombstoneReceiptAbsent(Id),
    // --- T9/T10 (anti-entropy receive)
    #[error("group {group:?} is published here with marker {local:?}, the sender's is {remote:?}")]
    MarkerConflict { group: Id, local: Id, remote: Id },
    #[error("received object fails verification: {0}")]
    ReceiveInvalid(String),
    #[error("received group declares {0}, a target name homed at this deployment")]
    ForeignTarget(Name),
    // --- T7 (certificate repair: existing bytes only, signed)
    #[error("repair source has no such certificate")]
    RepairSourceMissing,
    #[error("repair copy invalid: {0}")]
    RepairInvalid(String),
    #[error("repair target lacks the certified object's bytes")]
    RepairNoExistingBytes,
    // --- T12/T13 (atomic multi-group publication; docs/atomic-pub-log.md)
    #[error("{0:?} is bound to another batch, or a batch member was submitted alone")]
    BatchBinding(Id),
    #[error("batch intent: {0}")]
    BatchIntent(String),
    #[error("batch {0:?} is already recorded with other member bytes")]
    BatchConflict(Id),
    #[error("batch exceeds the single-transaction budget: {0}")]
    BatchTooLarge(String),
}

#[derive(Debug, Error)]
pub enum StoreError {
    #[error("guard: {0}")]
    Guard(#[from] GuardFailure),
    #[error("foundationdb: {0}")]
    Fdb(#[from] foundationdb::FdbError),
    #[error("s3: {0}")]
    S3(String),
    #[error("decode: {0}")]
    Decode(#[from] DecodeError),
    #[error("missing {kind}: {id}")]
    Missing { kind: &'static str, id: Id },
    #[error("injected crash at {0}")]
    Crashed(String),
    #[error("outcome unresolved after {attempts} attempts: {last}")]
    Unresolved { attempts: usize, last: String },
    #[error("{0}")]
    Invalid(String),
}

pub type Result<T> = std::result::Result<T, StoreError>;

impl StoreError {
    pub fn guard(&self) -> Option<&GuardFailure> {
        match self {
            StoreError::Guard(g) => Some(g),
            _ => None,
        }
    }
    pub fn is_crash(&self) -> bool {
        matches!(self, StoreError::Crashed(_))
    }
}
