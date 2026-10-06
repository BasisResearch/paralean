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
    #[error("group {group:?} already published with marker {existing:?}")]
    AlreadyPublished { group: Id, existing: Id },
    #[error("parent revision {0:?} is not admitted (absent from the store)")]
    UnknownParentRevision(Id),
    #[error("package is inconsistent: {0}")]
    BadPackage(String),
    #[error("receipt does not admit group {0:?} (PublicationReceipts staging rule)")]
    ReceiptRejected(Id),
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
    #[error("catalog key holds different bytes")]
    RecordMismatch,
    // --- T6
    #[error("object {kind:?} {id:?} is not acknowledged by the payload store")]
    NotAcknowledged { kind: Kind, id: Id },
    // --- T7 (certificate repair: existing bytes only, signed)
    #[error("repair source has no such certificate")]
    RepairSourceMissing,
    #[error("repair copy invalid: {0}")]
    RepairInvalid(String),
    #[error("repair target lacks the certified object's bytes")]
    RepairNoExistingBytes,
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
