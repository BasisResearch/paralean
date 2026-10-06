//! Receipts and job envelopes (p0-interfaces §6, §10): the format and staging rule are
//! P3 control's `paralean_store::receipt`; validators are its `paralean-p3 validator`
//! service, reached through `paralean_validator_api`.
//!
//! Working copies issue the envelope of each check themselves, signed with the controller
//! (fence authority) key, for groups that realise no target (P3 control's controller issues
//! envelopes for target jobs). The envelope pins the group, its capsule, the capsules of its
//! exact dependency closure, the base, policy v1 and the pinned checker version.

use std::time::Duration;

use paralean_control::checker::{base_id, CheckerConfig};
use paralean_store::receipt::{CheckerVersion, JobEnvelope, Policy, SignedJob};
use paralean_store::{Id, KeyFile, Object, Receipt, Signed, WorkspaceId};
use paralean_validator_api::{decode_receipt, ValidatorResponse};

/// This machine's checker version (impl/p1's `paralean`, `PARALEAN_LEAN`).
pub fn checker() -> Result<CheckerVersion, String> {
    CheckerConfig::from_env()?.version()
}

pub fn base() -> Result<Id, String> {
    Ok(base_id(&CheckerConfig::from_env()?.lean_githash))
}

/// A controller-signed envelope for checking `group` (with `capsule` and the dependency
/// capsules `deps`, dependencies first).
pub fn issue(kf: &KeyFile, worker: WorkspaceId, group: Id, capsule: Id, deps: Vec<Id>) -> Result<SignedJob, String> {
    let auth = kf.authority_signer().ok_or("the key file holds no controller (authority) seed")?;
    let checker = kf.checkers.first().and_then(|h| Id::from_hex(h)).ok_or("no pinned checker in the key file")?;
    let job = JobEnvelope {
        request: rand::random::<[u8; 16]>().to_vec(),
        group,
        capsule,
        deps,
        base: base()?,
        policy: Policy::v1().id(),
        checker,
        worker,
        targets: vec![],
        deadline_ms: 1_800_000,
        memory_mb: 0,
    };
    Ok(Signed::sign(job, &auth))
}

/// Send the envelope to a validator and return its receipt (accepted or rejected).
pub async fn validate(addr: &str, job: &SignedJob) -> Result<Receipt, String> {
    match paralean_validator_api::validate(addr, job, Duration::from_secs(1800)).await.map_err(|e| format!("validator {addr}: {e}"))? {
        ValidatorResponse::Receipt { receipt } => decode_receipt(&receipt),
        other => Err(format!("validator {addr} gave no receipt: {other:?}")),
    }
}
