//! Receipts and job envelopes (p0-interfaces §6, §10): the format and staging rule are
//! P3 control's `paralean_store::receipt`; validators are its `paralean-p3 validator`
//! service, reached through `paralean_validator_api`.
//!
//! Working copies issue the envelope of each check themselves, signed with their own
//! job-issuer key, for groups that realise no target (P3 control's controller issues
//! envelopes for target jobs). The envelope pins the group, its capsule, the capsules of its
//! exact dependency closure, the base, policy v1 and the pinned checker version.

use std::time::Duration;

use paralean_control::checker::{base_id, CheckerConfig};
use paralean_store::receipt::{CheckerVersion, JobEnvelope, Policy, SignedJob};
use paralean_store::{Id, KeyFile, Object, Receipt, Signed, Signer, WorkspaceId};
use paralean_validator_api::{decode_receipt, ValidatorRequest, ValidatorResponse};

/// This machine's checker version (impl/p1's `paralean`, `PARALEAN_LEAN`).
pub fn checker() -> Result<CheckerVersion, String> {
    CheckerConfig::from_env()?.version()
}

pub fn base() -> Result<Id, String> {
    Ok(base_id(&CheckerConfig::from_env()?.lean_githash))
}

/// A controller-signed envelope for checking `group` (with `capsule` and the dependency
/// capsules `deps`, dependencies first), bound to the atomic batch `batch` if any.
/// The envelope is signed with the working copy's job-issuer key (`KeyFile::job_issuers`,
/// P3 control's `SignedJob::issued_by`), never the authority key: issuer-signed envelopes may
/// name no target, so target jobs still go through the controller. `issuer` names the key
/// (a working copy's agent name); without an issuer seed the authority seed is used, which
/// only the controller and the forgery tests' rogue key files hold.
pub fn issue(kf: &KeyFile, issuer: &str, worker: WorkspaceId, group: Id, capsule: Id, deps: Vec<Id>,
    batch: Option<Id>) -> Result<SignedJob, String> {
    let auth = kf.job_issuer_signer(issuer).or_else(|| kf.authority_signer())
        .ok_or("the key file holds neither a job-issuer seed for this copy nor the controller seed")?;
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
        batch,
    };
    Ok(Signed::sign(job, &auth))
}

/// Send dependency-ordered envelopes, all signed by `signer`, to a validator as one batch:
/// an earlier accepted receipt serves a later job's dependency. One result per job.
pub async fn validate_batch(addr: &str, jobs: &[SignedJob], signer: &Signer, validator_keys: &[[u8; 32]])
    -> Result<Vec<Result<Receipt, String>>, String> {
    let req = ValidatorRequest::ValidateBatch { jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect() };
    let resp: ValidatorResponse = paralean_validator_api::rpc::call_authenticated_any(addr, &req, signer, validator_keys, Duration::from_secs(3600))
        .await.map_err(|e| format!("validator {addr}: {e}"))?;
    match resp {
        ValidatorResponse::Batch { responses } if responses.len() == jobs.len() => Ok(responses.into_iter().map(|r| match r {
            ValidatorResponse::Receipt { receipt } => decode_receipt(&receipt),
            other => Err(format!("no receipt: {other:?}")),
        }).collect()),
        other => Err(format!("validator {addr} gave no batch answer: {other:?}")),
    }
}

/// Send the envelope to a validator and return its receipt (accepted or rejected).
pub async fn validate(addr: &str, job: &SignedJob, signer: &Signer, validator_keys: &[[u8; 32]]) -> Result<Receipt, String> {
    match paralean_validator_api::validate(addr, job, signer, validator_keys, Duration::from_secs(1800)).await.map_err(|e| format!("validator {addr}: {e}"))? {
        ValidatorResponse::Receipt { receipt } => decode_receipt(&receipt),
        other => Err(format!("validator {addr} gave no receipt: {other:?}")),
    }
}
