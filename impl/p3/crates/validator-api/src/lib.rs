//! The P3 validator API.
//!
//! A validator is a service holding an Ed25519 key from the configured validator set. It
//! takes an immutable, controller-signed job envelope ([`SignedJob`], domain `v0/job`),
//! re-checks the group from its exact dependency closure with the stock kernel (or the
//! Paralean fork in validator mode) and returns a signed receipt bound to the envelope (the
//! format and the staging rule are `paralean_store::receipt`; p0-interfaces §6, OPEN-7).
//!
//! | Item | Use |
//! |---|---|
//! | [`ValidatorRequest`], [`ValidatorResponse`] | wire types (JSON frames, [`rpc`]) |
//! | [`validate`] | client call: envelope in, receipt or a reason out |
//! | [`published_receipt`] | consumers (`remote%`, validators checking dependencies): the receipt of a published group, re-verified |
//!
//! Responses are fail-closed. Only [`ValidatorResponse::Receipt`] carries a receipt; its
//! verdict may still be `rejected`. A timeout, an exceeded memory limit, a crash of the
//! checker or unavailable bytes give [`ValidatorResponse::Inconclusive`] and no receipt
//! ("timeout/unavailable bytes are inconclusive", architecture.md).

pub mod rpc;

use std::time::Duration;

use paralean_store::receipt::{check, SignedJob};
use paralean_store::{GuardFailure, Id, Receipt, Store, StoreError};
use serde::{Deserialize, Serialize};

pub use paralean_store::receipt;

/// A request to a validator. Byte strings are lowercase hex.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(tag = "op", rename_all = "snake_case")]
pub enum ValidatorRequest {
    /// Check the job's group. `job` is the `Signed<JobEnvelope>` bytes.
    Validate { job: String },
    /// Stop a running or queued check of this request (its checker process is killed).
    Cancel { request: String },
    Status,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "result", rename_all = "snake_case")]
pub enum ValidatorResponse {
    /// A signed receipt (`Signed<ReceiptBody>` bytes), accepted or rejected.
    Receipt { receipt: String },
    /// No verdict: deadline passed, memory limit hit, checker crashed, inputs unavailable.
    Inconclusive { reason: String },
    /// The envelope is not one this validator checks (signature, checker version, policy,
    /// base, revoked key, cancelled request, dependency not published).
    Refused { reason: String },
    /// The validator's queue is full; retry later or elsewhere.
    Busy,
    /// The request was cancelled while queued or running.
    Cancelled,
    Status {
        key: String,
        checker: String,
        running: usize,
        queued: usize,
        checks_run: u64,
    },
}

/// Send an envelope to the validator at `addr`.
pub async fn validate(addr: &str, job: &SignedJob, timeout: Duration) -> std::io::Result<ValidatorResponse> {
    rpc::call(addr, &ValidatorRequest::Validate { job: hex::encode(job.to_bytes()) }, timeout).await
}

/// Decode a receipt returned by [`validate`].
pub fn decode_receipt(hex_bytes: &str) -> Result<Receipt, String> {
    let b = hex::decode(hex_bytes).map_err(|e| e.to_string())?;
    Receipt::from_bytes(&b).map_err(|e| e.to_string())
}

/// Why a published group's receipt does not verify.
#[allow(dead_code)]
#[derive(Debug)]
pub enum PublishedReceiptError {
    NotPublished,
    Store(StoreError),
    Missing(&'static str),
    Binding(GuardFailure),
    Revoked,
}

/// The receipt and envelope of a published group, re-verified against the store's key ring
/// (signature, acceptance, binding, pins) and the store's revocations. Target epochs are
/// checked against the envelope's own target set: T1 fenced them at publication.
pub async fn published_receipt(store: &Store, group: &Id) -> Result<(Receipt, SignedJob), PublishedReceiptError> {
    use PublishedReceiptError as E;
    let (_, marker) = store.marker(group).await.map_err(E::Store)?.ok_or(E::NotPublished)?;
    // Published means certified (§8.3): a marker key alone is not evidence.
    let certs = store.meta.scan(&store.meta.keys.certs_of(group), 16, |_| None).await.map_err(E::Store)?;
    if certs.is_empty() {
        return Err(E::NotPublished);
    }
    let rc = store.receipt(&marker.receipt).await.map_err(E::Store)?.ok_or(E::Missing("receipt"))?;
    let jid = rc.body.request.as_ref().and_then(|q| <[u8; 32]>::try_from(&q[..]).ok()).ok_or(E::Missing("request"))?;
    let jv = store.meta.get(store.meta.keys.job(&Id(jid))).await.map_err(E::Store)?.ok_or(E::Missing("job envelope"))?;
    let job = SignedJob::from_bytes(&jv).map_err(|e| E::Store(e.into()))?;
    if job.id() != Id(jid) {
        return Err(E::Missing("job envelope with that ID"));
    }
    check(&rc, &job, group, &receipt::prepared_of(&job), &store.ring).map_err(E::Binding)?;
    if store.meta.get(store.meta.keys.revocation(&rc.body.validator_key)).await.map_err(E::Store)?.is_some() {
        return Err(E::Revoked);
    }
    Ok((rc, job))
}
