//! Ed25519 signing keys and the trusted key ring.
//!
//! Signatures cover the object's ID, `H(domain, body)` (§6, §8.3, §9). Certificates are
//! signed by their writer so a repair (T7) cannot forge one; tokens are signed by the fence
//! authority; receipts by a validator; catalogue records and commit certificates by the
//! token holder.

use std::collections::BTreeMap;

use ed25519_dalek::{Signature, Signer as _, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::id::{sha256, Id, WorkspaceId};
use crate::objects::Object;
use crate::receipt::{CheckerVersion, Pins, Policy};

#[derive(Clone)]
pub struct Signer {
    key: SigningKey,
}

impl Signer {
    pub fn from_seed(seed: [u8; 32]) -> Self {
        Signer { key: SigningKey::from_bytes(&seed) }
    }
    /// Deterministic key from a label (tests, fixtures and the demo key set).
    pub fn derive(label: &str) -> Self {
        Signer::from_seed(sha256(format!("paralean-p2-test-key/{label}").as_bytes()))
    }
    pub fn generate() -> Self {
        Signer::from_seed(rand::random())
    }
    pub fn seed(&self) -> [u8; 32] {
        self.key.to_bytes()
    }
    pub fn public(&self) -> [u8; 32] {
        self.key.verifying_key().to_bytes()
    }
    pub fn sign(&self, id: &Id) -> [u8; 64] {
        self.key.sign(&id.0).to_bytes()
    }
}

pub fn verify(public: &[u8; 32], id: &Id, sig: &[u8]) -> bool {
    let Ok(vk) = VerifyingKey::from_bytes(public) else { return false };
    let Ok(sig) = <[u8; 64]>::try_from(sig) else { return false };
    if cfg!(feature = "mutate-weak-signature") {
        ed25519_dalek::Verifier::verify(&vk, &id.0, &Signature::from_bytes(&sig)).is_ok()
    } else {
        paralean_crypto::verify(public, &id.0, &sig)
    }
}

/// Public keys the store trusts. Writers unknown to the ring are ignored by discovery and
/// recovery (their certificates count as absent).
#[derive(Clone, Default, Debug)]
pub struct KeyRing {
    pub authority: [u8; 32],
    pub validators: Vec<[u8; 32]>,
    pub writers: BTreeMap<WorkspaceId, [u8; 32]>,
    /// Policies and checker versions receipts may name (P3 staging rule).
    pub pins: Pins,
    /// Keys that may sign job envelopes besides the authority (working copies issuing
    /// envelopes for non-target groups). They never sign tokens or revocations.
    pub job_issuers: Vec<[u8; 32]>,
}

impl KeyRing {
    pub fn writer(&self, w: &WorkspaceId) -> Option<&[u8; 32]> {
        self.writers.get(w)
    }
    pub fn verify_writer(&self, w: &WorkspaceId, id: &Id, sig: &[u8]) -> bool {
        self.writer(w).is_some_and(|k| verify(k, id, sig))
    }
    pub fn verify_authority(&self, id: &Id, sig: &[u8]) -> bool {
        verify(&self.authority, id, sig)
    }
    pub fn is_validator(&self, k: &[u8; 32]) -> bool {
        self.validators.contains(k)
    }
    /// Also trust another deployment's writers and validators (anti-entropy peers), and its
    /// controller and job issuers as issuers of target-free job envelopes, so that its
    /// receipts can pass this deployment's staging rule. Its fence authority is not trusted
    /// as an authority: fences, target epochs and revocations are per deployment, so an
    /// envelope binding a target never passes here (`receipt::check`). Pins are not merged:
    /// the policies and checkers a deployment accepts are its own.
    pub fn trust(&mut self, peer: &KeyRing) {
        for (w, k) in &peer.writers {
            self.writers.entry(*w).or_insert(*k);
        }
        for v in &peer.validators {
            if !self.validators.contains(v) {
                self.validators.push(*v);
            }
        }
        for k in std::iter::once(&peer.authority).chain(&peer.job_issuers) {
            if *k != self.authority && !self.job_issuers.contains(k) {
                self.job_issuers.push(*k);
            }
        }
    }
}

/// A key file: seeds for the fence authority, validators and workspaces. The CLI reads it
/// from `$PARALEAN_KEYS`. Holding a seed is holding that role.
#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct KeyFile {
    pub authority: Option<String>,
    pub authority_public: String,
    pub validators: BTreeMap<String, KeyEntry>,
    pub workspaces: BTreeMap<String, KeyEntry>,
    /// Pinned policy IDs (hex). Receipts naming another policy are refused.
    #[serde(default)]
    pub policies: Vec<String>,
    /// Pinned checker-version IDs (hex).
    #[serde(default)]
    pub checkers: Vec<String>,
    /// Job-envelope issuer keys (`KeyRing::job_issuers`); a working copy holds one of these
    /// seeds, never the authority seed.
    #[serde(default)]
    pub job_issuers: BTreeMap<String, KeyEntry>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
pub struct KeyEntry {
    /// Workspace ID (hex, 16 bytes); empty for validators.
    #[serde(default)]
    pub id: String,
    pub public: String,
    #[serde(default)]
    pub seed: Option<String>,
}

impl KeyFile {
    /// A deterministic key set with `n` workspaces named `w0..w{n-1}` and one validator.
    pub fn demo(n: usize) -> KeyFile {
        KeyFile::demo_prefixed("", n)
    }

    /// As `demo`, with authority and workspace keys and IDs derived under `prefix`, so two
    /// deployments get distinct identities (the validator is shared).
    pub fn demo_prefixed(prefix: &str, n: usize) -> KeyFile {
        let auth = Signer::derive(&format!("{prefix}authority"));
        let val = Signer::derive("validator");
        let mut kf = KeyFile {
            authority: Some(hex::encode(auth.seed())),
            authority_public: hex::encode(auth.public()),
            policies: vec![Policy::v1().id().hex()],
            checkers: vec![CheckerVersion::fixture().id().hex()],
            ..Default::default()
        };
        kf.validators.insert(
            "v0".into(),
            KeyEntry { id: String::new(), public: hex::encode(val.public()), seed: Some(hex::encode(val.seed())) },
        );
        for i in 0..n {
            let name = format!("w{i}");
            let s = Signer::derive(&format!("{prefix}{name}"));
            kf.workspaces.insert(
                name.clone(),
                KeyEntry {
                    id: WorkspaceId::derive(&format!("{prefix}{name}")).hex(),
                    public: hex::encode(s.public()),
                    seed: Some(hex::encode(s.seed())),
                },
            );
        }
        kf
    }

    pub fn ring(&self) -> KeyRing {
        let pk = |s: &str| -> [u8; 32] { hex::decode(s).ok().and_then(|v| v.try_into().ok()).unwrap_or([0; 32]) };
        KeyRing {
            authority: pk(&self.authority_public),
            validators: self.validators.values().map(|e| pk(&e.public)).collect(),
            writers: self
                .workspaces
                .values()
                .filter_map(|e| Some((WorkspaceId::from_hex(&e.id)?, pk(&e.public))))
                .collect(),
            pins: Pins {
                policies: self.policies.iter().filter_map(|h| Id::from_hex(h)).collect(),
                checkers: self.checkers.iter().filter_map(|h| Id::from_hex(h)).collect(),
            },
            job_issuers: self.job_issuers.values().map(|e| pk(&e.public)).collect(),
        }
    }

    fn seed_of(e: &KeyEntry) -> Option<Signer> {
        let s = hex::decode(e.seed.as_ref()?).ok()?;
        Some(Signer::from_seed(s.try_into().ok()?))
    }
    pub fn authority_signer(&self) -> Option<Signer> {
        let s = hex::decode(self.authority.as_ref()?).ok()?;
        Some(Signer::from_seed(s.try_into().ok()?))
    }
    pub fn validator_signer(&self, name: &str) -> Option<Signer> {
        Self::seed_of(self.validators.get(name)?)
    }
    /// Add a validator key (rotation: the old key stays trusted until it is removed or
    /// revoked). Returns its signer.
    pub fn add_validator(&mut self, name: &str, signer: &Signer) {
        self.validators.insert(
            name.into(),
            KeyEntry { id: String::new(), public: hex::encode(signer.public()), seed: Some(hex::encode(signer.seed())) },
        );
    }
    /// Add a job-envelope issuer key.
    pub fn add_job_issuer(&mut self, name: &str, signer: &Signer) {
        self.job_issuers.insert(
            name.into(),
            KeyEntry { id: String::new(), public: hex::encode(signer.public()), seed: Some(hex::encode(signer.seed())) },
        );
    }
    pub fn job_issuer_signer(&self, name: &str) -> Option<Signer> {
        Self::seed_of(self.job_issuers.get(name)?)
    }
    /// Retire a validator key: remove it from the configured set.
    pub fn retire_validator(&mut self, name: &str) -> Option<KeyEntry> {
        self.validators.remove(name)
    }
    pub fn workspace(&self, name: &str) -> Option<(WorkspaceId, Signer)> {
        let e = self.workspaces.get(name)?;
        Some((WorkspaceId::from_hex(&e.id)?, Self::seed_of(e)?))
    }
}

#[cfg(test)]
mod security_tests {
    use super::*;
    #[test]
    fn weak_public_key_identity_signature_is_rejected() {
        // Identity R, identity A, zero S satisfies the relaxed verification
        // equation for every message but is not an acceptable Ed25519 signature.
        let mut public = [0; 32]; public[0] = 1;
        let mut sig = [0; 64]; sig[0] = 1;
        let mut order_two = [0xff; 32]; order_two[0] = 0xfe; order_two[31] = 0x7f;
        for key in [public, [0; 32], order_two] {
            assert!(!verify(&key, &Id([7; 32]), &sig));
        }
        let signer = Signer::generate();
        assert!(verify(&signer.public(), &Id([7; 32]), &signer.sign(&Id([7; 32]))));
    }
}
