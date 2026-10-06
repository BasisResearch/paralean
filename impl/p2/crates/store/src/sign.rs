//! Ed25519 signing keys and the trusted key ring.
//!
//! Signatures cover the object's ID, `H(domain, body)` (§6, §8.3, §9). Certificates are
//! signed by their writer so a repair (T7) cannot forge one; tokens are signed by the fence
//! authority; receipts by a validator; catalogue records and commit certificates by the
//! token holder.

use std::collections::BTreeMap;

use ed25519_dalek::{Signature, Signer as _, SigningKey, Verifier, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::id::{sha256, Id, WorkspaceId};

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
    vk.verify(&id.0, &Signature::from_bytes(&sig)).is_ok()
}

/// Public keys the store trusts. Writers unknown to the ring are ignored by discovery and
/// recovery (their certificates count as absent).
#[derive(Clone, Default, Debug)]
pub struct KeyRing {
    pub authority: [u8; 32],
    pub validators: Vec<[u8; 32]>,
    pub writers: BTreeMap<WorkspaceId, [u8; 32]>,
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
}

/// A key file: seeds for the fence authority, validators and workspaces. The CLI reads it
/// from `$PARALEAN_KEYS`. Holding a seed is holding that role.
#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct KeyFile {
    pub authority: Option<String>,
    pub authority_public: String,
    pub validators: BTreeMap<String, KeyEntry>,
    pub workspaces: BTreeMap<String, KeyEntry>,
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
        let auth = Signer::derive("authority");
        let val = Signer::derive("validator");
        let mut kf = KeyFile {
            authority: Some(hex::encode(auth.seed())),
            authority_public: hex::encode(auth.public()),
            ..Default::default()
        };
        kf.validators.insert(
            "v0".into(),
            KeyEntry { id: String::new(), public: hex::encode(val.public()), seed: Some(hex::encode(val.seed())) },
        );
        for i in 0..n {
            let name = format!("w{i}");
            let s = Signer::derive(&name);
            kf.workspaces.insert(
                name.clone(),
                KeyEntry {
                    id: WorkspaceId::derive(&name).hex(),
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
    pub fn workspace(&self, name: &str) -> Option<(WorkspaceId, Signer)> {
        let e = self.workspaces.get(name)?;
        Some((WorkspaceId::from_hex(&e.id)?, Self::seed_of(e)?))
    }
}
