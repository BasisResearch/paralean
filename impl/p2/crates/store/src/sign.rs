//! Ed25519 signing keys and the trusted key ring.
//!
//! Signatures cover the object's ID, `H(domain, body)` (§6, §8.3, §9). Certificates are
//! signed by their writer so a repair (T7) cannot forge one; tokens are signed by the fence
//! authority; receipts by a validator; catalogue records and commit certificates by the
//! token holder.

use std::collections::{BTreeMap, BTreeSet};

use ed25519_dalek::{Signature, Signer as _, SigningKey, VerifyingKey};
use serde::{Deserialize, Serialize};

use crate::id::{sha256, Id, WorkspaceId};
use crate::authority::AgentKeyGrant;
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
    verify_path(cfg!(feature = "mutate-weak-signature"), public, id, sig)
}

/// The verifier at one protocol path. `relaxed` is a compile-time constant that only a
/// guard-removal mutation sets: it restores dalek's non-strict acceptance at that path
/// alone, so each path's strict-vector regression is shown to exercise its own check.
pub fn verify_path(relaxed: bool, public: &[u8; 32], id: &Id, sig: &[u8]) -> bool {
    let Ok(sig) = <[u8; 64]>::try_from(sig) else { return false };
    if !relaxed { return paralean_crypto::verify(public, &id.0, &sig); }
    let Ok(vk) = VerifyingKey::from_bytes(public) else { return false };
    ed25519_dalek::Verifier::verify(&vk, &id.0, &Signature::from_bytes(&sig)).is_ok()
}

/// Public keys the store trusts. Writers unknown to the ring are ignored by discovery and
/// recovery (their certificates count as absent).
#[derive(Clone, Default, Debug)]
pub struct KeyRing {
    pub authority: [u8; 32],
    pub validators: Vec<[u8; 32]>,
    pub writers: BTreeMap<WorkspaceId, [u8; 32]>,
    /// Controller that owns each writer ID, retained across transitive peer trust.
    pub writer_origins: BTreeMap<WorkspaceId, [u8; 32]>,
    pub ambiguous_writer_origins: BTreeSet<WorkspaceId>,
    /// Retired writer keys remain valid for historical certificates. New T1/T8
    /// writes use only `writers`, the currently configured key.
    pub writer_key_history: BTreeMap<WorkspaceId, Vec<[u8; 32]>>,
    /// Policies and checker versions receipts may name (P3 staging rule).
    pub pins: Pins,
    /// Keys that may sign job envelopes besides the authority (working copies issuing
    /// envelopes for non-target groups). They never sign tokens or revocations.
    pub job_issuers: Vec<[u8; 32]>,
    /// Explicit controller-signed bindings of AgentID to certificate keys.
    pub agent_keys: Vec<AgentKeyGrant>,
    /// Peer controller keys allowed to issue agent registrations for imported records.
    pub agent_authorities: Vec<[u8; 32]>,
}

impl KeyRing {
    pub fn writer(&self, w: &WorkspaceId) -> Option<&[u8; 32]> {
        self.writers.get(w)
    }
    pub fn verify_writer(&self, w: &WorkspaceId, id: &Id, sig: &[u8]) -> bool {
        self.signing_writer_key(w, id, sig).is_some()
    }
    pub fn signing_writer_key(&self, w: &WorkspaceId, id: &Id, sig: &[u8]) -> Option<[u8; 32]> {
        self.signing_writer_key_path(cfg!(feature = "mutate-weak-signature"), w, id, sig)
    }
    /// `signing_writer_key` at one protocol path (`verify_path`): the current key, then
    /// retired keys kept for historical certificates.
    pub fn signing_writer_key_path(&self, relaxed: bool, w: &WorkspaceId, id: &Id, sig: &[u8]) -> Option<[u8; 32]> {
        let ok = |k: &[u8; 32]| verify_path(relaxed, k, id, sig);
        self.writer(w).copied().filter(ok).or_else(|| self.writer_key_history.get(w)?.iter().copied().find(ok))
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
            match self.writers.entry(*w) {
                std::collections::btree_map::Entry::Vacant(slot) => { slot.insert(*k); }
                std::collections::btree_map::Entry::Occupied(slot) if slot.get() != k => {
                    let history = self.writer_key_history.entry(*w).or_default();
                    if !history.contains(k) { history.push(*k); }
                }
                _ => {}
            }
        }
        for (w, authority) in &peer.writer_origins {
            match self.writer_origins.entry(*w) {
                std::collections::btree_map::Entry::Vacant(slot) => { slot.insert(*authority); }
                std::collections::btree_map::Entry::Occupied(slot) if slot.get() != authority => {
                    self.ambiguous_writer_origins.insert(*w);
                }
                _ => {}
            }
        }
        self.ambiguous_writer_origins.extend(&peer.ambiguous_writer_origins);
        for (w, keys) in &peer.writer_key_history {
            let history = self.writer_key_history.entry(*w).or_default();
            for key in keys { if !history.contains(key) { history.push(*key); } }
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
        for grant in &peer.agent_keys {
            if !self.agent_keys.contains(grant) { self.agent_keys.push(grant.clone()); }
        }
        if !self.agent_authorities.contains(&peer.authority) { self.agent_authorities.push(peer.authority); }
        for authority in &peer.agent_authorities {
            if !self.agent_authorities.contains(authority) { self.agent_authorities.push(*authority); }
        }
    }
}

/// A key file: seeds for the fence authority, validators and workspaces. The CLI reads it
/// from `$PARALEAN_KEYS`. Holding a seed is holding that role.
#[derive(Clone, Serialize, Deserialize, Default)]
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
    /// Controller-signed registrations; retained in redacted worker key files.
    #[serde(default)]
    pub agent_keys: Vec<AgentKeyGrant>,
    /// Public keys retired from active writing but retained for old certificates.
    #[serde(default)]
    pub writer_key_history: BTreeMap<String, Vec<String>>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct KeyEntry {
    /// Workspace ID (hex, 16 bytes); empty for validators.
    #[serde(default)]
    pub id: String,
    pub public: String,
    #[serde(default)]
    pub seed: Option<String>,
}

impl KeyFile {
    /// Atomically replace a key file without following a destination symlink.
    /// The new inode is private from creation, independent of the caller's umask.
    /// The containing directory must be controlled by the operator.
    #[cfg(unix)]
    pub fn write_private(&self, path: impl AsRef<std::path::Path>) -> std::io::Result<()> {
        use std::io::Write;
        use std::os::unix::fs::OpenOptionsExt;
        let path = path.as_ref();
        let parent = path.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(std::path::Path::new("."));
        let tmp = parent.join(format!(".paralean-keys-{:032x}", rand::random::<u128>()));
        let mode = if cfg!(feature = "mutate-public-key-file") { 0o666 } else { 0o600 };
        let mut file = std::fs::OpenOptions::new().write(true).create_new(true).mode(mode).open(&tmp)?;
        let result = (|| {
            let bytes = serde_json::to_vec_pretty(self).map_err(std::io::Error::other)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            std::fs::rename(&tmp, path)?;
            std::fs::File::open(parent)?.sync_all()
        })();
        if result.is_err() { let _ = std::fs::remove_file(&tmp); }
        result
    }

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
        kf.register_workspace_agents();
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
            writer_origins: self.workspaces.values()
                .filter_map(|e| Some((WorkspaceId::from_hex(&e.id)?, pk(&self.authority_public))))
                .collect(),
            ambiguous_writer_origins: BTreeSet::new(),
            writer_key_history: self.writer_key_history.iter().filter_map(|(id, keys)| Some((
                WorkspaceId::from_hex(id)?, keys.iter().filter_map(|key| hex::decode(key).ok()?.try_into().ok()).collect()
            ))).collect(),
            pins: Pins {
                policies: self.policies.iter().filter_map(|h| Id::from_hex(h)).collect(),
                checkers: self.checkers.iter().filter_map(|h| Id::from_hex(h)).collect(),
            },
            job_issuers: self.job_issuers.values().map(|e| pk(&e.public)).collect(),
            agent_keys: self.agent_keys.clone(),
            agent_authorities: vec![],
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

    /// Explicitly provision both legacy fixture and remote working-copy AgentIDs for
    /// every workspace. Call at key generation, before splitting worker key files.
    pub fn register_workspace_agents(&mut self) {
        let Some(authority) = self.authority_signer() else { return };
        for entry in self.workspaces.values() {
            let (Some(workspace), Ok(public)) = (WorkspaceId::from_hex(&entry.id), hex::decode(&entry.public)) else { continue };
            let Ok(public) = <[u8; 32]>::try_from(public) else { continue };
            for agent in [crate::id::AgentId::derive(&format!("agent/{}", workspace.hex())), crate::id::AgentId(workspace.0)] {
                let grant = AgentKeyGrant::sign(agent, workspace, public, &authority);
                if !self.agent_keys.contains(&grant) { self.agent_keys.push(grant); }
            }
        }
    }

    /// Rotate a workspace certificate key. Old certificates remain verifiable;
    /// revocation of the old agent key fences new author writes transactionally.
    pub fn rotate_workspace_key(&mut self, name: &str, signer: &Signer) -> Option<[u8; 32]> {
        let old = self.workspaces.get(name)?.clone();
        let workspace = WorkspaceId::from_hex(&old.id)?;
        let old_public: [u8; 32] = hex::decode(&old.public).ok()?.try_into().ok()?;
        self.writer_key_history.entry(old.id.clone()).or_default().push(old.public);
        self.workspaces.insert(name.into(), KeyEntry {
            id: workspace.hex(), public: hex::encode(signer.public()), seed: Some(hex::encode(signer.seed())),
        });
        self.register_workspace_agents();
        Some(old_public)
    }
}

impl std::fmt::Debug for KeyEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(feature = "mutate-key-debug") { return write!(f, "{:?}", self.seed); }
        f.debug_struct("KeyEntry").field("id", &self.id).field("public", &self.public)
            .field("seed", &self.seed.as_ref().map(|_| "[REDACTED]")).finish()
    }
}

impl std::fmt::Debug for KeyFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if cfg!(feature = "mutate-key-debug") { return write!(f, "{:?}", self.authority); }
        f.debug_struct("KeyFile").field("authority_public", &self.authority_public)
            .field("authority", &self.authority.as_ref().map(|_| "[REDACTED]"))
            .field("validators", &self.validators).field("workspaces", &self.workspaces)
            .field("job_issuers", &self.job_issuers).finish_non_exhaustive()
    }
}

#[cfg(test)]
mod security_tests {
    use super::*;
    #[test]
    fn debug_does_not_disclose_role_seeds() {
        let k = KeyFile::demo(1);
        let text = format!("{k:?}");
        assert!(!text.contains(k.authority.as_ref().unwrap()));
        assert!(!text.contains(k.validators["v0"].seed.as_ref().unwrap()));
        assert!(!text.contains(k.workspaces["w0"].seed.as_ref().unwrap()));
    }

    #[test]
    fn private_key_file_replaces_public_inode_and_symlink() {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let dir = std::env::temp_dir().join(format!("paralean-key-test-{:032x}", rand::random::<u128>()));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("keys");
        let other = dir.join("other");
        std::fs::write(&other, "untouched").unwrap();
        symlink(&other, &path).unwrap();
        let k = KeyFile::demo(1);
        k.write_private(&path).unwrap();
        assert_eq!(std::fs::read_to_string(&other).unwrap(), "untouched");
        assert_eq!(std::fs::metadata(&path).unwrap().permissions().mode() & 0o777, 0o600);
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        k.write_private(&path).unwrap();
        assert_eq!(std::fs::metadata(&path).unwrap().permissions().mode() & 0o777, 0o600);
        let read: KeyFile = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(read.authority, k.authority);
        std::fs::remove_dir_all(dir).unwrap();
    }

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
