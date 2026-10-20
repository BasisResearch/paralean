//! Controller-signed agent-key registrations. A registration binds an AgentID to a
//! workspace certificate key; transactions read its FDB slot and revocation bit.
use serde::{Deserialize, Serialize};

use crate::id::{sha256, AgentId, Id, WorkspaceId};
use crate::sign::{verify, Signer};

/// Stable git/projection author identity for a controller key.
pub fn controller_agent_id(public: &[u8; 32]) -> AgentId {
    let mut bytes = b"paralean\0v0/controller-agent\0".to_vec();
    bytes.extend_from_slice(public);
    let hash = sha256(&bytes);
    AgentId(hash[..16].try_into().expect("slice length"))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgentKeyGrant {
    pub agent: String,
    pub workspace: String,
    pub public: String,
    pub issuer: String,
    pub signature: String,
}

impl AgentKeyGrant {
    fn message(agent: &AgentId, workspace: &WorkspaceId, public: &[u8; 32]) -> Id {
        let mut bytes = b"paralean\0v0/agent-key\0".to_vec();
        bytes.extend_from_slice(&agent.0);
        bytes.extend_from_slice(&workspace.0);
        bytes.extend_from_slice(public);
        Id(sha256(&bytes))
    }
    pub fn sign(agent: AgentId, workspace: WorkspaceId, public: [u8; 32], authority: &Signer) -> Self {
        let id = Self::message(&agent, &workspace, &public);
        AgentKeyGrant {
            agent: agent.hex(), workspace: workspace.hex(), public: hex::encode(public),
            issuer: hex::encode(authority.public()), signature: hex::encode(authority.sign(&id)),
        }
    }
    pub fn parts(&self) -> Option<(AgentId, WorkspaceId, [u8; 32], [u8; 32])> {
        Some((
            AgentId::from_hex(&self.agent)?, WorkspaceId::from_hex(&self.workspace)?,
            hex::decode(&self.public).ok()?.try_into().ok()?,
            hex::decode(&self.issuer).ok()?.try_into().ok()?,
        ))
    }
    pub fn verify(&self) -> bool {
        let Some((agent, workspace, public, issuer)) = self.parts() else { return false };
        let Ok(signature) = hex::decode(&self.signature) else { return false };
        verify(&issuer, &Self::message(&agent, &workspace, &public), &signature)
    }
    pub fn encoded(&self) -> Vec<u8> { serde_json::to_vec(self).expect("agent grant serializes") }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ControllerDeleteGrant {
    pub tombstone: String,
    pub fence: u64,
    pub issuer: String,
    pub signature: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AgentKeyRevocation {
    pub public: String,
    pub issuer: String,
    pub signature: String,
}

impl AgentKeyRevocation {
    fn message(public: &[u8; 32]) -> Id {
        let mut bytes = b"paralean\0v0/agent-key-revoke\0".to_vec();
        bytes.extend_from_slice(public);
        Id(sha256(&bytes))
    }
    pub fn sign(public: [u8; 32], authority: &Signer) -> Self {
        AgentKeyRevocation { public: hex::encode(public), issuer: hex::encode(authority.public()),
            signature: hex::encode(authority.sign(&Self::message(&public))) }
    }
    pub fn verify(&self, authority: &[u8; 32]) -> bool {
        if self.issuer != hex::encode(authority) { return false }
        let (Ok(public), Ok(signature)) = (hex::decode(&self.public), hex::decode(&self.signature)) else { return false };
        let Ok(public) = <[u8; 32]>::try_from(public) else { return false };
        verify(authority, &Self::message(&public), &signature)
    }
    pub fn public(&self) -> Option<[u8; 32]> { hex::decode(&self.public).ok()?.try_into().ok() }
    pub fn encoded(&self) -> Vec<u8> { serde_json::to_vec(self).expect("agent revocation serializes") }
}

impl ControllerDeleteGrant {
    fn message(tombstone: &Id, fence: u64) -> Id {
        let mut bytes = b"paralean\0v0/controller-delete\0".to_vec();
        bytes.extend_from_slice(&tombstone.0);
        bytes.extend_from_slice(&fence.to_be_bytes());
        Id(sha256(&bytes))
    }
    pub fn sign(tombstone: Id, fence: u64, authority: &Signer) -> Self {
        let id = Self::message(&tombstone, fence);
        ControllerDeleteGrant { tombstone: tombstone.hex(), fence,
            issuer: hex::encode(authority.public()), signature: hex::encode(authority.sign(&id)) }
    }
    pub fn verify(&self, tombstone: &Id, issuer: &[u8; 32]) -> bool {
        if self.tombstone != tombstone.hex() || self.issuer != hex::encode(issuer) { return false }
        let Ok(signature) = hex::decode(&self.signature) else { return false };
        verify(issuer, &Self::message(tombstone, self.fence), &signature)
    }
    pub fn encoded(&self) -> Vec<u8> { serde_json::to_vec(self).expect("deletion grant serializes") }
}
