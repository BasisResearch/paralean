//! IDs and hash domains, docs/p0-interfaces.md §1.2:
//! `H(domain, x) = SHA-256("paralean\x00" ‖ domain ‖ "\x00" ‖ PCE(x))`.
//!
//! Every stored object is its hash preimage, so the SHA-256 of the stored bytes is the ID
//! (store.md, "Content-addressed writes").

use std::fmt;

use sha2::{Digest, Sha256};

use crate::pce::{DResult, Dec, DecodeError, Enc, Pce};

/// The fixed prefix of every preimage.
pub const PREFIX: &[u8] = b"paralean\x00";

pub fn sha256(b: &[u8]) -> [u8; 32] {
    Sha256::digest(b).into()
}

/// A 32-byte content address.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Id(pub [u8; 32]);

impl Id {
    pub fn hex(&self) -> String {
        hex::encode(self.0)
    }
    pub fn from_hex(s: &str) -> Option<Id> {
        let v = hex::decode(s).ok()?;
        Some(Id(v.try_into().ok()?))
    }
    pub fn short(&self) -> String {
        self.hex()[..12].to_string()
    }
}

impl fmt::Debug for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.short())
    }
}
impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.hex())
    }
}

/// IDs are PCE `bytes` of length 32.
impl Pce for Id {
    fn encode(&self, e: &mut Enc) {
        e.bytes(&self.0);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(Id(d.fixed::<32>("id")?))
    }
}

macro_rules! id16 {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        pub struct $name(pub [u8; 16]);
        impl $name {
            pub fn hex(&self) -> String { hex::encode(self.0) }
            pub fn from_hex(s: &str) -> Option<Self> {
                let v = hex::decode(s).ok()?;
                Some($name(v.try_into().ok()?))
            }
            /// A deterministic ID derived from a label (tests and fixtures).
            pub fn derive(label: &str) -> Self {
                let h = sha256(label.as_bytes());
                let mut a = [0u8; 16];
                a.copy_from_slice(&h[..16]);
                $name(a)
            }
            pub fn random() -> Self { $name(rand::random()) }
        }
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", &self.hex()[..8])
            }
        }
        impl Pce for $name {
            fn encode(&self, e: &mut Enc) { e.bytes(&self.0); }
            fn decode(d: &mut Dec<'_>) -> DResult<Self> { Ok($name(d.fixed::<16>(stringify!($name))?)) }
        }
    };
}

id16!(
    /// `WorkspaceID`: 16 random bytes (§10). Also the writer identity of certificates.
    WorkspaceId
);
id16!(
    /// `AgentID` (§11.1).
    AgentId
);
id16!(
    /// `ReplicaID`. Under store.md's single abstract replica σ this is one constant per
    /// deployment.
    ReplicaId
);

/// Hash domains. §1.2 lists all but `Blob` (store.md), `Manifest`, `Token` and `TCert`
/// (added by P2, see docs/p2-log.md).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Domain {
    Group,
    Capsule,
    Receipt,
    Revision,
    Marker,
    Cert,
    OCert,
    RCert,
    Tombstone,
    Snapshot,
    Catalog,
    Base,
    Chunk,
    Blob,
    Manifest,
    Token,
    /// Tombstone certificate (§11.4: tombstones are certificate-discovered like markers).
    TCert,
}

impl Domain {
    pub fn tag(self) -> &'static str {
        match self {
            Domain::Group => "v0/group",
            Domain::Capsule => "v0/capsule",
            Domain::Receipt => "v0/receipt",
            Domain::Revision => "v0/revision",
            Domain::Marker => "v0/marker",
            Domain::Cert => "v0/cert",
            Domain::OCert => "v0/ocert",
            Domain::RCert => "v0/rcert",
            Domain::Tombstone => "v0/tombstone",
            Domain::Snapshot => "v0/snapshot",
            Domain::Catalog => "v0/catalog",
            Domain::Base => "v0/base",
            Domain::Chunk => "v0/chunk",
            Domain::Blob => "v0/blob",
            Domain::Manifest => "v0/manifest",
            Domain::Token => "v0/token",
            Domain::TCert => "v0/tcert",
        }
    }

    /// The preimage `"paralean\x00" ‖ domain ‖ "\x00" ‖ pce`.
    pub fn preimage(self, pce: &[u8]) -> Vec<u8> {
        let t = self.tag().as_bytes();
        let mut v = Vec::with_capacity(PREFIX.len() + t.len() + 1 + pce.len());
        v.extend_from_slice(PREFIX);
        v.extend_from_slice(t);
        v.push(0);
        v.extend_from_slice(pce);
        v
    }

    pub fn hash(self, pce: &[u8]) -> Id {
        Id(sha256(&self.preimage(pce)))
    }

    /// Split a preimage of this domain into its PCE payload, or fail.
    pub fn strip(self, preimage: &[u8]) -> DResult<&[u8]> {
        let t = self.tag().as_bytes();
        let n = PREFIX.len() + t.len() + 1;
        if preimage.len() < n
            || &preimage[..PREFIX.len()] != PREFIX
            || &preimage[PREFIX.len()..n - 1] != t
            || preimage[n - 1] != 0
        {
            return Err(DecodeError::Invalid("preimage domain"));
        }
        Ok(&preimage[n..])
    }
}

/// Typed store kinds. Each kind has exactly one domain and one placement, so a key of one
/// kind is never read as another and an ID cannot verify as another kind's bytes.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum Kind {
    // --- S3 (payload store), key `obj/<kind>/<hex id>`.
    /// Group manifest (§8.1 `payload`; domain `v0/group`).
    Group,
    /// Term-table chunk (§8.1 `payload`; domain `v0/chunk`).
    Chunk,
    Capsule,
    /// Snapshot (§9). store.md's T5 reads `ocert/manifest/<m>` for "the record's
    /// manifest"; that object is the snapshot, certified as `ocert/snapshot/<m>`.
    Snapshot,
    /// Export manifests: the snapshot's `sourceRoot` and `buildReceipt` (domain `v0/manifest`).
    Manifest,
    /// Oversized metadata values (store.md "Layout": over 64 kB).
    Blob,
    /// The acknowledged copy of a marker before the publish transaction (§8.2 step 2).
    StagedMarker,
    /// The acknowledged copy of a tombstone before its publish transaction (T8).
    StagedTombstone,
}

impl Kind {
    pub const S3_KINDS: [Kind; 8] = [
        Kind::Group,
        Kind::Chunk,
        Kind::Capsule,
        Kind::Snapshot,
        Kind::Manifest,
        Kind::Blob,
        Kind::StagedMarker,
        Kind::StagedTombstone,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Kind::Group => "group",
            Kind::Chunk => "chunk",
            Kind::Capsule => "capsule",
            Kind::Snapshot => "snapshot",
            Kind::Manifest => "manifest",
            Kind::Blob => "blob",
            Kind::StagedMarker => "marker",
            Kind::StagedTombstone => "tombstone",
        }
    }
    pub fn from_name(s: &str) -> Option<Kind> {
        Kind::S3_KINDS.iter().copied().find(|k| k.name() == s)
    }
    pub fn domain(self) -> Domain {
        match self {
            Kind::Group => Domain::Group,
            Kind::Chunk => Domain::Chunk,
            Kind::Capsule => Domain::Capsule,
            Kind::Snapshot => Domain::Snapshot,
            Kind::Manifest => Domain::Manifest,
            Kind::Blob => Domain::Blob,
            Kind::StagedMarker => Domain::Marker,
            Kind::StagedTombstone => Domain::Tombstone,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preimage_shape_and_hash() {
        let p = Domain::Group.preimage(b"xyz");
        assert_eq!(p, b"paralean\x00v0/group\x00xyz".to_vec());
        assert_eq!(Domain::Group.hash(b"xyz").0, sha256(&p));
        assert_eq!(Domain::Group.strip(&p).unwrap(), b"xyz");
        assert!(Domain::Capsule.strip(&p).is_err());
    }

    /// Output of `scripts/p1-golden.sh`: P1's pure-Lean `Sha256.lean` run with P1's
    /// toolchain (nightly-2026-10-03) on the same inputs.
    /// A real P1 group (`paralean-group-v3`, F01 `two_eq`, captured by `impl/p1` on the fork):
    /// P2's `H("v0/group", bytes)` is P1's `declId` (p2-log.md deviation 10, fixed).
    #[test]
    fn p1_group_id_matches() {
        let bytes = include_bytes!("../tests/data/p1-F01-two_eq.grp");
        assert_eq!(
            Domain::Group.hash(bytes).hex(),
            "d2663a5ba5635213970abada58b7625ed4b60b048044111cf296203f6e084036"
        );
    }

    #[test]
    fn matches_p1_lean_sha256() {
        let range: Vec<u8> = (0..1000u32).map(|i| (i % 251) as u8).collect();
        let cases: [(&[u8], &str); 5] = [
            (b"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
            (b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
            (b"paralean\x00v0/group\x00xyz", "5129d1688c87166c5dd0698ff36f43ebb72b809ba925c6d9ae283f773f18b067"),
            (&range, "4e4c294b331f7a2099a379bec34b9f9fc03dc46ab465d998f4d683da53487e6d"),
            (
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
        ];
        for (input, want) in cases {
            assert_eq!(hex::encode(sha256(input)), want);
        }
        assert_eq!(Domain::Group.hash(b"xyz").hex(), cases[2].1, "preimage hashing agrees with P1");
    }

    #[test]
    fn sha256_vectors() {
        // FIPS 180-4 test vectors.
        assert_eq!(
            hex::encode(sha256(b"")),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hex::encode(sha256(b"abc")),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
