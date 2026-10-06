//! Typed immutable objects (§6, §7, §8, §9, §11.1) and the mutable store records (target
//! records, tokens, the fence).
//!
//! Field order follows p0-interfaces.md. Every top-level object starts with
//! `format : uvarint = 0` (§1.4); a reader rejects other formats. IDs are PCE `bytes` of
//! length 32; workspace, agent and replica IDs are `bytes` of length 16.

use std::fmt;

use crate::id::{AgentId, Domain, Id, Kind, ReplicaId, WorkspaceId};
use crate::pce::{DResult, Dec, DecodeError, Enc, Pce};
use crate::sign::{KeyRing, Signer};

pub const FORMAT: u64 = 0;

fn put_format(e: &mut Enc) {
    e.uvarint(FORMAT);
}
fn get_format(d: &mut Dec<'_>) -> DResult<()> {
    match d.uvarint()? {
        FORMAT => Ok(()),
        f => Err(DecodeError::Format(f)),
    }
}

/// A content-addressed object with its own hash domain.
pub trait Object: Pce {
    const DOMAIN: Domain;
    fn id(&self) -> Id {
        Self::DOMAIN.hash(&self.to_pce())
    }
    /// The stored bytes: the hash preimage.
    fn preimage(&self) -> Vec<u8> {
        Self::DOMAIN.preimage(&self.to_pce())
    }
    fn from_preimage(b: &[u8]) -> DResult<Self> {
        Self::from_pce(Self::DOMAIN.strip(b)?)
    }
}

// ---------------------------------------------------------------- Lean names

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum NameComp {
    Str(String),
    Num(u128),
}

/// A Lean `Name`, root component first. PCE: `list` of `str(string) | num(nat)`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Name(pub Vec<NameComp>);

impl Name {
    /// Parse a dotted name; all-digit components are numeric.
    pub fn parse(s: &str) -> Name {
        Name(
            s.split('.')
                .filter(|c| !c.is_empty())
                .map(|c| match c.parse::<u128>() {
                    Ok(n) if !c.starts_with('0') || c == "0" => NameComp::Num(n),
                    _ => NameComp::Str(c.to_string()),
                })
                .collect(),
        )
    }
}

impl fmt::Display for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let parts: Vec<String> = self
            .0
            .iter()
            .map(|c| match c {
                NameComp::Str(s) => s.clone(),
                NameComp::Num(n) => n.to_string(),
            })
            .collect();
        write!(f, "{}", parts.join("."))
    }
}
impl fmt::Debug for Name {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{self}")
    }
}

impl Pce for Name {
    fn encode(&self, e: &mut Enc) {
        e.list(&self.0, |e, c| match c {
            NameComp::Str(s) => {
                e.byte(0).string(s);
            }
            NameComp::Num(n) => {
                e.byte(1).nat(*n);
            }
        });
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(Name(d.list(|d| match d.byte()? {
            0 => Ok(NameComp::Str(d.string()?)),
            1 => Ok(NameComp::Num(d.nat()?)),
            tag => Err(DecodeError::UnknownTag { what: "name component", tag }),
        })?))
    }
}

fn enc_ids(e: &mut Enc, ids: &[Id]) {
    e.set(ids, |e, x| x.encode(e));
}
fn dec_ids(d: &mut Dec<'_>) -> DResult<Vec<Id>> {
    d.set(Id::decode)
}
fn enc_names(e: &mut Enc, ns: &[Name]) {
    e.set(ns, |e, x| x.encode(e));
}

// ---------------------------------------------------------------- opaque payloads

/// An S3 object whose PCE the store does not interpret: group manifests (P1's
/// `paralean-group-v2` bytes are their PCE), chunks, capsules and blobs.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Opaque {
    pub kind: Kind,
    pub pce: Vec<u8>,
}

impl Opaque {
    pub fn new(kind: Kind, pce: Vec<u8>) -> Self {
        Opaque { kind, pce }
    }
    pub fn id(&self) -> Id {
        self.kind.domain().hash(&self.pce)
    }
    pub fn preimage(&self) -> Vec<u8> {
        self.kind.domain().preimage(&self.pce)
    }
}

// ---------------------------------------------------------------- receipts (§6)

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    Accepted,
    Rejected(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReceiptBody {
    pub group: Id,
    pub base: Id,
    pub validator_key: [u8; 32],
    pub validator_bin: Vec<u8>,
    pub policy: Id,
    pub request: Option<Vec<u8>>,
    pub target: Option<Vec<u8>>,
    pub verdict: Verdict,
    pub axioms: Vec<Name>,
}

impl Pce for ReceiptBody {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.group.encode(e);
        self.base.encode(e);
        e.bytes(&self.validator_key).bytes(&self.validator_bin);
        self.policy.encode(e);
        e.option(&self.request, |e, x| {
            e.bytes(x);
        });
        e.option(&self.target, |e, x| {
            e.bytes(x);
        });
        match &self.verdict {
            Verdict::Accepted => {
                e.byte(0);
            }
            Verdict::Rejected(r) => {
                e.byte(1).string(r);
            }
        }
        enc_names(e, &self.axioms);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(ReceiptBody {
            group: Id::decode(d)?,
            base: Id::decode(d)?,
            validator_key: d.fixed::<32>("validatorKey")?,
            validator_bin: d.bytes()?.to_vec(),
            policy: Id::decode(d)?,
            request: d.option(|d| Ok(d.bytes()?.to_vec()))?,
            target: d.option(|d| Ok(d.bytes()?.to_vec()))?,
            verdict: match d.byte()? {
                0 => Verdict::Accepted,
                1 => Verdict::Rejected(d.string()?),
                tag => return Err(DecodeError::UnknownTag { what: "verdict", tag }),
            },
            axioms: d.set(Name::decode)?,
        })
    }
}
impl Object for ReceiptBody {
    const DOMAIN: Domain = Domain::Receipt;
}

// ---------------------------------------------------------------- revisions (§7)

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Revision {
    pub group: Id,
    pub name: Name,
    /// Sorted, distinct.
    pub parents: Vec<Id>,
    pub capsule: Id,
    pub workspace: WorkspaceId,
}

impl Pce for Revision {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.group.encode(e);
        self.name.encode(e);
        enc_ids(e, &self.parents);
        self.capsule.encode(e);
        self.workspace.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(Revision {
            group: Id::decode(d)?,
            name: Name::decode(d)?,
            parents: dec_ids(d)?,
            capsule: Id::decode(d)?,
            workspace: WorkspaceId::decode(d)?,
        })
    }
}
impl Object for Revision {
    const DOMAIN: Domain = Domain::Revision;
}

// ---------------------------------------------------------------- markers (§8.2, §11.1)

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Anchor {
    FileStart,
    After(Id),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Marker {
    pub group: Id,
    /// Sorted, distinct.
    pub revisions: Vec<Id>,
    pub receipt: Id,
    pub file_path: String,
    pub anchor: Anchor,
    // `rightAnchor` (OPEN-18): an optional field fixed to `0x00` in v0.
    pub lamport: u64,
    pub author: AgentId,
    pub root_path: Vec<(Id, u64, AgentId)>,
    pub lineage_keys: Vec<(Name, u64, AgentId)>,
}

impl Pce for Marker {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.group.encode(e);
        enc_ids(e, &self.revisions);
        self.receipt.encode(e);
        e.string(&self.file_path);
        match &self.anchor {
            Anchor::FileStart => {
                e.byte(0);
            }
            Anchor::After(g) => {
                e.byte(1);
                g.encode(e);
            }
        }
        e.byte(0); // rightAnchor: none
        e.uvarint(self.lamport);
        self.author.encode(e);
        e.list(&self.root_path, |e, (g, l, a)| {
            g.encode(e);
            e.uvarint(*l);
            a.encode(e);
        });
        e.list(&self.lineage_keys, |e, (n, l, a)| {
            n.encode(e);
            e.uvarint(*l);
            a.encode(e);
        });
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        let group = Id::decode(d)?;
        let revisions = dec_ids(d)?;
        let receipt = Id::decode(d)?;
        let file_path = d.string()?;
        let anchor = match d.byte()? {
            0 => Anchor::FileStart,
            1 => Anchor::After(Id::decode(d)?),
            tag => return Err(DecodeError::UnknownTag { what: "anchor", tag }),
        };
        match d.byte()? {
            0 => {}
            tag => return Err(DecodeError::UnknownTag { what: "rightAnchor (v0: none)", tag }),
        }
        Ok(Marker {
            group,
            revisions,
            receipt,
            file_path,
            anchor,
            lamport: d.uvarint()?,
            author: AgentId::decode(d)?,
            root_path: d.list(|d| Ok((Id::decode(d)?, d.uvarint()?, AgentId::decode(d)?)))?,
            lineage_keys: d.list(|d| Ok((Name::decode(d)?, d.uvarint()?, AgentId::decode(d)?)))?,
        })
    }
}
impl Object for Marker {
    const DOMAIN: Domain = Domain::Marker;
}

/// Tombstone (§11.4): `{filePath, target : group, lamport, author, receiptID?}`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Tombstone {
    pub file_path: String,
    pub target: Id,
    pub lamport: u64,
    pub author: AgentId,
    pub receipt: Option<Id>,
}

impl Pce for Tombstone {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        e.string(&self.file_path);
        self.target.encode(e);
        e.uvarint(self.lamport);
        self.author.encode(e);
        e.option(&self.receipt, |e, x| x.encode(e));
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(Tombstone {
            file_path: d.string()?,
            target: Id::decode(d)?,
            lamport: d.uvarint()?,
            author: AgentId::decode(d)?,
            receipt: d.option(Id::decode)?,
        })
    }
}
impl Object for Tombstone {
    const DOMAIN: Domain = Domain::Tombstone;
}

// ---------------------------------------------------------------- certificates (§8.3, §9)

/// Publication certificate body: `{replica, markerID, groupID, writer}`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CertBody {
    pub replica: ReplicaId,
    pub marker: Id,
    pub group: Id,
    pub writer: WorkspaceId,
}

impl Pce for CertBody {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.replica.encode(e);
        self.marker.encode(e);
        self.group.encode(e);
        self.writer.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(CertBody {
            replica: ReplicaId::decode(d)?,
            marker: Id::decode(d)?,
            group: Id::decode(d)?,
            writer: WorkspaceId::decode(d)?,
        })
    }
}
impl Object for CertBody {
    const DOMAIN: Domain = Domain::Cert;
}

/// Object certificate body: `{replica, kind, id, writer}`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ObjectCertBody {
    pub replica: ReplicaId,
    pub kind: Kind,
    pub id: Id,
    pub writer: WorkspaceId,
}

impl Pce for ObjectCertBody {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.replica.encode(e);
        e.string(self.kind.name());
        self.id.encode(e);
        self.writer.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(ObjectCertBody {
            replica: ReplicaId::decode(d)?,
            kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("ocert kind"))?,
            id: Id::decode(d)?,
            writer: WorkspaceId::decode(d)?,
        })
    }
}
impl Object for ObjectCertBody {
    const DOMAIN: Domain = Domain::OCert;
}

/// A fence token as embedded in records: `{rank, holder}`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord, Hash)]
pub struct TokenRef {
    pub rank: u64,
    pub holder: WorkspaceId,
}

impl Pce for TokenRef {
    fn encode(&self, e: &mut Enc) {
        e.uvarint(self.rank);
        self.holder.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(TokenRef { rank: d.uvarint()?, holder: WorkspaceId::decode(d)? })
    }
}

/// The signed token issued by T3 (domain `v0/token`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenBody {
    pub token: TokenRef,
}
impl Pce for TokenBody {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.token.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(TokenBody { token: TokenRef::decode(d)? })
    }
}
impl Object for TokenBody {
    const DOMAIN: Domain = Domain::Token;
}

/// Commit certificate body: `{replica, catalogID, token}`; signed by the token holder.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CommitCertBody {
    pub replica: ReplicaId,
    pub catalog: Id,
    pub token: TokenRef,
}

impl Pce for CommitCertBody {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.replica.encode(e);
        self.catalog.encode(e);
        self.token.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(CommitCertBody { replica: ReplicaId::decode(d)?, catalog: Id::decode(d)?, token: TokenRef::decode(d)? })
    }
}
impl Object for CommitCertBody {
    const DOMAIN: Domain = Domain::RCert;
}

// ---------------------------------------------------------------- catalogue (§9)

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct CatalogRecord {
    pub workspace: WorkspaceId,
    pub snapshot: Id,
    pub predecessor: Option<Id>,
    pub token: TokenRef,
}

impl Pce for CatalogRecord {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.workspace.encode(e);
        self.snapshot.encode(e);
        e.option(&self.predecessor, |e, x| x.encode(e));
        self.token.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(CatalogRecord {
            workspace: WorkspaceId::decode(d)?,
            snapshot: Id::decode(d)?,
            predecessor: d.option(Id::decode)?,
            token: TokenRef::decode(d)?,
        })
    }
}
impl Object for CatalogRecord {
    const DOMAIN: Domain = Domain::Catalog;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TargetAssignment {
    pub name: Name,
    pub owner: WorkspaceId,
    pub epoch: u64,
    pub assigned_by: Vec<u8>,
    pub signature: Vec<u8>,
}

impl Pce for TargetAssignment {
    fn encode(&self, e: &mut Enc) {
        self.name.encode(e);
        self.owner.encode(e);
        e.uvarint(self.epoch).bytes(&self.assigned_by).bytes(&self.signature);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(TargetAssignment {
            name: Name::decode(d)?,
            owner: WorkspaceId::decode(d)?,
            epoch: d.uvarint()?,
            assigned_by: d.bytes()?.to_vec(),
            signature: d.bytes()?.to_vec(),
        })
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Snapshot {
    pub workspace: WorkspaceId,
    pub base: Id,
    /// Revision IDs, sorted and distinct.
    pub contents: Vec<Id>,
    pub predecessors: Vec<Id>,
    pub targets: Vec<TargetAssignment>,
    pub source_root: Id,
    pub build_receipt: Id,
}

impl Pce for Snapshot {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.workspace.encode(e);
        self.base.encode(e);
        enc_ids(e, &self.contents);
        enc_ids(e, &self.predecessors);
        e.set(&self.targets, |e, t| t.encode(e));
        self.source_root.encode(e);
        self.build_receipt.encode(e);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(Snapshot {
            workspace: WorkspaceId::decode(d)?,
            base: Id::decode(d)?,
            contents: dec_ids(d)?,
            predecessors: dec_ids(d)?,
            targets: d.set(TargetAssignment::decode)?,
            source_root: Id::decode(d)?,
            build_receipt: Id::decode(d)?,
        })
    }
}
impl Object for Snapshot {
    const DOMAIN: Domain = Domain::Snapshot;
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum BuildVerdict {
    Ok,
    Failed(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TargetCheck {
    pub target: Vec<u8>,
    pub group: Id,
    pub statement_matches: bool,
    pub axioms: Vec<Name>,
}

/// Export manifests (domain `v0/manifest`): the snapshot's source layout and its stock-build
/// attestation (§9 `BuildReceipt`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Manifest {
    SourceRoot { files: Vec<(String, Vec<Id>)> },
    BuildReceipt {
        exporter_bin: Vec<u8>,
        lean_commit: String,
        mathlib_commit: String,
        layout: Id,
        build_log_hash: Vec<u8>,
        target_checks: Vec<TargetCheck>,
        verdict: BuildVerdict,
    },
}

impl Pce for Manifest {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        match self {
            Manifest::SourceRoot { files } => {
                e.byte(0);
                e.list(files, |e, (p, caps)| {
                    e.string(p);
                    e.list(caps, |e, c| c.encode(e));
                });
            }
            Manifest::BuildReceipt {
                exporter_bin,
                lean_commit,
                mathlib_commit,
                layout,
                build_log_hash,
                target_checks,
                verdict,
            } => {
                e.byte(1).bytes(exporter_bin).string(lean_commit).string(mathlib_commit);
                layout.encode(e);
                e.bytes(build_log_hash);
                e.list(target_checks, |e, t| {
                    e.bytes(&t.target);
                    t.group.encode(e);
                    e.bool(t.statement_matches);
                    enc_names(e, &t.axioms);
                });
                match verdict {
                    BuildVerdict::Ok => {
                        e.byte(0);
                    }
                    BuildVerdict::Failed(r) => {
                        e.byte(1).string(r);
                    }
                }
            }
        }
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        match d.byte()? {
            0 => Ok(Manifest::SourceRoot {
                files: d.list(|d| Ok((d.string()?, d.list(Id::decode)?)))?,
            }),
            1 => Ok(Manifest::BuildReceipt {
                exporter_bin: d.bytes()?.to_vec(),
                lean_commit: d.string()?,
                mathlib_commit: d.string()?,
                layout: Id::decode(d)?,
                build_log_hash: d.bytes()?.to_vec(),
                target_checks: d.list(|d| {
                    Ok(TargetCheck {
                        target: d.bytes()?.to_vec(),
                        group: Id::decode(d)?,
                        statement_matches: d.bool()?,
                        axioms: d.set(Name::decode)?,
                    })
                })?,
                verdict: match d.byte()? {
                    0 => BuildVerdict::Ok,
                    1 => BuildVerdict::Failed(d.string()?),
                    tag => return Err(DecodeError::UnknownTag { what: "build verdict", tag }),
                },
            }),
            tag => Err(DecodeError::UnknownTag { what: "manifest", tag }),
        }
    }
}
impl Object for Manifest {
    const DOMAIN: Domain = Domain::Manifest;
}

// ---------------------------------------------------------------- signed objects

/// A signed object: the body's preimage and an Ed25519 signature over the body's ID.
/// Stored as PCE `bytes(preimage(body)) ‖ bytes(signature)`. The ID is the body's ID, so
/// the signature is not part of the identity (as for receipts, §6).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Signed<T> {
    pub body: T,
    pub sig: [u8; 64],
}

impl<T: Object> Signed<T> {
    pub fn sign(body: T, signer: &Signer) -> Self {
        let sig = signer.sign(&body.id());
        Signed { body, sig }
    }
    pub fn id(&self) -> Id {
        self.body.id()
    }
    pub fn verify(&self, public: &[u8; 32]) -> bool {
        crate::sign::verify(public, &self.id(), &self.sig)
    }
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut e = Enc::new();
        e.bytes(&self.body.preimage()).bytes(&self.sig);
        e.out
    }
    pub fn from_bytes(b: &[u8]) -> DResult<Self> {
        let mut d = Dec::new(b);
        let body = T::from_preimage(d.bytes()?)?;
        let sig = d.fixed::<64>("signature")?;
        d.end()?;
        Ok(Signed { body, sig })
    }
}

pub type Receipt = Signed<ReceiptBody>;
pub type Cert = Signed<CertBody>;
pub type ObjectCert = Signed<ObjectCertBody>;
pub type CommitCert = Signed<CommitCertBody>;
pub type Token = Signed<TokenBody>;
pub type SignedRecord = Signed<CatalogRecord>;

impl Receipt {
    /// The staging rule of §6: accepted, for exactly this group, signed by a trusted
    /// validator whose key is the one named in the body.
    pub fn admits(&self, group: &Id, ring: &KeyRing) -> bool {
        self.body.group == *group
            && self.body.verdict == Verdict::Accepted
            && ring.is_validator(&self.body.validator_key)
            && self.verify(&self.body.validator_key)
    }
}

// ---------------------------------------------------------------- mutable records

/// `target/<name>`: §7 `TargetRecord` plus the request ID of the last reassignment (store.md
/// "Transactions": the effect of T4 is recognised by a request ID).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TargetRecord {
    pub name: Name,
    pub owner: WorkspaceId,
    pub epoch: u64,
    pub head: Option<Id>,
    pub last_request: Vec<u8>,
}

impl Pce for TargetRecord {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.name.encode(e);
        self.owner.encode(e);
        e.uvarint(self.epoch);
        e.option(&self.head, |e, x| x.encode(e));
        e.bytes(&self.last_request);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(TargetRecord {
            name: Name::decode(d)?,
            owner: WorkspaceId::decode(d)?,
            epoch: d.uvarint()?,
            head: d.option(Id::decode)?,
            last_request: d.bytes()?.to_vec(),
        })
    }
}

/// `assign/<name>/<epoch>`: who was assigned at that epoch, by which request (grow-only log
/// used to resolve an unknown-outcome T4 exactly; see docs/p2-log.md).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AssignEntry {
    pub owner: WorkspaceId,
    pub request: Vec<u8>,
}

impl Pce for AssignEntry {
    fn encode(&self, e: &mut Enc) {
        put_format(e);
        self.owner.encode(e);
        e.bytes(&self.request);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        get_format(d)?;
        Ok(AssignEntry { owner: WorkspaceId::decode(d)?, request: d.bytes()?.to_vec() })
    }
}

/// `token/<rank>`: the signed token and the request that issued it.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TokenEntry {
    pub token: Token,
    pub request: Vec<u8>,
}

impl Pce for TokenEntry {
    fn encode(&self, e: &mut Enc) {
        e.bytes(&self.token.to_bytes()).bytes(&self.request);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(TokenEntry { token: Token::from_bytes(d.bytes()?)?, request: d.bytes()?.to_vec() })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(n: u8) -> Id {
        Id([n; 32])
    }

    #[test]
    fn roundtrips_and_strictness() {
        let m = Marker {
            group: id(1),
            revisions: vec![id(2), id(3)],
            receipt: id(4),
            file_path: "A/B.lean".into(),
            anchor: Anchor::After(id(5)),
            lamport: 7,
            author: AgentId::derive("a"),
            root_path: vec![(id(5), 3, AgentId::derive("b"))],
            lineage_keys: vec![(Name::parse("Foo.bar"), 7, AgentId::derive("a"))],
        };
        let b = m.to_pce();
        assert_eq!(Marker::from_pce(&b).unwrap(), m);
        assert_eq!(Marker::from_preimage(&m.preimage()).unwrap(), m);
        // Trailing byte rejected.
        let mut b2 = b.clone();
        b2.push(0);
        assert!(Marker::from_pce(&b2).is_err());
        // Unknown format rejected.
        let mut b3 = b.clone();
        b3[0] = 1;
        assert_eq!(Marker::from_pce(&b3), Err(DecodeError::Format(1)));
        // Domain separation: a marker preimage does not decode as a revision.
        assert!(Revision::from_preimage(&m.preimage()).is_err());
    }

    #[test]
    fn signed_roundtrip() {
        let s = Signer::derive("w");
        let c = Cert::sign(
            CertBody { replica: ReplicaId::derive("r"), marker: id(1), group: id(2), writer: WorkspaceId::derive("w") },
            &s,
        );
        let c2 = Cert::from_bytes(&c.to_bytes()).unwrap();
        assert_eq!(c, c2);
        assert!(c2.verify(&s.public()));
        assert!(!c2.verify(&Signer::derive("x").public()));
    }

    #[test]
    fn names() {
        let n = Name::parse("Nat.add_comm.1");
        assert_eq!(n.to_string(), "Nat.add_comm.1");
        assert_eq!(n.0[2], NameComp::Num(1));
        assert_eq!(Name::from_pce(&n.to_pce()).unwrap(), n);
    }
}
