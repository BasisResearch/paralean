//! Bounded, commit-ordered anti-entropy stream. The wire layer transports these PCE types;
//! this module owns their FDB cursor and materialization semantics.

use std::collections::BTreeMap;
use std::sync::Arc;

use foundationdb::options::{MutationType, StreamingMode};
use foundationdb::tuple::{Bytes, Versionstamp};
use foundationdb::{KeySelector, RangeOption, Transaction};

use crate::error::{Result, StoreError};
use crate::id::{sha256, Id, Kind, ReplicaId, WorkspaceId};
use crate::meta::{get, Keys, Step};
use crate::objects::*;
use crate::pce::{DResult, Dec, DecodeError, Enc, Pce};
use crate::faults::Txn;
use crate::group_chunks::unique_chunks;
use crate::antientropy::{self, Item, Outcome};
use crate::store::Store;
use crate::writer::Writer;
use crate::SignedJob;

const FORMAT: u64 = 0;
const MAX_PAGE_ITEMS: usize = 128;
const MAX_PAGE_BYTES: usize = 1024 * 1024;
const PART_FRAGMENT: usize = 64 * 1024;
const MAX_WIRE_OBJECT: u64 = 64 * 1024 * 1024;
/// Per-event receiver caps, enforced when a part is first persisted (`ae_save_progress`),
/// so before any object it names is fetched (W2 A-12). An event that would pass one is
/// archived as terminal in the same transaction. The part and inline caps are the ones
/// `ae_import_staged` re-checks.
pub const MAX_EVENT_PARTS: u64 = 8192;
pub const MAX_EVENT_INLINE_BYTES: u64 = 8 * 1024 * 1024;
/// Total stored-preimage length of the objects one event's ObjectRefs name.
pub const MAX_EVENT_OBJECT_BYTES: u64 = 4 * 1024 * 1024 * 1024;
/// Total declared object bytes of one source's active (not yet applied or archived) events.
/// A part that would pass it is refused without effect and retried after others drain.
pub const MAX_SOURCE_OBJECT_BYTES: u64 = 32 * 1024 * 1024 * 1024;

/// Running totals of one active event's staged parts (`aepartstat/<source>/<event>`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct PartStats { parts: u64, inline: u64, objects: u64 }
impl PartStats {
    fn decode(v: &[u8]) -> Result<Self> {
        let n = |i: usize| -> Result<u64> {
            Ok(u64::from_be_bytes(v.get(i * 8..i * 8 + 8).and_then(|s| s.try_into().ok())
                .ok_or_else(|| StoreError::Invalid("bad anti-entropy part statistics".into()))?))
        };
        if v.len() != 24 { return Err(StoreError::Invalid("bad anti-entropy part statistics".into())); }
        Ok(Self { parts: n(0)?, inline: n(1)?, objects: n(2)? })
    }
    fn encode(&self) -> Vec<u8> {
        [self.parts, self.inline, self.objects].iter().flat_map(|n| n.to_be_bytes()).collect()
    }
    /// The cap a new part `seq` would pass, if any; otherwise the totals including it.
    fn admit(&self, seq: u64, part: &AePart) -> std::result::Result<Self, String> {
        let mut next = *self;
        next.parts += 1;
        if !cfg!(feature = "mutate-ae-unbounded-parts") {
            if seq >= MAX_EVENT_PARTS || next.parts > MAX_EVENT_PARTS {
                return Err(format!("anti-entropy event exceeds {MAX_EVENT_PARTS} parts"));
            }
        }
        match part {
            AePart::MetaFragment { bytes, .. } | AePart::CertificateFragment { bytes, .. } => {
                next.inline += bytes.len() as u64;
                if !cfg!(feature = "mutate-ae-unbounded-parts") {
                    if bytes.len() > PART_FRAGMENT { return Err("anti-entropy fragment exceeds 64 KiB".into()); }
                    if next.inline > MAX_EVENT_INLINE_BYTES { return Err("anti-entropy event exceeds 8 MiB metadata cap".into()); }
                }
            }
            AePart::ObjectRef { length, .. } => {
                next.objects = next.objects.saturating_add(*length);
                if !cfg!(feature = "mutate-ae-unbounded-objects") {
                    if *length > MAX_WIRE_OBJECT { return Err("anti-entropy object reference exceeds the 64 MiB wire object cap".into()); }
                    if next.objects > MAX_EVENT_OBJECT_BYTES {
                        return Err(format!("anti-entropy event objects exceed the {} GiB cap", MAX_EVENT_OBJECT_BYTES >> 30));
                    }
                }
            }
        }
        Ok(next)
    }
}

fn format(e: &mut Enc) { e.uvarint(FORMAT); }
fn check_format(d: &mut Dec<'_>) -> DResult<()> {
    let v = d.uvarint()?;
    if v == FORMAT { Ok(()) } else { Err(DecodeError::Format(v)) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AeKind {
    GroupVariant { group: Id, marker: Id, cert: Id },
    Tombstone { id: Id, cert: Id },
    Catalogue { source: String, id: Id, cert: Id },
    Evidence { kind: String, object: Id, cert: Id },
}

impl Pce for AeKind {
    fn encode(&self, e: &mut Enc) {
        match self {
            Self::GroupVariant { group, marker, cert } => { e.byte(0); group.encode(e); marker.encode(e); cert.encode(e); }
            Self::Tombstone { id, cert } => { e.byte(1); id.encode(e); cert.encode(e); }
            Self::Catalogue { source, id, cert } => { e.byte(2).string(source); id.encode(e); cert.encode(e); }
            Self::Evidence { kind, object, cert } => { e.byte(3).string(kind); object.encode(e); cert.encode(e); }
        }
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(match d.byte()? {
            0 => Self::GroupVariant { group: Id::decode(d)?, marker: Id::decode(d)?, cert: Id::decode(d)? },
            1 => Self::Tombstone { id: Id::decode(d)?, cert: Id::decode(d)? },
            2 => Self::Catalogue { source: d.string()?, id: Id::decode(d)?, cert: Id::decode(d)? },
            3 => Self::Evidence { kind: d.string()?, object: Id::decode(d)?, cert: Id::decode(d)? },
            tag => return Err(DecodeError::UnknownTag { what: "anti-entropy event", tag }),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeEvent { pub key: Vec<u8>, pub kind: AeKind }
impl Pce for AeEvent {
    fn encode(&self, e: &mut Enc) { format(e); e.bytes(&self.key); self.kind.encode(e); }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> { check_format(d)?; Ok(Self { key: d.bytes()?.to_vec(), kind: AeKind::decode(d)? }) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AePage { pub generation: Id, pub events: Vec<AeEvent>, pub next: Option<Vec<u8>>, pub more: bool }
impl Pce for AePage {
    fn encode(&self, e: &mut Enc) { format(e); self.generation.encode(e); e.list(&self.events, |e, x| x.encode(e)); e.option(&self.next, |e, x| { e.bytes(x); }); e.bool(self.more); }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> { check_format(d)?; Ok(Self { generation: Id::decode(d)?, events: d.list(AeEvent::decode)?, next: d.option(|d| Ok(d.bytes()?.to_vec()))?, more: d.bool()? }) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AePart {
    MetaFragment { kind: String, id: Id, offset: u64, total: u64, bytes: Vec<u8> },
    ObjectRef { kind: Kind, id: Id, length: u64 },
    CertificateFragment { kind: String, id: Id, offset: u64, total: u64, bytes: Vec<u8> },
}
impl Pce for AePart {
    fn encode(&self, e: &mut Enc) {
        match self {
            Self::MetaFragment { kind, id, offset, total, bytes } => { e.byte(0).string(kind); id.encode(e); e.uvarint(*offset).uvarint(*total).bytes(bytes); }
            Self::ObjectRef { kind, id, length } => { e.byte(1).string(kind.name()); id.encode(e); e.uvarint(*length); }
            Self::CertificateFragment { kind, id, offset, total, bytes } => { e.byte(2).string(kind); id.encode(e); e.uvarint(*offset).uvarint(*total).bytes(bytes); }
        }
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        Ok(match d.byte()? {
            0 => Self::MetaFragment { kind: d.string()?, id: Id::decode(d)?, offset: d.uvarint()?, total: d.uvarint()?, bytes: d.bytes()?.to_vec() },
            1 => Self::ObjectRef { kind: Kind::from_name(&d.string()?).ok_or(DecodeError::Invalid("S3 kind"))?, id: Id::decode(d)?, length: d.uvarint()? },
            2 => Self::CertificateFragment { kind: d.string()?, id: Id::decode(d)?, offset: d.uvarint()?, total: d.uvarint()?, bytes: d.bytes()?.to_vec() },
            tag => return Err(DecodeError::UnknownTag { what: "anti-entropy part", tag }),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeBundlePage { pub event_key: Vec<u8>, pub after_part: Option<u64>, pub parts: Vec<(u64, AePart)>, pub next_part: Option<u64>, pub complete: bool }
impl Pce for AeBundlePage {
    fn encode(&self, e: &mut Enc) {
        format(e); e.bytes(&self.event_key); e.option(&self.after_part, |e, n| { e.uvarint(*n); });
        e.list(&self.parts, |e, (n, p)| { e.uvarint(*n); p.encode(e); });
        e.option(&self.next_part, |e, n| { e.uvarint(*n); }); e.bool(self.complete);
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        check_format(d)?;
        Ok(Self { event_key: d.bytes()?.to_vec(), after_part: d.option(Dec::uvarint)?, parts: d.list(|d| Ok((d.uvarint()?, AePart::decode(d)?)))?, next_part: d.option(Dec::uvarint)?, complete: d.bool()? })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PendingState { Collecting, Deferred(String), Terminal(String) }
impl Pce for PendingState {
    fn encode(&self, e: &mut Enc) { match self { Self::Collecting => { e.byte(0); }, Self::Deferred(s) => { e.byte(1).string(s); }, Self::Terminal(s) => { e.byte(2).string(s); } } }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> { Ok(match d.byte()? { 0 => Self::Collecting, 1 => Self::Deferred(d.string()?), 2 => Self::Terminal(d.string()?), tag => return Err(DecodeError::UnknownTag { what: "pending state", tag }) }) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AePending { pub source: String, pub generation: Id, pub event: AeEvent, pub next_part: Option<u64>, pub objects_after: Option<Vec<u8>>, pub missing_count: u64, pub state: PendingState, pub last_error: Option<String> }
impl Pce for AePending {
    fn encode(&self, e: &mut Enc) { format(e); e.string(&self.source); self.generation.encode(e); self.event.encode(e); e.option(&self.next_part, |e, n| { e.uvarint(*n); }); e.option(&self.objects_after, |e, x| { e.bytes(x); }); e.uvarint(self.missing_count); self.state.encode(e); e.option(&self.last_error, |e, x| { e.string(x); }); }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> { check_format(d)?; Ok(Self { source: d.string()?, generation: Id::decode(d)?, event: AeEvent::decode(d)?, next_part: d.option(Dec::uvarint)?, objects_after: d.option(|d| Ok(d.bytes()?.to_vec()))?, missing_count: d.uvarint()?, state: PendingState::decode(d)?, last_error: d.option(Dec::string)? }) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeProgress { pub generation: Id, pub cursor: Option<Vec<u8>> }
impl Pce for AeProgress {
    fn encode(&self, e: &mut Enc) { format(e); self.generation.encode(e); e.option(&self.cursor, |e, x| { e.bytes(x); }); }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> { check_format(d)?; Ok(Self { generation: Id::decode(d)?, cursor: d.option(|d| Ok(d.bytes()?.to_vec()))? }) }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AePendingPage { pub entries: Vec<AePending>, pub next: Option<Vec<u8>>, pub more: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeTerminalPage { pub entries: Vec<AePending>, pub next: Option<Vec<u8>>, pub more: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeObjectPage { pub refs: Vec<(Kind, Id, u64)>, pub next: Option<Vec<u8>>, pub more: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignCataloguePage { pub records: Vec<(Id, SignedRecord)>, pub next: Option<Vec<u8>>, pub more: bool }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AeIdentity { pub deployment: String, pub replica: ReplicaId, pub config_digest: Id, pub generation: Id, pub transport_public: [u8; 32] }

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FederationMember {
    pub replica: ReplicaId,
    pub transport_public: [u8; 32],
    pub authority: [u8; 32],
    pub writers: BTreeMap<WorkspaceId, [u8; 32]>,
    pub job_issuers: Vec<[u8; 32]>,
}
impl Pce for FederationMember {
    fn encode(&self, e: &mut Enc) {
        self.replica.encode(e); e.bytes(&self.transport_public).bytes(&self.authority);
        e.list(&self.writers.iter().collect::<Vec<_>>(), |e, (w, key)| { w.encode(e); e.bytes(*key); });
        e.list(&self.job_issuers, |e, key| { e.bytes(key); });
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        let replica = ReplicaId::decode(d)?;
        let transport_public = d.fixed::<32>("transport public key")?;
        let authority = d.fixed::<32>("authority key")?;
        let entries = d.list(|d| Ok((WorkspaceId::decode(d)?, d.fixed::<32>("writer key")?)))?;
        let writers: BTreeMap<_, _> = entries.iter().copied().collect();
        if writers.len() != entries.len() { return Err(DecodeError::Invalid("duplicate writer")); }
        let job_issuers = d.list(|d| d.fixed::<32>("job issuer key"))?;
        Ok(Self { replica, transport_public, authority, writers, job_issuers })
    }
}

/// Immutable federation roster. `deployment` selects the local member and is excluded from
/// the shared digest; all members pin the same roster and target-home map.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FederationConfig {
    pub deployment: String,
    pub members: BTreeMap<String, FederationMember>,
    pub target_homes: BTreeMap<Name, String>,
}
impl FederationConfig {
    pub fn digest(&self) -> Id {
        let mut e = Enc::new();
        e.raw(b"paralean\0v0/federation\0");
        e.uvarint(FORMAT);
        e.list(&self.members.iter().collect::<Vec<_>>(), |e, (name, member)| { e.string(name); member.encode(e); });
        e.list(&self.target_homes.iter().collect::<Vec<_>>(), |e, (name, home)| { name.encode(e); e.string(home); });
        Id(sha256(&e.out))
    }
    pub fn validate(&self) -> Result<()> {
        if self.members.len() < 2 || self.members.len() > 32 { return Err(StoreError::Invalid("federation needs 2–32 deployments".into())); }
        if !self.members.contains_key(&self.deployment) { return Err(StoreError::Invalid("local deployment absent from federation roster".into())); }
        if self.target_homes.values().any(|home| !self.members.contains_key(home)) { return Err(StoreError::Invalid("target home absent from federation roster".into())); }
        let mut owners = BTreeMap::new();
        let mut replicas = std::collections::BTreeSet::new();
        let mut transports = std::collections::BTreeSet::new();
        for (source, member) in &self.members {
            if source.is_empty() || source.len() > 128 || !source.bytes().all(|b| b.is_ascii_graphic()) {
                return Err(StoreError::Invalid("invalid federation deployment name".into()));
            }
            if !replicas.insert(member.replica) || !transports.insert(member.transport_public) {
                return Err(StoreError::Invalid("replica or transport key occurs in multiple federation members".into()));
            }
            for writer in member.writers.keys() {
                if owners.insert(writer, source).is_some() { return Err(StoreError::Invalid("writer ID occurs in multiple federation members".into())); }
            }
        }
        if self.target_homes.keys().any(|name| name.0.is_empty()) { return Err(StoreError::Invalid("empty target name".into())); }
        Ok(())
    }
}
impl Pce for FederationConfig {
    fn encode(&self, e: &mut Enc) {
        format(e); e.string(&self.deployment);
        e.list(&self.members.iter().collect::<Vec<_>>(), |e, (name, member)| { e.string(name); member.encode(e); });
        e.list(&self.target_homes.iter().collect::<Vec<_>>(), |e, (name, home)| { name.encode(e); e.string(home); });
    }
    fn decode(d: &mut Dec<'_>) -> DResult<Self> {
        check_format(d)?;
        let deployment = d.string()?;
        let members_list = d.list(|d| Ok((d.string()?, FederationMember::decode(d)?)))?;
        let homes_list = d.list(|d| Ok((Name::decode(d)?, d.string()?)))?;
        let members: BTreeMap<_, _> = members_list.iter().cloned().collect();
        let target_homes: BTreeMap<_, _> = homes_list.iter().cloned().collect();
        if members.len() != members_list.len() || target_homes.len() != homes_list.len() { return Err(DecodeError::Invalid("duplicate federation entry")); }
        Ok(Self { deployment, members, target_homes })
    }
}

impl Keys {
    pub fn ae_config(&self) -> Vec<u8> { self.root.pack(&("federation", "config")) }
    pub fn ae_log(&self) -> foundationdb::tuple::Subspace { self.sub("aelog") }
    pub fn ae_generation(&self) -> Vec<u8> { self.root.pack(&("aegeneration",)) }
    pub fn ae_cursor(&self, source: &str) -> Vec<u8> { self.root.pack(&("aecursor", source)) }
    pub fn ae_pending(&self, source: &str, event: &[u8]) -> Vec<u8> { self.root.pack(&("aepending", source, Bytes::from(event))) }
    pub fn ae_pending_sub(&self, source: &str) -> foundationdb::tuple::Subspace { self.root.subspace(&("aepending", source)) }
    pub fn ae_terminal(&self, source: &str, event: &[u8]) -> Vec<u8> { self.root.pack(&("aeterminal", source, Bytes::from(event))) }
    pub fn ae_terminal_sub(&self, source: &str) -> foundationdb::tuple::Subspace { self.root.subspace(&("aeterminal", source)) }
    pub fn ae_count(&self, source: &str) -> Vec<u8> { self.root.pack(&("aecount", source)) }
    pub fn ae_parts(&self, source: &str, event: &[u8]) -> foundationdb::tuple::Subspace { self.root.subspace(&("aepart", source, Bytes::from(event))) }
    pub fn ae_part(&self, source: &str, event: &[u8], seq: u64) -> Vec<u8> { self.ae_parts(source, event).pack(&(seq,)) }
    pub fn ae_part_stats(&self, source: &str, event: &[u8]) -> Vec<u8> { self.root.pack(&("aepartstat", source, Bytes::from(event))) }
    pub fn ae_source_bytes(&self, source: &str) -> Vec<u8> { self.root.pack(&("aesourcebytes", source)) }
    pub fn xcertv(&self, kind: &str, object: &Id, cert: &Id) -> Vec<u8> { self.root.pack(&("xcertv", kind, Bytes::from(&object.0[..]), Bytes::from(&cert.0[..]))) }
    pub fn xcertvs_of(&self, kind: &str, object: &Id) -> foundationdb::tuple::Subspace { self.root.subspace(&("xcertv", kind, Bytes::from(&object.0[..]))) }
    pub fn xcatalog(&self, source: &str, id: &Id) -> Vec<u8> { self.root.pack(&("xcatalog", source, Bytes::from(&id.0[..]))) }
    pub fn xcatalogs_of(&self, source: &str) -> foundationdb::tuple::Subspace { self.root.subspace(&("xcatalog", source)) }
    pub fn xrcert(&self, source: &str, id: &Id) -> Vec<u8> { self.root.pack(&("xrcert", source, Bytes::from(&id.0[..]))) }
    pub fn xtoken(&self, source: &str, rank: u64) -> Vec<u8> { self.root.pack(&("xtoken", source, rank)) }
    pub fn xocert(&self, source: &str, kind: Kind, id: &Id) -> Vec<u8> { self.root.pack(&("xocert", source, kind.name(), Bytes::from(&id.0[..]))) }
    pub fn xrevision(&self, source: &str, id: &Id) -> Vec<u8> { self.root.pack(&("xrevision", source, Bytes::from(&id.0[..]))) }
    pub fn jobproof(&self, group: &Id, marker: &Id, cert: &Id) -> Vec<u8> {
        self.root.pack(&("jobproof", Bytes::from(&group.0[..]), Bytes::from(&marker.0[..]), Bytes::from(&cert.0[..])))
    }
}

/// Read the persisted home map inside each metadata write transaction. This is intentionally
/// independent of a Store handle's construction time: pinning config races with a write.
pub(crate) async fn config_in_txn(trx: &Transaction, keys: &Keys) -> Result<Option<FederationConfig>> {
    get(trx, &keys.ae_config()).await?.map(|v| FederationConfig::from_pce(&v).map_err(StoreError::from)).transpose()
}

/// Append an immutable event at this transaction's commit version. A distinct user version
/// (or object suffix) allows multiple events in the same transaction.
pub(crate) fn append_event(trx: &Transaction, keys: &Keys, kind: &AeKind, ordinal: u16) {
    let key = keys.ae_log().pack_with_versionstamp(&(Versionstamp::incomplete(ordinal),));
    trx.atomic_op(&key, &kind.to_pce(), MutationType::SetVersionstampedKey);
}

impl Store {
    /// A source-ready foreign record. Foreign catalogue records never enter the local fence
    /// or local `rcert/` namespace.
    pub async fn foreign_record(&self, source: &str, id: &Id) -> Result<Option<SignedRecord>> {
        self.ae_check_source(source).await?;
        let cfg = self.ae_federation().await?.expect("source check requires config");
        let member = &cfg.members[source];
        let Some(bytes) = self.meta.get(self.meta.keys.xcatalog(source, id)).await? else { return Ok(None) };
        let rec = SignedRecord::from_bytes(&bytes)?;
        let Some(cert_bytes) = self.meta.get(self.meta.keys.xrcert(source, id)).await? else { return Ok(None) };
        let cert = CommitCert::from_bytes(&cert_bytes)?;
        if rec.id() != *id || rec.body.workspace != rec.body.token.holder
            || !member.writers.get(&rec.body.workspace).is_some_and(|key| rec.verify(key))
            || cert.body.catalog != *id || cert.body.token != rec.body.token || cert.body.replica != member.replica
            || !member.writers.get(&rec.body.token.holder).is_some_and(|key| cert.verify(key)) {
            return Err(StoreError::Invalid("cached foreign catalogue source proof invalid".into()));
        }
        Ok(Some(rec))
    }

    pub async fn foreign_catalogue_page(&self, source: &str, after: Option<Vec<u8>>, max_items: usize) -> Result<ForeignCataloguePage> {
        self.ae_check_source(source).await?;
        let (prefix, end) = self.meta.keys.xcatalogs_of(source).range();
        if after.as_ref().is_some_and(|key| key < &prefix || key >= &end) { return Err(StoreError::Invalid("foreign catalogue cursor outside source range".into())); }
        let start = after.clone().unwrap_or(prefix);
        let limit = max_items.clamp(1, MAX_PAGE_ITEMS);
        let (rows, more) = self.meta.read(move |trx| {
            let (start, end) = (start.clone(), end.clone());
            Box::pin(async move {
                let opt = RangeOption { limit: Some(limit), mode: StreamingMode::WantAll,
                    ..RangeOption::from((KeySelector::first_greater_than(start), KeySelector::first_greater_or_equal(end))) };
                let result = trx.get_range(&opt, 1, false).await?;
                Ok((result.iter().map(|kv| kv.key().to_vec()).collect::<Vec<_>>(), result.more()))
            })
        }).await?;
        let next = rows.last().cloned().or(after);
        let mut records = Vec::new();
        for key in rows {
            let (_, _, raw): (String, String, Bytes<'_>) = self.meta.keys.root.unpack(&key)
                .map_err(|e| StoreError::Invalid(format!("bad foreign catalogue key: {e}")))?;
            let id = Id(raw[..].try_into().map_err(|_| StoreError::Invalid("bad foreign catalogue ID".into()))?);
            if let Some(rec) = self.foreign_record(source, &id).await? { records.push((id, rec)); }
        }
        Ok(ForeignCataloguePage { records, next, more })
    }
    async fn ae_object_ref(&self, parts: &mut Vec<AePart>, kind: Kind, id: Id) -> Result<Vec<u8>> {
        // The wire length is an immutable part of the event. A mutable S3 HEAD length can
        // describe corrupt bytes; after repair that would strand the receiver with a stale
        // staged ObjectRef. Verify the content hash before fixing the length.
        let bytes = self.s3.get(kind, &id).await?.ok_or(StoreError::Missing { kind: "anti-entropy payload", id })?;
        let length = bytes.len() as u64;
        if length > MAX_WIRE_OBJECT { return Err(StoreError::Invalid(format!("{} {id} exceeds the 64 MiB wire object cap", kind.name()))); }
        parts.push(AePart::ObjectRef { kind, id, length });
        Ok(bytes)
    }

    /// Materialize one immutable event, then return a bounded page of stable numbered parts.
    /// Later certificates have their own events, so this never enumerates all certificates.
    pub async fn ae_materialize(&self, event: &AeEvent, after_part: Option<u64>, max_bytes: usize) -> Result<AeBundlePage> {
        let (prefix, end) = self.meta.keys.ae_log().range();
        if event.key < prefix || event.key >= end || self.meta.get(event.key.clone()).await?.as_deref() != Some(event.kind.to_pce().as_slice()) {
            return Err(StoreError::Invalid("unknown or mismatched anti-entropy event".into()));
        }
        let mut all = Vec::new();
        match &event.kind {
            AeKind::GroupVariant { group, marker, cert } => {
                let m = self.marker_variant(group, marker).await?.ok_or(StoreError::Missing { kind: "marker variant", id: *marker })?;
                push_meta(&mut all, "marker", *marker, &m.preimage())?;
                let receipt = self.receipt(&m.receipt).await?.ok_or(StoreError::Missing { kind: "receipt", id: m.receipt })?;
                push_meta(&mut all, "receipt", m.receipt, &receipt.to_bytes())?;
                let job_id = receipt.body.request.as_ref().and_then(|v| <[u8; 32]>::try_from(v.as_slice()).ok()).map(Id)
                    .ok_or_else(|| StoreError::Invalid("receipt has no job ID".into()))?;
                let job = self.meta.get(self.meta.keys.jobproof(group, marker, cert)).await?
                    .or(self.meta.get(self.meta.keys.job(&job_id)).await?)
                    .ok_or(StoreError::Missing { kind: "job proof", id: job_id })?;
                if SignedJob::from_bytes(&job)?.id() != job_id {
                    return Err(StoreError::Invalid("job proof does not match receipt request".into()));
                }
                push_meta(&mut all, "job", job_id, &job)?;
                let mut capsules = BTreeMap::new();
                for rid in &m.revisions {
                    let rev = self.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?;
                    push_meta(&mut all, "revision", *rid, &rev.preimage())?;
                    capsules.insert(rev.capsule, ());
                }
                let cert_bytes = self.meta.get(self.meta.keys.xcertv("cert", group, cert)).await?;
                let cert_bytes = match cert_bytes {
                    Some(bytes) => bytes,
                    None => self.certs(group).await?.into_iter().find(|c| c.id() == *cert && c.body.marker == *marker)
                        .ok_or_else(|| StoreError::Invalid("group event certificate unavailable".into()))?.to_bytes(),
                };
                push_cert(&mut all, "cert", *cert, &cert_bytes)?;
                let group_bytes = self.ae_object_ref(&mut all, Kind::Group, *group).await?;
                self.ae_object_ref(&mut all, Kind::StagedMarker, *marker).await?;
                for capsule in capsules.keys() { self.ae_object_ref(&mut all, Kind::Capsule, *capsule).await?; }
                let actual = unique_chunks(Kind::Group.domain().strip(&group_bytes)?)?;
                let stored = self.meta.get(self.meta.keys.group_chunks(group)).await?
                    .map(|index| decode_chunk_index(&index)).transpose()?;
                if actual != stored && (actual.is_some() || stored.is_some()) {
                    return Err(StoreError::Invalid("group chunk index differs from verified group manifest".into()));
                }
                if let Some(chunks) = actual {
                    for (chunk, length) in chunks { all.push(AePart::ObjectRef { kind: Kind::Chunk, id: chunk, length }); }
                }
            }
            AeKind::Tombstone { id, cert } => {
                let tomb = self.tombstone(id).await?.ok_or(StoreError::Missing { kind: "tombstone", id: *id })?;
                push_meta(&mut all, "tombstone", *id, &tomb.preimage())?;
                let cert_bytes = match self.meta.get(self.meta.keys.xcertv("tcert", id, cert)).await? {
                    Some(bytes) => bytes,
                    None => self.tcerts(id).await?.into_iter().find(|c| c.id() == *cert)
                        .ok_or_else(|| StoreError::Invalid("tombstone event certificate unavailable".into()))?.to_bytes(),
                };
                push_cert(&mut all, "tcert", *cert, &cert_bytes)?;
                self.ae_object_ref(&mut all, Kind::StagedTombstone, *id).await?;
            }
            AeKind::Catalogue { source, id, cert } => {
                let origin = if source.is_empty() { &self.deployment } else { source };
                let local = origin == &self.deployment;
                let rec_bytes = self.meta.get(if local { self.meta.keys.catalog(id) } else { self.meta.keys.xcatalog(origin, id) }).await?
                    .ok_or(StoreError::Missing { kind: "catalogue", id: *id })?;
                let rec = SignedRecord::from_bytes(&rec_bytes)?;
                if rec.id() != *id { return Err(StoreError::Invalid("catalogue record ID mismatch".into())); }
                let cert_bytes = self.meta.get(if local { self.meta.keys.rcert(id) } else { self.meta.keys.xrcert(origin, id) }).await?
                    .ok_or(StoreError::Missing { kind: "commit certificate", id: *cert })?;
                let found = CommitCert::from_bytes(&cert_bytes)?;
                if found.id() != *cert { return Err(StoreError::Invalid("catalogue event certificate unavailable".into())); }
                let token_bytes = self.meta.get(if local { self.meta.keys.token(rec.body.token.rank) } else { self.meta.keys.xtoken(origin, rec.body.token.rank) }).await?
                    .ok_or_else(|| StoreError::Invalid("catalogue event lacks source token".into()))?;
                push_meta(&mut all, "catalogue", *id, &rec.to_bytes())?;
                push_cert(&mut all, "rcert", *cert, &found.to_bytes())?;
                push_meta(&mut all, "token", Id(sha256(&token_bytes)), &token_bytes)?;
                self.ae_object_ref(&mut all, Kind::Snapshot, rec.body.snapshot).await?;
                let snapshot = self.s3.get_object::<Snapshot>(Kind::Snapshot, &rec.body.snapshot).await?
                    .ok_or(StoreError::Missing { kind: "snapshot", id: rec.body.snapshot })?;
                let mut objects = vec![(Kind::Snapshot, rec.body.snapshot), (Kind::Manifest, snapshot.source_root), (Kind::Manifest, snapshot.build_receipt)];
                let mut chunk_refs = BTreeMap::new();
                for rid in &snapshot.contents {
                    let rev_bytes = if local {
                        self.revision(rid).await?.ok_or(StoreError::Missing { kind: "revision", id: *rid })?.preimage()
                    } else {
                        self.meta.get(self.meta.keys.xrevision(origin, rid)).await?
                            .ok_or(StoreError::Missing { kind: "revision", id: *rid })?
                    };
                    let rev = Revision::from_preimage(&rev_bytes)?;
                    if rev.id() != *rid { return Err(StoreError::Invalid("catalogue revision ID mismatch".into())); }
                    push_meta(&mut all, "catalogue-revision", *rid, &rev_bytes)?;
                    objects.push((Kind::Group, rev.group));
                    objects.push((Kind::Capsule, rev.capsule));
                }
                objects.sort(); objects.dedup();
                for (kind, object) in objects {
                    if kind != Kind::Snapshot {
                        let bytes = self.ae_object_ref(&mut all, kind, object).await?;
                        if kind == Kind::Group {
                            let actual = unique_chunks(Kind::Group.domain().strip(&bytes)?)?;
                            let stored = self.meta.get(self.meta.keys.group_chunks(&object)).await?
                                .map(|index| decode_chunk_index(&index)).transpose()?;
                            if actual != stored && (actual.is_some() || stored.is_some()) {
                                return Err(StoreError::Invalid("catalogue group chunk index differs from verified manifest".into()));
                            }
                            if let Some(chunks) = actual {
                                for (chunk, length) in chunks {
                                    if chunk_refs.insert(chunk, length).is_some_and(|old| old != length) {
                                        return Err(StoreError::Invalid("chunk has conflicting manifest lengths".into()));
                                    }
                                }
                            }
                        }
                    }
                    let ocert_bytes = self.meta.get(if local { self.meta.keys.ocert(kind, &object) } else { self.meta.keys.xocert(origin, kind, &object) }).await?
                        .ok_or_else(|| StoreError::Invalid(format!("catalogue event lacks {} object certificate", kind.name())))?;
                    let ocert = ObjectCert::from_bytes(&ocert_bytes)?;
                    push_cert(&mut all, &format!("ocert/{}", kind.name()), ocert.id(), &ocert_bytes)?;
                }
                for (chunk, length) in chunk_refs { all.push(AePart::ObjectRef { kind: Kind::Chunk, id: chunk, length }); }
            }
            AeKind::Evidence { kind, object, cert } => {
                let bytes = if let Some(v) = self.meta.get(self.meta.keys.xcertv(kind, object, cert)).await? { Some(v) } else if kind == "cert" {
                    self.certs(object).await?.into_iter().find(|c| c.id() == *cert).map(|c| c.to_bytes())
                } else if kind == "tcert" {
                    self.tcerts(object).await?.into_iter().find(|c| c.id() == *cert).map(|c| c.to_bytes())
                } else if let Some(s3_kind) = kind.strip_prefix("ocert/").and_then(Kind::from_name) {
                    self.valid_ocert(s3_kind, object).await?.filter(|c| c.id() == *cert).map(|c| c.to_bytes())
                } else { None }.ok_or(StoreError::Missing { kind: "certificate evidence", id: *cert })?;
                push_cert(&mut all, kind, *cert, &bytes)?;
            }
        }
        let max = max_bytes.clamp(256, MAX_PAGE_BYTES);
        let mut size = 0;
        let mut parts = Vec::new();
        let total = all.len();
        for (seq, part) in all.into_iter().enumerate() {
            if after_part.is_some_and(|n| seq as u64 <= n) { continue; }
            let cost = part.to_pce().len() + 12;
            if parts.len() >= MAX_PAGE_ITEMS - 1 { break; }
            if !parts.is_empty() && size + cost > max { break; }
            if cost > max { return Err(StoreError::Invalid("anti-entropy requested page too small for one part".into())); }
            if cost > MAX_PAGE_BYTES { return Err(StoreError::Invalid("anti-entropy part exceeds maximum".into())); }
            size += cost;
            parts.push((seq as u64, part));
        }
        let next_part = parts.last().map(|(seq, _)| *seq).or(after_part);
        let complete = next_part.is_some_and(|n| n as usize + 1 >= total) || total == 0;
        Ok(AeBundlePage { event_key: event.key.clone(), after_part, parts, next_part, complete })
    }

    pub async fn ae_missing_objects(&self, source: &str, event: &AeEvent, after: Option<Vec<u8>>, max_items: usize) -> Result<AeObjectPage> {
        self.ae_check_source(source).await?;
        let (prefix, end) = self.meta.keys.ae_parts(source, &event.key).range();
        if after.as_ref().is_some_and(|k| k < &prefix || k >= &end) { return Err(StoreError::Invalid("object cursor outside event range".into())); }
        let start = after.clone().unwrap_or(prefix);
        let limit = max_items.clamp(1, MAX_PAGE_ITEMS);
        let (rows, more) = self.meta.read(move |trx| {
            let (start, end) = (start.clone(), end.clone());
            Box::pin(async move {
                let opt = RangeOption { limit: Some(limit), mode: StreamingMode::WantAll,
                    ..RangeOption::from((KeySelector::first_greater_than(start), KeySelector::first_greater_or_equal(end))) };
                let r = trx.get_range(&opt, 1, false).await?;
                Ok((r.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect::<Vec<_>>(), r.more()))
            })
        }).await?;
        let next = rows.last().map(|(k, _)| k.clone()).or(after);
        let mut refs = Vec::new();
        for (_, value) in rows {
            if let AePart::ObjectRef { kind, id, length } = AePart::from_pce(&value)? {
                if self.s3.get_acked(kind, &id).await?.is_none_or(|(_, bytes)| bytes.len() as u64 != length) { refs.push((kind, id, length)); }
            }
        }
        Ok(AeObjectPage { refs, next, more })
    }

    async fn ae_check_source(&self, source: &str) -> Result<()> {
        let cfg = self.ae_federation().await?.ok_or_else(|| StoreError::Invalid("federation config is not pinned".into()))?;
        if !cfg.members.contains_key(source) { return Err(StoreError::Invalid(format!("unknown anti-entropy source {source}"))); }
        Ok(())
    }

    pub async fn ae_progress(&self, source: &str) -> Result<Option<AeProgress>> {
        self.ae_check_source(source).await?;
        self.meta.get(self.meta.keys.ae_cursor(source)).await?.map(|v| AeProgress::from_pce(&v).map_err(StoreError::from)).transpose()
    }

    /// Record a retryable materialization/import error without overwriting a newer pending
    /// cursor or state from another worker. The event remains eligible for replay.
    pub async fn ae_note_error(&self, source: &str, event: &AeEvent, why: &str) -> Result<()> {
        self.ae_check_source(source).await?;
        let mut bounded = why.to_owned();
        while bounded.len() > 4096 { bounded.pop(); }
        let key = self.meta.keys.ae_pending(source, &event.key);
        self.meta.run(Txn::Ae, Box::new(move |trx| {
            let (key, bounded) = (key.clone(), bounded.clone());
            Box::pin(async move {
                let Some(bytes) = get(trx, &key).await? else { return Ok(Step::Done(())); };
                let mut pending = AePending::from_pce(&bytes)?;
                pending.last_error = Some(bounded);
                trx.set(&key, &pending.to_pce());
                Ok(Step::Commit(()))
            })
        })).await
    }

    pub async fn ae_pending_page(&self, source: &str, after: Option<Vec<u8>>, max_items: usize) -> Result<AePendingPage> {
        self.ae_check_source(source).await?;
        let (prefix, end) = self.meta.keys.ae_pending_sub(source).range();
        if after.as_ref().is_some_and(|k| k < &prefix || k >= &end) { return Err(StoreError::Invalid("pending cursor outside source range".into())); }
        let start = after.clone().unwrap_or(prefix);
        let limit = max_items.clamp(1, MAX_PAGE_ITEMS);
        let (rows, more) = self.meta.read(move |trx| {
            let (start, end) = (start.clone(), end.clone());
            Box::pin(async move {
                let opt = RangeOption { limit: Some(limit), mode: StreamingMode::WantAll,
                    ..RangeOption::from((KeySelector::first_greater_than(start), KeySelector::first_greater_or_equal(end))) };
                let r = trx.get_range(&opt, 1, false).await?;
                Ok((r.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect::<Vec<_>>(), r.more()))
            })
        }).await?;
        let next = rows.last().map(|(k, _)| k.clone()).or(after);
        let entries = rows.into_iter().map(|(_, v)| AePending::from_pce(&v).map_err(StoreError::from)).collect::<Result<_>>()?;
        Ok(AePendingPage { entries, next, more })
    }

    /// Archived terminal diagnostics do not occupy an active pending slot. The archive is
    /// retained indefinitely and paged separately from retryable work.
    pub async fn ae_terminal_page(&self, source: &str, after: Option<Vec<u8>>, max_items: usize) -> Result<AeTerminalPage> {
        self.ae_check_source(source).await?;
        let (prefix, end) = self.meta.keys.ae_terminal_sub(source).range();
        if after.as_ref().is_some_and(|k| k < &prefix || k >= &end) { return Err(StoreError::Invalid("terminal cursor outside source range".into())); }
        let start = after.clone().unwrap_or(prefix);
        let limit = max_items.clamp(1, MAX_PAGE_ITEMS);
        let (rows, more) = self.meta.read(move |trx| {
            let (start, end) = (start.clone(), end.clone());
            Box::pin(async move {
                let opt = RangeOption { limit: Some(limit), mode: StreamingMode::WantAll,
                    ..RangeOption::from((KeySelector::first_greater_than(start), KeySelector::first_greater_or_equal(end))) };
                let r = trx.get_range(&opt, 1, false).await?;
                Ok((r.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect::<Vec<_>>(), r.more()))
            })
        }).await?;
        let next = rows.last().map(|(k, _)| k.clone()).or(after);
        let entries = rows.into_iter().map(|(_, v)| {
            let p = AePending::from_pce(&v)?;
            if !matches!(p.state, PendingState::Terminal(_)) { return Err(StoreError::Invalid("terminal archive holds active state".into())); }
            Ok(p)
        }).collect::<Result<_>>()?;
        Ok(AeTerminalPage { entries, next, more })
    }

    pub async fn ae_active_pending_count(&self, source: &str) -> Result<u64> {
        self.ae_check_source(source).await?;
        match self.meta.get(self.meta.keys.ae_count(source)).await? {
            None => Ok(0),
            Some(bytes) => Ok(u64::from_be_bytes(bytes.as_slice().try_into()
                .map_err(|_| StoreError::Invalid("bad active anti-entropy pending count".into()))?)),
        }
    }

    /// Atomically persist a bounded receiver batch. The cursor never moves backwards and the
    /// generation is immutable for this peer. Terminal upserts move to a durable diagnostic
    /// archive while freeing their active pending slot and staged fragments in this transaction.
    ///
    /// A new part is admitted only within its event's caps (`MAX_EVENT_*`): an event that
    /// would pass one is archived as terminal here, its staged parts cleared, and its key is
    /// returned; nothing it names is fetched afterwards. Its pending row must be in this batch
    /// or already stored. A part that would pass the source's `MAX_SOURCE_OBJECT_BYTES`
    /// refuses the whole batch (retryable once other events of the source drain).
    pub async fn ae_save_progress(
        &self, source: &str, generation: Id, cursor: Option<Vec<u8>>,
        pending_upserts: &[AePending], pending_deletes: &[Vec<u8>],
        part_upserts: &[(Vec<u8>, u64, AePart)],
    ) -> Result<Vec<Vec<u8>>> {
        self.ae_check_source(source).await?;
        if pending_upserts.len() + pending_deletes.len() + part_upserts.len() > MAX_PAGE_ITEMS {
            return Err(StoreError::Invalid("anti-entropy progress batch too large".into()));
        }
        if pending_upserts.iter().any(|p| p.source != source || p.generation != generation) {
            return Err(StoreError::Invalid("pending source or generation mismatch".into()));
        }
        let (keys, source, cursor) = (self.meta.keys.clone(), source.to_owned(), cursor.clone());
        let (upserts, deletes, parts) = (Arc::new(pending_upserts.to_vec()), Arc::new(pending_deletes.to_vec()), Arc::new(part_upserts.to_vec()));
        self.meta.run(Txn::Ae, Box::new(move |trx| {
            let (keys, source, cursor, upserts, deletes, parts) = (keys.clone(), source.clone(), cursor.clone(), upserts.clone(), deletes.clone(), parts.clone());
            Box::pin(async move {
                let ckey = keys.ae_cursor(&source);
                let old = get(trx, &ckey).await?.map(|v| AeProgress::from_pce(&v)).transpose()?;
                if let Some(o) = &old {
                    if o.generation != generation { return Err(StoreError::Invalid("source generation changed".into())); }
                    if let (Some(prev), Some(next)) = (&o.cursor, &cursor) {
                        if next < prev { return Err(StoreError::Invalid("anti-entropy cursor regressed".into())); }
                    }
                    if o.cursor.is_some() && cursor.is_none() { return Err(StoreError::Invalid("anti-entropy cursor cleared".into())); }
                }
                let count_key = keys.ae_count(&source);
                let mut count = get(trx, &count_key).await?.map(|v| u64::from_be_bytes(v.try_into().unwrap_or([0; 8]))).unwrap_or(0);
                let source_key = keys.ae_source_bytes(&source);
                let mut source_bytes = get(trx, &source_key).await?.map(|v| u64::from_be_bytes(v.try_into().unwrap_or([0; 8]))).unwrap_or(0);
                // Freeing an event's staged parts also frees its share of the source budget.
                let release = |event: Vec<u8>| {
                    let stats_key = keys.ae_part_stats(&source, &event);
                    async move {
                        let freed = get(trx, &stats_key).await?.map(|v| PartStats::decode(&v)).transpose()?.unwrap_or_default().objects;
                        trx.clear(&stats_key);
                        Ok::<u64, StoreError>(freed)
                    }
                };
                for p in upserts.iter() {
                    let key = keys.ae_pending(&source, &p.event.key);
                    let terminal_key = keys.ae_terminal(&source, &p.event.key);
                    if let PendingState::Terminal(_) = &p.state {
                        if get(trx, &terminal_key).await?.is_none() {
                            trx.set(&terminal_key, &p.to_pce());
                        }
                        if get(trx, &key).await?.is_some() {
                            count = count.saturating_sub(1);
                            trx.clear(&key);
                        }
                        let (start, end) = keys.ae_parts(&source, &p.event.key).range();
                        trx.clear_range(&start, &end);
                        source_bytes = source_bytes.saturating_sub(release(p.event.key.clone()).await?);
                        continue;
                    }
                    // A stale worker must not resurrect an event already archived by
                    // another worker; the first terminal diagnosis is retained.
                    if get(trx, &terminal_key).await?.is_some() { continue; }
                    if get(trx, &key).await?.is_none() {
                        count += 1;
                        if count > 10_000 { return Err(StoreError::Invalid("anti-entropy pending quota exhausted".into())); }
                    }
                    trx.set(&key, &p.to_pce());
                }
                for event in deletes.iter() {
                    let key = keys.ae_pending(&source, event);
                    if get(trx, &key).await?.is_some() { count = count.saturating_sub(1); trx.clear(&key); }
                    let (start, end) = keys.ae_parts(&source, event).range();
                    trx.clear_range(&start, &end);
                    source_bytes = source_bytes.saturating_sub(release(event.clone()).await?);
                }
                let mut stats: BTreeMap<Vec<u8>, PartStats> = BTreeMap::new();
                let mut capped: Vec<Vec<u8>> = Vec::new();
                for (event, seq, part) in parts.iter() {
                    if capped.contains(event) || get(trx, &keys.ae_terminal(&source, event)).await?.is_some()
                        || deletes.iter().any(|deleted| deleted == event) {
                        continue;
                    }
                    let key = keys.ae_part(&source, event, *seq);
                    let value = part.to_pce();
                    if let Some(old) = get(trx, &key).await? {
                        if old != value { return Err(StoreError::Invalid("anti-entropy part changed during replay".into())); }
                        continue;
                    }
                    let current = match stats.get(event) {
                        Some(s) => *s,
                        None => get(trx, &keys.ae_part_stats(&source, event)).await?.map(|v| PartStats::decode(&v)).transpose()?.unwrap_or_default(),
                    };
                    match current.admit(*seq, part) {
                        Ok(next) => {
                            source_bytes = source_bytes.saturating_add(next.objects - current.objects);
                            if source_bytes > MAX_SOURCE_OBJECT_BYTES && !cfg!(feature = "mutate-ae-unbounded-source") {
                                return Err(StoreError::Invalid(format!(
                                    "anti-entropy source {source} has {} GiB of pending objects; retry after its events drain",
                                    MAX_SOURCE_OBJECT_BYTES >> 30)));
                            }
                            stats.insert(event.clone(), next);
                            trx.set(&key, &value);
                        }
                        Err(why) => {
                            // Archive the event as terminal now: its parts are cleared and
                            // nothing it names is fetched.
                            let pending_key = keys.ae_pending(&source, event);
                            let mut entry = match upserts.iter().rev().find(|p| &p.event.key == event) {
                                Some(p) => p.clone(),
                                None => AePending::from_pce(&get(trx, &pending_key).await?.ok_or_else(||
                                    StoreError::Invalid("anti-entropy parts for an event that is not pending".into()))?)?,
                            };
                            entry.state = PendingState::Terminal(why);
                            let terminal_key = keys.ae_terminal(&source, event);
                            if get(trx, &terminal_key).await?.is_none() { trx.set(&terminal_key, &entry.to_pce()); }
                            if get(trx, &pending_key).await?.is_some() { count = count.saturating_sub(1); trx.clear(&pending_key); }
                            let (start, end) = keys.ae_parts(&source, event).range();
                            trx.clear_range(&start, &end);
                            // The cached totals include the stored ones and this batch's.
                            let stored = release(event.clone()).await?;
                            let total = stats.remove(event).map_or(stored, |s| s.objects);
                            source_bytes = source_bytes.saturating_sub(total);
                            capped.push(event.clone());
                        }
                    }
                }
                for (event, s) in &stats {
                    trx.set(&keys.ae_part_stats(&source, event), &s.encode());
                }
                trx.set(&count_key, &count.to_be_bytes());
                trx.set(&source_key, &source_bytes.to_be_bytes());
                trx.set(&ckey, &AeProgress { generation, cursor }.to_pce());
                Ok(Step::Commit(capped))
            })
        })).await
    }

    pub async fn ae_federation(&self) -> Result<Option<FederationConfig>> {
        self.meta.get(self.meta.keys.ae_config()).await?.map(|v| FederationConfig::from_pce(&v).map_err(StoreError::from)).transpose()
    }

    pub async fn ae_identity(&self) -> Result<AeIdentity> {
        let cfg = self.ae_federation().await?.ok_or_else(|| StoreError::Invalid("federation config is not pinned".into()))?;
        cfg.validate()?;
        let member = cfg.members.get(&self.deployment).ok_or_else(|| StoreError::Invalid("local federation member missing".into()))?;
        let generation = self.meta.get(self.meta.keys.ae_generation()).await?.ok_or_else(|| StoreError::Invalid("anti-entropy generation is not initialized".into()))?;
        let generation = Id(<[u8; 32]>::try_from(generation.as_slice()).map_err(|_| StoreError::Invalid("bad anti-entropy generation".into()))?);
        Ok(AeIdentity { deployment: self.deployment.clone(), replica: self.replica, config_digest: cfg.digest(), generation, transport_public: member.transport_public })
    }

    /// Pin only an empty deployment. Every subsequent publication transaction re-reads this
    /// key, so already-opened Store handles cannot bypass the home rule.
    pub async fn ae_pin_config(&self, cfg: &FederationConfig) -> Result<AeIdentity> {
        cfg.validate()?;
        if cfg.deployment != self.deployment { return Err(StoreError::Invalid("config selects another deployment".into())); }
        let own = &cfg.members[&self.deployment];
        if own.replica != self.replica || own.authority != self.ring.authority {
            return Err(StoreError::Invalid("local federation keys or replica differ from store".into()));
        }
        for member in cfg.members.values() {
            for (writer, key) in &member.writers {
                if self.ring.writers.get(writer) != Some(key) {
                    return Err(StoreError::Invalid("federation writer key differs from trusted store ring".into()));
                }
            }
        }
        let (keys, value, generation) = (self.meta.keys.clone(), cfg.to_pce(), Id(rand::random()));
        self.meta.run(Txn::Ae, Box::new(move |trx| {
            let (keys, value) = (keys.clone(), value.clone());
            Box::pin(async move {
                if let Some(existing) = get(trx, &keys.ae_config()).await? {
                    if existing == value { return Ok(Step::Done(())); }
                    return Err(StoreError::Invalid("federation config already pinned differently".into()));
                }
                let (begin, end) = keys.root.range();
                let opt = RangeOption { limit: Some(1), ..RangeOption::from((KeySelector::first_greater_or_equal(begin), KeySelector::first_greater_or_equal(end))) };
                if !trx.get_range(&opt, 1, false).await?.is_empty() {
                    return Err(StoreError::Invalid("cannot pin federation: deployment metadata already exists; explicit migration required".into()));
                }
                trx.set(&keys.ae_config(), &value);
                trx.set(&keys.ae_generation(), &generation.0);
                Ok(Step::Commit(()))
            })
        })).await?;
        self.ae_identity().await
    }
    /// One bounded descriptor page. The read has one FDB read version; `after` is exclusive.
    pub async fn ae_page(&self, after: Option<Vec<u8>>, max_items: usize, max_bytes: usize) -> Result<AePage> {
        let keys = self.meta.keys.clone();
        let (prefix, prefix_end) = keys.ae_log().range();
        if after.as_ref().is_some_and(|k| k < &prefix || k >= &prefix_end) { return Err(StoreError::Invalid("anti-entropy cursor outside log range".into())); }
        let limit = max_items.clamp(1, MAX_PAGE_ITEMS);
        let byte_limit = max_bytes.clamp(256, MAX_PAGE_BYTES);
        let generation = self.meta.get(keys.ae_generation()).await?.ok_or_else(|| StoreError::Invalid("anti-entropy generation is not initialized".into()))?;
        let generation = Id(<[u8; 32]>::try_from(generation.as_slice()).map_err(|_| StoreError::Invalid("bad anti-entropy generation".into()))?);
        let (prefix, end) = keys.ae_log().range();
        let start = after.clone().unwrap_or(prefix);
        let (raw, fdb_more) = self.meta.read(move |trx| {
            let (start, end) = (start.clone(), end.clone());
            Box::pin(async move {
                let opt = RangeOption { limit: Some(limit), mode: StreamingMode::WantAll,
                    ..RangeOption::from((KeySelector::first_greater_than(start), KeySelector::first_greater_or_equal(end))) };
                let rows = trx.get_range(&opt, 1, false).await?;
                Ok((rows.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect::<Vec<_>>(), rows.more()))
            })
        }).await?;
        let mut events = Vec::new();
        let mut size = 0;
        let mut more = fdb_more;
        for (key, value) in raw {
            let event = AeEvent { key, kind: AeKind::from_pce(&value)? };
            let cost = event.to_pce().len();
            if !events.is_empty() && size + cost > byte_limit { more = true; break; }
            if cost > MAX_PAGE_BYTES { return Err(StoreError::Invalid("anti-entropy event descriptor exceeds maximum".into())); }
            size += cost;
            events.push(event);
        }
        let next = events.last().map(|e| e.key.clone()).or(after);
        Ok(AePage { generation, events, next, more })
    }
}

fn decode_chunk_index(index: &[u8]) -> Result<BTreeMap<Id, u64>> {
    let mut dec = Dec::new(index);
    let chunks = dec.list(|d| Ok((Id::decode(d)?, d.uvarint()?)))?;
    if dec.remaining() != 0 { return Err(StoreError::Invalid("trailing group chunk index bytes".into())); }
    let mut unique = BTreeMap::new();
    for (id, length) in chunks {
        if unique.insert(id, length).is_some_and(|old| old != length) {
            return Err(StoreError::Invalid("chunk has conflicting index lengths".into()));
        }
    }
    Ok(unique)
}

fn push_meta(out: &mut Vec<AePart>, kind: &str, id: Id, bytes: &[u8]) -> Result<()> {
    if bytes.len() + event_inline_bytes(out) > 8 * 1024 * 1024 {
        return Err(StoreError::Invalid("anti-entropy event metadata exceeds 8 MiB cap".into()));
    }
    for (i, chunk) in bytes.chunks(PART_FRAGMENT).enumerate() {
        out.push(AePart::MetaFragment { kind: kind.into(), id, offset: (i * PART_FRAGMENT) as u64, total: bytes.len() as u64, bytes: chunk.to_vec() });
    }
    Ok(())
}
fn push_cert(out: &mut Vec<AePart>, kind: &str, id: Id, bytes: &[u8]) -> Result<()> {
    if bytes.len() + event_inline_bytes(out) > 8 * 1024 * 1024 {
        return Err(StoreError::Invalid("anti-entropy event metadata exceeds 8 MiB cap".into()));
    }
    for (i, chunk) in bytes.chunks(PART_FRAGMENT).enumerate() {
        out.push(AePart::CertificateFragment { kind: kind.into(), id, offset: (i * PART_FRAGMENT) as u64, total: bytes.len() as u64, bytes: chunk.to_vec() });
    }
    Ok(())
}

fn event_inline_bytes(parts: &[AePart]) -> usize {
    parts.iter().map(|part| match part {
        AePart::MetaFragment { bytes, .. } | AePart::CertificateFragment { bytes, .. } => bytes.len(),
        AePart::ObjectRef { .. } => 0,
    }).sum()
}

fn assemble_fragments(parts: &[AePart], certificate: bool) -> Result<BTreeMap<(String, Id), Vec<u8>>> {
    let mut fragments: BTreeMap<(String, Id), Vec<(u64, u64, Vec<u8>)>> = BTreeMap::new();
    for part in parts {
        match part {
            AePart::MetaFragment { kind, id, offset, total, bytes } if !certificate => {
                fragments.entry((kind.clone(), *id)).or_default().push((*offset, *total, bytes.clone()));
            }
            AePart::CertificateFragment { kind, id, offset, total, bytes } if certificate => {
                fragments.entry((kind.clone(), *id)).or_default().push((*offset, *total, bytes.clone()));
            }
            _ => {}
        }
    }
    let mut out = BTreeMap::new();
    for (key, mut chunks) in fragments {
        chunks.sort_by_key(|c| c.0);
        let mut bytes = Vec::new();
        let total = chunks[0].1;
        if total > 64 * 1024 * 1024 { return Err(StoreError::Invalid("anti-entropy metadata exceeds object limit".into())); }
        for (offset, declared, part) in chunks {
            if declared != total || offset != bytes.len() as u64 { return Err(StoreError::Invalid("anti-entropy metadata fragment gap or conflict".into())); }
            bytes.extend_from_slice(&part);
        }
        if bytes.len() as u64 != total { return Err(StoreError::Invalid("incomplete anti-entropy metadata fragments".into())); }
        out.insert(key, bytes);
    }
    Ok(out)
}

impl Writer {
    /// Apply one fully staged event after the service has fetched all missing S3 objects.
    /// Partial events stay in the durable queue. The underlying T9/T10 operations are
    /// idempotent, so a crash after import but before cursor cleanup safely replays.
    pub async fn ae_import_staged(&self, source: &str, event: &AeEvent) -> Result<Outcome> {
        self.store.ae_check_source(source).await?;
        let sub = self.store.meta.keys.ae_parts(source, &event.key);
        let (mut start, end) = sub.range();
        let mut parts = Vec::new();
        let mut expected_seq = 0u64;
        let mut total_inline = 0usize;
        loop {
            let (rows, more) = self.store.meta.read({
                let (start, end) = (start.clone(), end.clone());
                move |trx| {
                    let (start, end) = (start.clone(), end.clone());
                    Box::pin(async move {
                        let opt = RangeOption { limit: Some(MAX_PAGE_ITEMS), mode: StreamingMode::WantAll,
                            ..RangeOption::from((KeySelector::first_greater_than(start), KeySelector::first_greater_or_equal(end))) };
                        let result = trx.get_range(&opt, 1, false).await?;
                        Ok((result.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect::<Vec<_>>(), result.more()))
                    })
                }
            }).await?;
            if rows.is_empty() { break; }
            for (key, value) in rows {
                let (seq,): (u64,) = sub.unpack(&key)
                    .map_err(|e| StoreError::Invalid(format!("bad event part key: {e}")))?;
                if seq != expected_seq { return Ok(Outcome::Deferred("anti-entropy event part gap".into())); }
                expected_seq += 1;
                if expected_seq > 8192 { return Ok(Outcome::Rejected("anti-entropy event exceeds 8192 parts".into())); }
                let part = AePart::from_pce(&value)?;
                total_inline += match &part {
                    AePart::MetaFragment { bytes, .. } | AePart::CertificateFragment { bytes, .. } => bytes.len(),
                    AePart::ObjectRef { .. } => 0,
                };
                if total_inline > 8 * 1024 * 1024 { return Ok(Outcome::Rejected("anti-entropy event exceeds 8 MiB metadata cap".into())); }
                start = key;
                parts.push(part);
            }
            if !more { break; }
        }
        if parts.is_empty() { return Ok(Outcome::Deferred("anti-entropy event parts are absent".into())); }
        for part in &parts {
            if let AePart::ObjectRef { kind, id, length } = part {
                if self.store.s3.get_acked(*kind, id).await?.is_none_or(|(_, bytes)| bytes.len() as u64 != *length) {
                    return Ok(Outcome::Deferred(format!("{} {id} not acknowledged locally", kind.name())));
                }
            }
        }
        let meta = assemble_fragments(&parts, false)?;
        let certs = assemble_fragments(&parts, true)?;
        match &event.kind {
            AeKind::GroupVariant { group, marker, cert } => {
                let marker_bytes = meta.get(&("marker".into(), *marker)).ok_or_else(|| StoreError::Invalid("group event lacks marker".into()))?;
                let m = Marker::from_preimage(marker_bytes)?;
                if m.group != *group { return Ok(Outcome::Rejected("group event marker names another group".into())); }
                let receipt = meta.get(&("receipt".into(), m.receipt)).ok_or_else(|| StoreError::Invalid("group event lacks receipt".into()))?;
                let receipt_dec = Receipt::from_bytes(receipt)?;
                let job_id = receipt_dec.body.request.as_ref().and_then(|v| <[u8; 32]>::try_from(v.as_slice()).ok()).map(Id)
                    .ok_or_else(|| StoreError::Invalid("group receipt has no job ID".into()))?;
                let job = meta.get(&("job".into(), job_id)).ok_or_else(|| StoreError::Invalid("group event lacks job".into()))?;
                let revisions = m.revisions.iter().map(|rid| meta.get(&("revision".into(), *rid)).cloned().ok_or_else(|| StoreError::Invalid("group event lacks revision".into()))).collect::<Result<Vec<_>>>()?;
                let cert_values = vec![certs.get(&("cert".into(), *cert)).ok_or_else(|| StoreError::Invalid("group event lacks bound certificate".into()))?.clone()];
                let outcome = antientropy::import(self, &Item::Group { marker: marker_bytes.clone(), revisions, receipt: receipt.clone(), job: job.clone(), certs: cert_values }).await?;
                if let Outcome::Conflict { local, remote, .. } = outcome {
                    let local_marker = self.store.marker_variant(group, &local).await?
                        .ok_or(StoreError::Missing { kind: "local marker", id: local })?;
                    let mut fields = Vec::new();
                    if local_marker.file_path != m.file_path { fields.push("file_path"); }
                    if local_marker.anchor != m.anchor { fields.push("anchor"); }
                    if local_marker.lamport != m.lamport { fields.push("lamport"); }
                    if local_marker.author != m.author { fields.push("author"); }
                    if local_marker.revisions != m.revisions { fields.push("revisions"); }
                    if local_marker.root_path != m.root_path { fields.push("root_path"); }
                    if local_marker.lineage_keys != m.lineage_keys { fields.push("lineage_keys"); }
                    if local_marker.receipt != m.receipt { fields.push("receipt"); }
                    return Ok(Outcome::Rejected(format!("MarkerConflict group={} local={} remote={} differing_fields={}; immutable Workspaces layout/revision content",
                        group.hex(), local.hex(), remote.hex(), fields.join(","))));
                }
                Ok(outcome)
            }
            AeKind::Tombstone { id, cert } => {
                let tombstone = meta.get(&("tombstone".into(), *id)).ok_or_else(|| StoreError::Invalid("tombstone event lacks object".into()))?;
                let cert_values = vec![certs.get(&("tcert".into(), *cert)).ok_or_else(|| StoreError::Invalid("tombstone event lacks bound certificate".into()))?.clone()];
                antientropy::import(self, &Item::Tombstone { tombstone: tombstone.clone(), certs: cert_values }).await
            }
            AeKind::Evidence { kind, object, cert } => {
                let bytes = certs.get(&(kind.clone(), *cert)).ok_or_else(|| StoreError::Invalid("evidence event lacks certificate".into()))?;
                let cfg = self.store.ae_federation().await?.ok_or_else(|| StoreError::Invalid("federation config missing".into()))?;
                let valid = if kind == "cert" {
                    Cert::from_bytes(bytes).ok().is_some_and(|c| c.id() == *cert && c.body.group == *object
                        && cfg.members.values().any(|m| m.replica == c.body.replica && m.writers.get(&c.body.writer).is_some_and(|k| c.verify(k))))
                } else if kind == "tcert" {
                    TombstoneCert::from_bytes(bytes).ok().is_some_and(|c| c.id() == *cert && c.body.tombstone == *object
                        && cfg.members.values().any(|m| m.replica == c.body.replica && m.writers.get(&c.body.writer).is_some_and(|k| c.verify(k))))
                } else if let Some(s3_kind) = kind.strip_prefix("ocert/").and_then(Kind::from_name) {
                    ObjectCert::from_bytes(bytes).ok().is_some_and(|c| c.id() == *cert && c.body.id == *object && c.body.kind == s3_kind
                        && cfg.members.values().any(|m| m.replica == c.body.replica && m.writers.get(&c.body.writer).is_some_and(|k| c.verify(k))))
                } else { false };
                if !valid { return Ok(Outcome::Rejected("evidence signature or object binding invalid".into())); }
                let keys = self.store.meta.keys.clone();
                let (evidence_kind, evidence_object, evidence_cert) = (kind.clone(), *object, *cert);
                let key = keys.xcertv(kind, object, cert);
                let bytes = bytes.clone();
                self.store.meta.run(Txn::Ae, Box::new(move |trx| {
                    let (key, bytes, keys, evidence_kind) = (key.clone(), bytes.clone(), keys.clone(), evidence_kind.clone());
                    Box::pin(async move {
                        if let Some(existing) = get(trx, &key).await? {
                            if existing == bytes { return Ok(Step::Done(false)); }
                            return Err(StoreError::Invalid("foreign certificate identity collision".into()));
                        }
                        trx.set(&key, &bytes);
                        append_event(trx, &keys, &AeKind::Evidence { kind: evidence_kind, object: evidence_object, cert: evidence_cert }, 0);
                        Ok(Step::Commit(true))
                    })
                })).await.map(|fresh| if fresh { Outcome::Applied } else { Outcome::Present })
            }
            AeKind::Catalogue { source: event_origin, id, cert } => {
                let origin = if event_origin.is_empty() { source } else { event_origin.as_str() };
                let cfg = self.store.ae_federation().await?.ok_or_else(|| StoreError::Invalid("federation config missing".into()))?;
                let Some(member) = cfg.members.get(origin) else { return Ok(Outcome::Rejected("catalogue origin is not a federation member".into())); };
                let rec_bytes = meta.get(&("catalogue".into(), *id)).ok_or_else(|| StoreError::Invalid("catalogue event lacks record".into()))?;
                let rec = SignedRecord::from_bytes(rec_bytes)?;
                if rec.id() != *id || rec.body.workspace != rec.body.token.holder
                    || !member.writers.get(&rec.body.workspace).is_some_and(|k| rec.verify(k)) {
                    return Ok(Outcome::Rejected("catalogue record has invalid source writer signature or ID".into()));
                }
                let rc_bytes = certs.get(&("rcert".into(), *cert)).ok_or_else(|| StoreError::Invalid("catalogue event lacks commit certificate".into()))?;
                let rc = CommitCert::from_bytes(rc_bytes)?;
                if rc.id() != *cert || rc.body.catalog != *id || rc.body.token != rec.body.token || rc.body.replica != member.replica
                    || !member.writers.get(&rec.body.token.holder).is_some_and(|k| rc.verify(k)) {
                    return Ok(Outcome::Rejected("catalogue commit certificate lacks source proof".into()));
                }
                let token_values: Vec<_> = meta.iter().filter(|((kind, _), _)| kind == "token").collect();
                if token_values.len() != 1 { return Ok(Outcome::Rejected("catalogue event lacks unique source token".into())); }
                let token_bytes = token_values[0].1;
                let token = TokenEntry::from_pce(token_bytes)?;
                if token.token.body.token != rec.body.token || !token.token.verify(&member.authority) {
                    return Ok(Outcome::Rejected("catalogue source fence token invalid".into()));
                }
                if let Some(parent) = rec.body.predecessor {
                    match self.store.foreign_record(origin, &parent).await? {
                        None => return Ok(Outcome::Deferred(format!("source catalogue predecessor {parent} absent"))),
                        Some(parent_rec) if parent_rec.body.workspace != rec.body.workspace || parent_rec.body.token.rank > rec.body.token.rank =>
                            return Ok(Outcome::Rejected("source catalogue predecessor has different workspace or later fence rank".into())),
                        Some(_) => {}
                    }
                }
                let Some(snapshot_bytes) = self.store.s3.get(Kind::Snapshot, &rec.body.snapshot).await? else {
                    return Ok(Outcome::Deferred("catalogue snapshot absent".into()));
                };
                let snapshot = Snapshot::from_preimage(&snapshot_bytes)?;
                if snapshot.workspace != rec.body.workspace { return Ok(Outcome::Rejected("catalogue snapshot workspace mismatch".into())); }
                let mut required = vec![(Kind::Snapshot, rec.body.snapshot), (Kind::Manifest, snapshot.source_root), (Kind::Manifest, snapshot.build_receipt)];
                let mut revision_rows = Vec::new();
                for rid in &snapshot.contents {
                    let rev_bytes = meta.get(&("catalogue-revision".into(), *rid)).ok_or_else(|| StoreError::Invalid("catalogue event lacks revision".into()))?;
                    let rev = Revision::from_preimage(rev_bytes)?;
                    if rev.id() != *rid { return Ok(Outcome::Rejected("catalogue revision ID mismatch".into())); }
                    required.push((Kind::Group, rev.group));
                    required.push((Kind::Capsule, rev.capsule));
                    revision_rows.push((*rid, rev_bytes.clone()));
                }
                required.sort(); required.dedup();
                let mut ocerts = Vec::new();
                for (kind, object) in required {
                    let Some((_, object_bytes)) = self.store.s3.get_acked(kind, &object).await? else {
                        return Ok(Outcome::Deferred(format!("catalogue {} {object} absent", kind.name())));
                    };
                    if kind == Kind::Group {
                        if let Some(chunks) = unique_chunks(Kind::Group.domain().strip(&object_bytes)?)? {
                            for (chunk, length) in chunks {
                                if self.store.s3.get_acked(Kind::Chunk, &chunk).await?.is_none_or(|(_, bytes)| bytes.len() as u64 != length) {
                                    return Ok(Outcome::Deferred(format!("catalogue group chunk {chunk} absent")));
                                }
                            }
                        }
                    }
                    let label = format!("ocert/{}", kind.name());
                    let Some((_, bytes)) = certs.iter().find(|((k, _), value)| k == &label && ObjectCert::from_bytes(value).ok().is_some_and(|oc| oc.body.id == object)) else {
                        return Ok(Outcome::Deferred(format!("catalogue {} {object} lacks source object certificate", kind.name())));
                    };
                    let oc = ObjectCert::from_bytes(bytes)?;
                    if oc.body.kind != kind || oc.body.id != object || oc.body.replica != member.replica
                        || !member.writers.get(&oc.body.writer).is_some_and(|key| oc.verify(key)) {
                        return Ok(Outcome::Rejected(format!("catalogue {} {object} object certificate invalid", kind.name())));
                    }
                    ocerts.push((kind, object, bytes.clone()));
                }
                let keys = self.store.meta.keys.clone();
                let (origin, record, rcert, token_bytes, record_id, cert_id, token_rank) =
                    (origin.to_owned(), rec_bytes.clone(), rc_bytes.clone(), token_bytes.clone(), *id, *cert, rec.body.token.rank);
                self.store.meta.run(Txn::Ae, Box::new(move |trx| {
                    let (keys, origin, record, rcert, token_bytes, revision_rows, ocerts) =
                        (keys.clone(), origin.clone(), record.clone(), rcert.clone(), token_bytes.clone(), revision_rows.clone(), ocerts.clone());
                    Box::pin(async move {
                        let rk = keys.xcatalog(&origin, &record_id);
                        if let Some(old) = get(trx, &rk).await? {
                            if old != record { return Err(StoreError::Invalid("foreign catalogue record collision".into())); }
                        }
                        let ck = keys.xrcert(&origin, &record_id);
                        let mut changed = false;
                        let mut publication_new = false;
                        if let Some(old) = get(trx, &ck).await? {
                            if old != rcert { return Err(StoreError::Invalid("foreign catalogue certificate collision".into())); }
                        } else {
                            trx.set(&rk, &record);
                            trx.set(&ck, &rcert);
                            changed = true;
                            publication_new = true;
                        }
                        let tk = keys.xtoken(&origin, token_rank);
                        if let Some(old) = get(trx, &tk).await? {
                            if old != token_bytes { return Err(StoreError::Invalid("source token rank collision".into())); }
                        } else { trx.set(&tk, &token_bytes); changed = true; }
                        for (rid, bytes) in revision_rows {
                            let key = keys.xrevision(&origin, &rid);
                            if let Some(old) = get(trx, &key).await? {
                                if old != bytes { return Err(StoreError::Invalid("foreign revision collision".into())); }
                            } else { trx.set(&key, &bytes); changed = true; }
                        }
                        if ocerts.len() > u16::MAX as usize - 2 { return Err(StoreError::Invalid("too many object certificates in catalogue event".into())); }
                        let mut ordinal = 1u16;
                        for (kind, object, bytes) in ocerts {
                            let key = keys.xocert(&origin, kind, &object);
                            if let Some(old) = get(trx, &key).await? {
                                if old != bytes {
                                    let cert = ObjectCert::from_bytes(&bytes)?.id();
                                    let label = format!("ocert/{}", kind.name());
                                    let alternative = keys.xcertv(&label, &object, &cert);
                                    if get(trx, &alternative).await?.is_none() {
                                        trx.set(&alternative, &bytes);
                                        append_event(trx, &keys, &AeKind::Evidence { kind: label, object, cert }, ordinal);
                                        ordinal += 1;
                                        changed = true;
                                    }
                                }
                            } else { trx.set(&key, &bytes); changed = true; }
                        }
                        if publication_new { append_event(trx, &keys, &AeKind::Catalogue { source: origin, id: record_id, cert: cert_id }, 0); }
                        if changed { Ok(Step::Commit(true)) } else { Ok(Step::Done(false)) }
                    })
                })).await.map(|fresh| if fresh { Outcome::Applied } else { Outcome::Present })
            }
        }
    }
}
