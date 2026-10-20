//! Whole-store invariant audit, run by the tests after every injected fault.
//!
//! Checked (store.md and HARDENED.md `hardened_safe`):
//! - published ⇒ certified: every `marker/<g>` has a valid certificate naming its marker
//!   (`published_certified`); and every certificate names a published group (`cert_sound`);
//! - no metadata key names an object absent from (or corrupt in) S3 (store.md P2
//!   obligation): markers' staged copies, groups, capsules, blobs, snapshots, manifests and
//!   every object with an object certificate;
//! - target records: the head is a published revision of that name, every published
//!   revision of the name is the head or an ancestor of it, so there is at most one head
//!   (`recorded_head_tops_chain`, `target_head_unique`);
//! - commit certificates are fenced: the certificate's token is the record's, that rank was
//!   issued to that holder and is at most the fence (`record_cert_fenced`);
//! - no orphan commits: a committed record's predecessor is committed and its snapshot is
//!   certified (`record_cert_parents_ready`);
//! - every rank in `1..=fence` was issued exactly once, none above;
//! - every published group's receipt passes the P3 staging rule against the envelope stored
//!   with it (`job/<id>`); groups whose validator key was revoked since are listed as suspect.
//! - tombstones (§11.4) as markers: a stored tombstone is certified, its staged S3 copy
//!   exists, and every tombstone certificate names a stored tombstone; a tombstone deletes a
//!   published, certified group of the same file, by its author, with a larger Lamport time;
//! - anti-entropy evidence (`xcert/`): another deployment's certificate, kept apart, that
//!   verifies and names an object stored here.

use std::collections::{BTreeMap, BTreeSet};

use foundationdb::tuple::Bytes;

use crate::error::{Result, StoreError};
use crate::id::{AgentId, Id, Kind, WorkspaceId};
use crate::authority::{AgentKeyGrant, AgentKeyRevocation, ControllerDeleteGrant};
use crate::group_chunks::unique_chunks;
use crate::meta::{self, Envelope};
use crate::objects::*;
use crate::pce::{Dec, Pce};
use crate::recovery::reconstruct_heads;
use crate::store::Store;

#[derive(Debug, Default, Clone)]
pub struct AuditReport {
    pub violations: Vec<String>,
    /// Marker keys without a certificate (allowed only by fixtures that write them raw).
    pub uncertified_markers: Vec<Id>,
    /// Published groups whose receipt's validator key has since been revoked.
    pub suspect_receipts: Vec<Id>,
    /// Tombstone keys without a certificate (likewise).
    pub uncertified_tombstones: Vec<Id>,
    pub counts: BTreeMap<&'static str, usize>,
}

impl AuditReport {
    pub fn ok(&self) -> bool {
        self.violations.is_empty()
    }
    pub fn assert_ok(&self) {
        assert!(self.violations.is_empty(), "audit violations:\n{}", self.violations.join("\n"));
    }
}

fn id_of(b: &Bytes) -> Result<Id> {
    Ok(Id(b[..].try_into().map_err(|_| StoreError::Invalid("bad id in key".into()))?))
}

async fn s3_present(store: &Store, kind: Kind, id: &Id, what: &str, r: &mut AuditReport) -> Result<()> {
    if store.s3.get(kind, id).await?.is_none() {
        r.violations.push(format!("{what} names {} {id} absent or corrupt in S3", kind.name()));
    }
    Ok(())
}

async fn envelope_s3(store: &Store, v: &[u8], what: &str, r: &mut AuditReport) -> Result<()> {
    if let Envelope::Blob { blob, .. } = Envelope::decode(v)? {
        s3_present(store, Kind::Blob, &blob, what, r).await?;
    }
    Ok(())
}

async fn registered_key(store: &Store, agent: AgentId, writer: WorkspaceId, public: [u8; 32], replica: crate::id::ReplicaId) -> Result<bool> {
    if store.ring.ambiguous_writer_origins.contains(&writer) { return Ok(false); }
    let expected_issuer = if let Some(cfg) = store.ae_federation().await? {
        cfg.members.values().find(|member| member.replica == replica && member.writers.contains_key(&writer))
            .map(|member| member.authority)
    } else { store.ring.writer_origins.get(&writer).copied() };
    let Some(expected_issuer) = expected_issuer else { return Ok(false) };
    let Some(bytes) = store.meta.get(store.meta.keys.agent_key(&agent, &public)).await? else { return Ok(false) };
    let Ok(grant) = serde_json::from_slice::<AgentKeyGrant>(&bytes) else { return Ok(false) };
    Ok(grant.parts().is_some_and(|(a, w, k, issuer)| a == agent && w == writer && k == public &&
        issuer == expected_issuer && grant.verify()))
}

pub async fn audit(store: &Store) -> Result<AuditReport> {
    let mut r = AuditReport::default();
    let keys = &store.meta.keys;
    let page = store.page;

    // The controller's signed registry and immutable revocations are audit records.
    for (key, value) in store.meta.scan(&keys.sub("agent"), page, |_| None).await? {
        let (_, raw_agent, raw_public): (String, Bytes, Bytes) = keys.root.unpack(&key).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let grant: AgentKeyGrant = serde_json::from_slice(&value).map_err(|e| StoreError::Invalid(format!("bad agent grant: {e}")))?;
        if !grant.parts().is_some_and(|(agent, _, public, issuer)| agent.0[..] == raw_agent[..] && public[..] == raw_public[..]
            && (issuer == store.ring.authority || store.ring.agent_authorities.contains(&issuer)) && grant.verify()) {
            r.violations.push("agent registry contains invalid controller grant".into());
        }
    }
    for (key, value) in store.meta.scan(&keys.sub("arevoke"), page, |_| None).await? {
        let (_, raw_public): (String, Bytes) = keys.root.unpack(&key).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let revocation: AgentKeyRevocation = serde_json::from_slice(&value).map_err(|e| StoreError::Invalid(format!("bad agent revocation: {e}")))?;
        if !revocation.public().is_some_and(|public| public[..] == raw_public[..]) || !revocation.verify(&store.ring.authority) {
            r.violations.push("agent revocation lacks local controller signature".into());
        }
    }

    // ---- markers and certificates
    let mut all_markers: BTreeMap<Id, BTreeMap<Id, Marker>> = BTreeMap::new();
    for (k, v) in store.meta.scan(&keys.sub("marker"), page, |_| None).await? {
        let (_, g): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let g = id_of(&g)?;
        envelope_s3(store, &v, "marker value", &mut r).await?;
        let Some(stored) = store.open_value(&v).await? else { continue };
        let m = Marker::from_preimage(&stored)?;
        if m.group != g { r.violations.push(format!("marker key {g} holds another group")); }
        all_markers.entry(g).or_default().insert(m.id(), m);
    }
    for (k, v) in store.meta.scan(&keys.sub("mvariant"), page, |_| None).await? {
        let (_, g, marker): (String, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let (g, marker) = (id_of(&g)?, id_of(&marker)?);
        envelope_s3(store, &v, "marker variant value", &mut r).await?;
        let Some(stored) = store.open_value(&v).await? else { continue };
        let m = Marker::from_preimage(&stored)?;
        if m.id() != marker || m.group != g { r.violations.push(format!("marker variant {g}/{marker} key mismatch")); }
        all_markers.entry(g).or_default().insert(marker, m);
    }
    let mut certified: BTreeSet<Id> = BTreeSet::new();
    let mut certified_markers: BTreeSet<(Id, Id)> = BTreeSet::new();
    for (k, v) in store.meta.scan(&keys.sub("cert"), page, |_| None).await? {
        let (_, g, _w): (String, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let g = id_of(&g)?;
        let c = Cert::from_bytes(&v)?;
        if !store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            r.violations.push(format!("certificate for {g} does not verify"));
            continue;
        }
        match all_markers.get(&g).and_then(|variants| variants.get(&c.body.marker)) {
            Some(_) if c.body.group == g => {
                certified.insert(g);
                certified_markers.insert((g, c.body.marker));
            }
            _ => r.violations.push(format!("certificate for {g} names no published marker (cert_sound)")),
        }
    }
    for (k, v) in store.meta.scan(&keys.sub("vcer"), page, |_| None).await? {
        let (_, g, marker, w): (String, Bytes, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let (g, marker) = (id_of(&g)?, id_of(&marker)?);
        let c = Cert::from_bytes(&v)?;
        if c.body.group != g || c.body.marker != marker || c.body.writer.0[..] != w[..]
            || !store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig)
            || !all_markers.get(&g).is_some_and(|variants| variants.contains_key(&marker)) {
            r.violations.push(format!("variant certificate for {g}/{marker} invalid or names no marker"));
        } else { certified.insert(g); certified_markers.insert((g, marker)); }
    }
    let mut markers: BTreeMap<Id, (Id, Marker)> = BTreeMap::new();
    for g in all_markers.keys() {
        if let Some(selected) = store.marker(g).await? { markers.insert(*g, selected); }
    }
    for (g, variants) in &all_markers {
        let mut baseline: Option<&Marker> = None;
        for (mid, marker) in variants {
            if marker.id() != *mid || marker.group != *g {
                r.violations.push(format!("marker variant {g}/{mid} ID or group mismatch"));
            }
            if certified_markers.contains(&(*g, *mid)) {
                s3_present(store, Kind::StagedMarker, mid, "marker variant", &mut r).await?;
            }
            if let Some(base) = baseline {
                if base.group != marker.group || base.revisions != marker.revisions
                    || base.lineage_keys != marker.lineage_keys || base.author != marker.author {
                    r.violations.push(format!("marker variants of {g} disagree on lineage"));
                }
            } else { baseline = Some(marker); }
        }
    }
    *r.counts.entry("markers").or_default() = markers.len();
    *r.counts.entry("certified groups").or_default() = certified.len();
    let mut revisions: BTreeMap<Id, Revision> = BTreeMap::new();
    for (g, (mid, m)) in &markers {
        if !certified.contains(g) {
            r.uncertified_markers.push(*g);
            continue;
        }
        s3_present(store, Kind::StagedMarker, mid, "marker", &mut r).await?;
        s3_present(store, Kind::Group, g, "marker", &mut r).await?;
        let mut author_certificates = store.certs(g).await?.into_iter().filter(|c| c.body.marker == *mid).collect::<Vec<_>>();
        for (_, bytes) in store.meta.scan(&keys.xcertvs_of("cert", g), page, |_| None).await? {
            if let Ok(cert) = Cert::from_bytes(&bytes) {
                if cert.body.marker == *mid && store.ring.verify_writer(&cert.body.writer, &cert.id(), &cert.sig) {
                    author_certificates.push(cert);
                }
            }
        }
        let mut registered_author = false;
        for cert in author_certificates {
            if let Some(public) = store.ring.signing_writer_key(&cert.body.writer, &cert.id(), &cert.sig) {
                if registered_key(store, m.author, cert.body.writer, public, cert.body.replica).await? { registered_author = true; break; }
            }
        }
        if !registered_author { r.violations.push(format!("marker {mid} has no certificate from a registered author key")); }
        match store.receipt(&m.receipt).await? {
            None => r.violations.push(format!("marker of {g} names absent receipt")),
            Some(rc) => {
                let job = match rc.body.request.as_ref().and_then(|q| <[u8; 32]>::try_from(&q[..]).ok()) {
                    Some(jid) => store.meta.get(keys.job(&Id(jid))).await?,
                    None => None,
                };
                match job.map(|v| crate::receipt::SignedJob::from_bytes(&v)).transpose()? {
                    None => r.violations.push(format!("receipt of {g} names no stored job envelope")),
                    Some(job) => {
                        // Epochs were fenced by T1; here the receipt is checked against the
                        // envelope's own target set.
                        let prepared = crate::receipt::prepared_of(&job);
                        let mut receipt_ring = (*store.ring).clone();
                        if let Some(cfg) = store.ae_federation().await? {
                            let mut home: Option<String> = None;
                            for rid in &m.revisions {
                                if let Some(rev) = store.revision(rid).await? {
                                    if let Some(h) = cfg.target_homes.get(&rev.name) {
                                        if home.as_ref().is_some_and(|x| x != h) {
                                            r.violations.push(format!("marker of {g} mixes target homes"));
                                        }
                                        home = Some(h.clone());
                                    }
                                }
                            }
                            if let Some(home) = home {
                                receipt_ring.authority = cfg.members[&home].authority;
                                receipt_ring.job_issuers.clear();
                            }
                        }
                        if let Err(e) = crate::receipt::check(&rc, &job, g, &prepared, &receipt_ring) {
                            r.violations.push(format!("receipt of {g} fails the staging rule: {e}"));
                        }
                    }
                }
                if store.meta.get(keys.revocation(&rc.body.validator_key)).await?.is_some() {
                    r.suspect_receipts.push(*g);
                }
            }
        }
        for rid in &m.revisions {
            let Some(rv) = store.meta.get(keys.revision(rid)).await? else {
                r.violations.push(format!("marker of {g} names absent revision {rid}"));
                continue;
            };
            envelope_s3(store, &rv, "revision value", &mut r).await?;
            let Some(rev) = store.revision(rid).await? else { continue };
            s3_present(store, Kind::Capsule, &rev.capsule, "revision", &mut r).await?;
            revisions.insert(*rid, rev);
        }
    }

    // ---- tombstones
    let mut tcerted: BTreeMap<Id, Vec<TombstoneCert>> = BTreeMap::new();
    for (k, v) in store.meta.scan(&keys.sub("tcert"), page, |_| None).await? {
        let (_, t, _w): (String, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let t = id_of(&t)?;
        let c = TombstoneCert::from_bytes(&v)?;
        if c.body.tombstone != t || !store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            r.violations.push(format!("tombstone certificate for {t} does not verify"));
            continue;
        }
        tcerted.entry(t).or_default().push(c);
    }
    let tombstone_federation = store.ae_federation().await?;
    let mut ntomb = 0;
    for (k, v) in store.meta.scan(&keys.sub("tombstone"), page, |_| None).await? {
        ntomb += 1;
        let (_, t): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let tid = id_of(&t)?;
        envelope_s3(store, &v, "tombstone value", &mut r).await?;
        let Some(stored) = store.open_value(&v).await? else { continue };
        let tb = Tombstone::from_preimage(&stored)?;
        if tb.id() != tid {
            r.violations.push(format!("tombstone key {tid} holds another tombstone"));
            continue;
        }
        let Some(cs) = tcerted.remove(&tid) else {
            r.uncertified_tombstones.push(tid);
            continue;
        };
        if cs.iter().any(|c| c.body.target != tb.target) {
            r.violations.push(format!("a certificate of tombstone {tid} names another target"));
        }
        s3_present(store, Kind::StagedTombstone, &tid, "tombstone", &mut r).await?;
        let target_position = if let Some(position) = tb.position { Some(position) }
            else { store.marker_base(&tb.target).await?.map(|(id, _)| id) };
        let target_marker = target_position.and_then(|position| all_markers.get(&tb.target)?.get(&position).map(|m| (position, m)));
        match target_marker {
            Some((position, m)) if certified_markers.contains(&(tb.target, position)) => {
                if m.file_path != tb.file_path || m.lamport >= tb.lamport {
                    r.violations.push(format!("tombstone {tid} is not a valid deletion of {}", tb.target));
                }
                let controller_grant = store.meta.get(keys.delete_grant(&tid)).await?
                    .map(|bytes| serde_json::from_slice::<ControllerDeleteGrant>(&bytes)
                        .map_err(|e| StoreError::Invalid(format!("bad controller deletion grant: {e}")))).transpose()?;
                if let Some(grant) = controller_grant {
                    let issuer: Option<[u8; 32]> = hex::decode(&grant.issuer).ok().and_then(|v| v.try_into().ok());
                    let valid = issuer.is_some_and(|issuer| {
                        (issuer == store.ring.authority || store.ring.agent_authorities.contains(&issuer)) &&
                        grant.verify(&tid, &issuer) && tb.author == crate::authority::controller_agent_id(&issuer)
                    });
                    if !valid { r.violations.push(format!("controller grant of tombstone {tid} is invalid")); }
                    if let Some(issuer) = issuer {
                        let mut source_certs = cs.clone();
                        for (_, value) in store.meta.scan(&keys.xcertvs_of("tcert", &tid), page, |_| None).await? {
                            if let Ok(cert) = TombstoneCert::from_bytes(&value) { source_certs.push(cert); }
                        }
                        let mut source_bound = false;
                        let mut foreign_source = false;
                        for cert in source_certs {
                            if cert.body.tombstone != tid || cert.body.target != tb.target { continue; }
                            let Some(public) = store.ring.signing_writer_key(&cert.body.writer, &cert.id(), &cert.sig) else { continue };
                            let origin_matches = !store.ring.ambiguous_writer_origins.contains(&cert.body.writer) &&
                                tombstone_federation.as_ref().map_or_else(
                                    || store.ring.writer_origins.get(&cert.body.writer).copied() == Some(issuer),
                                    |cfg| cfg.members.values().any(|member| member.replica == cert.body.replica &&
                                        member.authority == issuer && member.verify_writer(&store.ring, &cert.body.writer, &cert.id(), &cert.sig)));
                            if store.ring.agent_keys.iter().any(|entry| entry.parts().is_some_and(|(_, writer, key, controller)|
                                writer == cert.body.writer && key == public && controller == issuer && entry.verify())) && origin_matches {
                                source_bound = true;
                                foreign_source |= cert.body.replica != store.replica;
                            }
                        }
                        if !source_bound { r.violations.push(format!("controller deletion {tid} has no certificate from its issuing deployment")); }
                        // A received grant is checked against its source certificate, not
                        // against this replica's independent fence, even if controllers share
                        // the same signing key.
                        if issuer == store.ring.authority && !foreign_source {
                            let current = store.meta.fence().await?;
                            if grant.fence > current || (grant.fence > 0 && store.meta.get(keys.token(grant.fence)).await?.is_none()) {
                                r.violations.push(format!("controller deletion {tid} has no issued fence rank"));
                            }
                        }
                    }
                } else if m.author != tb.author {
                    r.violations.push(format!("tombstone {tid} has neither author nor controller authority"));
                } else {
                    let mut source_certs = cs.clone();
                    for (_, value) in store.meta.scan(&keys.xcertvs_of("tcert", &tid), page, |_| None).await? {
                        if let Ok(cert) = TombstoneCert::from_bytes(&value) { source_certs.push(cert); }
                    }
                    let mut author_bound = false;
                    for cert in source_certs {
                        if let Some(public) = store.ring.signing_writer_key(&cert.body.writer, &cert.id(), &cert.sig) {
                            if registered_key(store, tb.author, cert.body.writer, public, cert.body.replica).await? { author_bound = true; break; }
                        }
                    }
                    if !author_bound { r.violations.push(format!("tombstone {tid} has no registered author certificate")); }
                }
            }
            _ => r.violations.push(format!("tombstone {tid} deletes {}, not a certified position", tb.target)),
        }
        if let Some(rc) = tb.receipt {
            if store.receipt(&rc).await?.is_none() {
                r.violations.push(format!("tombstone {tid} names absent receipt {rc}"));
            }
        }
    }
    for t in tcerted.keys() {
        r.violations.push(format!("tombstone certificate names no stored tombstone {t} (cert_sound)"));
    }
    *r.counts.entry("tombstones").or_default() = ntomb;

    // ---- anti-entropy evidence
    let mut nx = 0;
    for (k, v) in store.meta.scan(&keys.sub("xcert"), page, |_| None).await? {
        nx += 1;
        let (_, kind, o, _rep, _w): (String, String, Bytes, Bytes, Bytes) =
            keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let o = id_of(&o)?;
        let ok = match kind.as_str() {
            "cert" => Cert::from_bytes(&v).ok().is_some_and(|c| {
                c.body.group == o
                    && store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig)
                    && all_markers.get(&o).is_some_and(|variants| variants.contains_key(&c.body.marker))
            }),
            "tcert" => TombstoneCert::from_bytes(&v).ok().is_some_and(|c| {
                c.body.tombstone == o && store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig)
            }) && store.meta.get(keys.tombstone(&o)).await?.is_some(),
            _ => false,
        };
        if !ok {
            r.violations.push(format!("anti-entropy evidence {kind}/{o} does not verify or names nothing stored"));
        }
    }
    let federation = store.ae_federation().await?;
    for (k, v) in store.meta.scan(&keys.sub("xcertv"), page, |_| None).await? {
        nx += 1;
        let (_, kind, object, cert_id): (String, String, Bytes, Bytes) =
            keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let (object, cert_id) = (id_of(&object)?, id_of(&cert_id)?);
        let allowed = |replica, writer, cert: &Id, sig: &[u8]| {
            store.ring.verify_writer(&writer, cert, sig)
                && federation.as_ref().is_none_or(|cfg| cfg.members.values().any(|member|
                    member.replica == replica && member.verify_writer(&store.ring, &writer, cert, sig)))
        };
        let valid = if kind == "cert" {
            Cert::from_bytes(&v).ok().is_some_and(|c| c.id() == cert_id && c.body.group == object
                && allowed(c.body.replica, c.body.writer, &c.id(), &c.sig)
                && all_markers.get(&object).is_some_and(|variants| variants.contains_key(&c.body.marker)))
        } else if kind == "tcert" {
            TombstoneCert::from_bytes(&v).ok().is_some_and(|c| c.id() == cert_id && c.body.tombstone == object
                && allowed(c.body.replica, c.body.writer, &c.id(), &c.sig))
                && store.meta.get(keys.tombstone(&object)).await?.is_some()
        } else if let Some(s3_kind) = kind.strip_prefix("ocert/").and_then(Kind::from_name) {
            ObjectCert::from_bytes(&v).ok().is_some_and(|c| c.id() == cert_id && c.body.kind == s3_kind && c.body.id == object
                && allowed(c.body.replica, c.body.writer, &c.id(), &c.sig))
        } else { false };
        if !valid { r.violations.push(format!("anti-entropy evidence {kind}/{object}/{cert_id} invalid or source-unbound")); }
        if valid {
            if let Some(s3_kind) = kind.strip_prefix("ocert/").and_then(Kind::from_name) {
                s3_present(store, s3_kind, &object, "foreign object certificate", &mut r).await?;
            }
        }
    }
    *r.counts.entry("received evidence").or_default() = nx;

    for (k, v) in store.meta.scan(&keys.sub("gchunks"), page, |_| None).await? {
        let (_, raw): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let group = id_of(&raw)?;
        let mut dec = Dec::new(&v);
        let rows = dec.list(|d| Ok((Id::decode(d)?, d.uvarint()?)))?;
        if dec.remaining() != 0 { r.violations.push(format!("group {group} chunk index has trailing bytes")); }
        let Some(group_bytes) = store.s3.get(Kind::Group, &group).await? else {
            r.violations.push(format!("group {group} chunk index names absent group"));
            continue;
        };
        let derived = unique_chunks(Kind::Group.domain().strip(&group_bytes)?)?;
        if derived.as_ref().is_none_or(|chunks| chunks.iter().map(|(id, len)| (*id, *len)).collect::<Vec<_>>() != rows) {
            r.violations.push(format!("group {group} chunk index differs from authenticated manifest"));
        }
        for (chunk, length) in rows {
            if store.s3.get(Kind::Chunk, &chunk).await?.is_none_or(|bytes| bytes.len() as u64 != length) {
                r.violations.push(format!("group {group} chunk {chunk} absent, corrupt or wrong length"));
            }
        }
    }
    let mut nforeign = 0;
    for (k, _) in store.meta.scan(&keys.sub("xcatalog"), page, |_| None).await? {
        nforeign += 1;
        let (_, source, raw): (String, String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let id = id_of(&raw)?;
        match store.foreign_record(&source, &id).await {
            Ok(Some(record)) => {
                let token = store.meta.get(keys.xtoken(&source, record.body.token.rank)).await?;
                let valid_token = token.and_then(|bytes| TokenEntry::from_pce(&bytes).ok()).is_some_and(|entry|
                    federation.as_ref().is_some_and(|cfg| cfg.members.get(&source).is_some_and(|member|
                        entry.token.body.token == record.body.token && entry.token.verify(&member.authority))));
                if !valid_token { r.violations.push(format!("foreign catalogue {source}/{id} lacks source token proof")); }
            }
            Ok(None) => r.violations.push(format!("foreign catalogue {source}/{id} lacks commit proof")),
            Err(e) => r.violations.push(format!("foreign catalogue {source}/{id} invalid: {e}")),
        }
    }
    *r.counts.entry("foreign catalogues").or_default() = nforeign;

    // ---- targets
    let heads = reconstruct_heads(&revisions);
    let mut ntargets = 0;
    for (_, v) in store.meta.scan(&keys.sub("target"), page, |_| None).await? {
        ntargets += 1;
        let t = TargetRecord::from_pce(&v)?;
        let published_of_name: Vec<&Id> = revisions.iter().filter(|(_, rv)| rv.name == t.name).map(|(i, _)| i).collect();
        match t.head {
            None => {
                if !published_of_name.is_empty() {
                    r.violations.push(format!("target {} has published proofs but no head", t.name));
                }
            }
            Some(h) => {
                if !revisions.get(&h).is_some_and(|rv| rv.name == t.name) {
                    r.violations.push(format!("target {} head {h} is not a published revision of it", t.name));
                }
                let hs = heads.get(&t.name).cloned().unwrap_or_default();
                if hs != vec![h] {
                    r.violations.push(format!("target {} has heads {hs:?}, record says {h:?}", t.name));
                }
            }
        }
    }
    *r.counts.entry("targets").or_default() = ntargets;

    // ---- fence and tokens
    let fence = store.fence().await?;
    let mut ranks = BTreeSet::new();
    for (k, v) in store.meta.scan(&keys.sub("token"), page, |_| None).await? {
        let (_, rank): (String, u64) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let e = TokenEntry::from_pce(&v)?;
        if e.token.body.token.rank != rank || !store.ring.verify_authority(&e.token.id(), &e.token.sig) {
            r.violations.push(format!("token {rank} malformed or unsigned"));
        }
        ranks.insert(rank);
    }
    if ranks != (1..=fence).collect::<BTreeSet<u64>>() {
        r.violations.push(format!("issued ranks {ranks:?} differ from 1..={fence}"));
    }

    // ---- object certificates
    let mut nocerts = 0;
    for (k, _) in store.meta.scan(&keys.sub("ocert"), page, |_| None).await? {
        nocerts += 1;
        let (_, kind, id): (String, String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let kind = Kind::from_name(&kind).ok_or_else(|| StoreError::Invalid("ocert kind".into()))?;
        let id = id_of(&id)?;
        if store.valid_ocert(kind, &id).await?.is_none() {
            r.violations.push(format!("object certificate {}/{id} does not verify", kind.name()));
        }
        s3_present(store, kind, &id, "object certificate", &mut r).await?;
    }
    *r.counts.entry("object certs").or_default() = nocerts;

    // ---- catalogue
    let mut records: BTreeMap<Id, SignedRecord> = BTreeMap::new();
    for (_, v) in store.meta.scan(&keys.sub("catalog"), page, |_| None).await? {
        let rec = SignedRecord::from_bytes(&v)?;
        s3_present(store, Kind::Snapshot, &rec.body.snapshot, "catalogue record", &mut r).await?;
        records.insert(rec.id(), rec);
    }
    let mut committed = 0;
    for (k, v) in store.meta.scan(&keys.sub("rcert"), page, |_| None).await? {
        committed += 1;
        let (_, c): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let c = id_of(&c)?;
        let rc = CommitCert::from_bytes(&v)?;
        let Some(rec) = records.get(&c) else {
            r.violations.push(format!("commit certificate for absent record {c}"));
            continue;
        };
        if rc.body.token != rec.body.token || rc.body.catalog != c {
            r.violations.push(format!("commit certificate of {c} carries another token"));
        }
        match store.token(rec.body.token.rank).await? {
            Some(e) if e.token.body.token == rec.body.token && rec.body.token.rank <= fence => {}
            _ => r.violations.push(format!("committed record {c} was not fenced (rank {})", rec.body.token.rank)),
        }
        if store.valid_ocert(Kind::Snapshot, &rec.body.snapshot).await?.is_none() {
            r.violations.push(format!("committed record {c} has no snapshot certificate"));
        }
        if let Some(p) = rec.body.predecessor {
            let pc = store.meta.get(keys.rcert(&p)).await?.is_some();
            let ps = match records.get(&p) {
                Some(pr) => store.valid_ocert(Kind::Snapshot, &pr.body.snapshot).await?.is_some(),
                None => false,
            };
            if !(pc && ps) {
                r.violations.push(format!("orphan commit: {c} committed over uncommitted parent {p}"));
            }
        }
    }
    *r.counts.entry("records").or_default() = records.len();
    *r.counts.entry("committed records").or_default() = committed;
    let _ = meta::INLINE_LIMIT;
    Ok(r)
}
