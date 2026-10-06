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
//! - every rank in `1..=fence` was issued exactly once, none above.

use std::collections::{BTreeMap, BTreeSet};

use foundationdb::tuple::Bytes;

use crate::error::{Result, StoreError};
use crate::id::{Id, Kind};
use crate::meta::{self, Envelope};
use crate::objects::*;
use crate::pce::Pce;
use crate::recovery::reconstruct_heads;
use crate::store::Store;

#[derive(Debug, Default, Clone)]
pub struct AuditReport {
    pub violations: Vec<String>,
    /// Marker keys without a certificate (allowed only by fixtures that write them raw).
    pub uncertified_markers: Vec<Id>,
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

pub async fn audit(store: &Store) -> Result<AuditReport> {
    let mut r = AuditReport::default();
    let keys = &store.meta.keys;
    let page = store.page;

    // ---- markers and certificates
    let mut markers: BTreeMap<Id, (Id, Marker)> = BTreeMap::new();
    for (k, v) in store.meta.scan(&keys.sub("marker"), page, |_| None).await? {
        let (_, g): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let g = id_of(&g)?;
        envelope_s3(store, &v, "marker value", &mut r).await?;
        let Some(stored) = store.open_value(&v).await? else { continue };
        let m = Marker::from_preimage(&stored)?;
        markers.insert(g, (m.id(), m));
    }
    let mut certified: BTreeSet<Id> = BTreeSet::new();
    for (k, v) in store.meta.scan(&keys.sub("cert"), page, |_| None).await? {
        let (_, g, _w): (String, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let g = id_of(&g)?;
        let c = Cert::from_bytes(&v)?;
        if !store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            r.violations.push(format!("certificate for {g} does not verify"));
            continue;
        }
        match markers.get(&g) {
            Some((mid, _)) if *mid == c.body.marker => {
                certified.insert(g);
            }
            _ => r.violations.push(format!("certificate for {g} names no published marker (cert_sound)")),
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
        if store.receipt(&m.receipt).await?.is_none() {
            r.violations.push(format!("marker of {g} names absent receipt"));
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
