//! Recovery after losing every local ID: discovery of published groups from certificates,
//! causal head reconstruction per name, and catalogue recovery selected by certificates.
//!
//! Discovery (§8.3, AckCertificates): a paginated range scan of `cert/`; a group is
//! discovered iff some valid certificate names it and its marker. Raw markers are never
//! read as evidence (a `marker/` key without a certificate is ignored).
//!
//! Tombstones (§11.4) are discovered the same way: a paginated scan of `tcert/`; a
//! tombstone counts iff a valid tombstone certificate names it and its stored bytes. A
//! `tombstone/` key without a certificate is ignored.
//!
//! Rendering (§11.3/§11.4, Workspaces `render`): a file shows the *live* discovered groups
//! of that file: not tombstoned by a discovered tombstone and not superseded, i.e. no
//! discovered group has one of its revisions as an ancestor (for any name). Order is the
//! model's `PosLt` over carried data only: the root paths carried in the markers
//! (`rootPath`, RGA order: a proper prefix first, otherwise the larger `(lamport, author)` at
//! the first difference first), then the group's own key, oldest first.
//!
//! Catalogue recovery (§9, CatalogCertificates `ScanEnumerate`): a paginated range scan of
//! `catalog/`, then per-record point reads. A record is *ready* iff its commit certificate
//! (`rcert`), its snapshot's object certificate and every payload's object certificate are
//! present and verify; readiness never asks whether surviving bytes were once
//! acknowledged. A record is *admissible* iff it decodes, is ready, belongs to the
//! workspace, is buildable (its build receipt says so) and its predecessor is admissible.
//! Heads are the admissible records that are no admissible record's predecessor; automatic
//! selection needs a unique head.

use std::collections::{BTreeMap, BTreeSet};

use foundationdb::tuple::Bytes;

use crate::error::{Result, StoreError};
use crate::id::{Id, Kind, WorkspaceId};
use crate::objects::*;
use crate::store::Store;

#[derive(Clone, Debug)]
pub struct Published {
    pub marker_id: Id,
    pub marker: Marker,
    pub certifiers: Vec<WorkspaceId>,
}

#[derive(Clone, Debug)]
pub struct PublishedTombstone {
    pub tombstone: Tombstone,
    pub certifiers: Vec<WorkspaceId>,
}

#[derive(Clone, Debug, Default)]
pub struct Discovery {
    pub groups: BTreeMap<Id, Published>,
    /// Tombstones with a valid tombstone certificate, by tombstone ID.
    pub tombstones: BTreeMap<Id, PublishedTombstone>,
    /// Tombstone keys with no valid certificate: ignored.
    pub ignored_tombstones: Vec<Id>,
    /// Groups with a revision that is an ancestor of a discovered revision (any name).
    pub superseded: BTreeSet<Id>,
    /// The rendered sequence of live groups of every file.
    pub files: BTreeMap<String, Vec<Id>>,
    /// Marker keys with no valid certificate: ignored, reported for diagnosis only.
    pub ignored_markers: Vec<Id>,
    /// Certificates whose marker key is missing or names another marker.
    pub dangling_certs: usize,
    pub revisions: BTreeMap<Id, Revision>,
    /// Causal heads per name over the discovered revisions.
    pub heads: BTreeMap<Name, Vec<Id>>,
    /// Names with more than one head (an eventual error in the registry, §7).
    pub conflicts: Vec<Name>,
}

/// Heads of each name: known revisions not superseded by a known descendant of that name.
pub fn reconstruct_heads(revs: &BTreeMap<Id, Revision>) -> BTreeMap<Name, Vec<Id>> {
    let mut superseded: BTreeSet<Id> = BTreeSet::new();
    for r in revs.values() {
        for p in &r.parents {
            if revs.get(p).is_some_and(|pr| pr.name == r.name) {
                superseded.insert(*p);
            }
        }
    }
    // Ancestry is transitive: a revision below a superseded one is superseded too, which
    // the parent edges already give because every known revision's parents are admitted.
    let mut heads: BTreeMap<Name, Vec<Id>> = BTreeMap::new();
    for (id, r) in revs {
        if !superseded.contains(id) {
            heads.entry(r.name.clone()).or_default().push(*id);
        }
    }
    heads
}

pub async fn discover(store: &Store) -> Result<Discovery> {
    discover_with(store, |_| None).await
}

/// Discovery with a hook between scan pages (tests run concurrent publications there).
pub async fn discover_with(
    store: &Store,
    between: impl FnMut(usize) -> Option<futures::future::BoxFuture<'static, ()>>,
) -> Result<Discovery> {
    let keys = &store.meta.keys;
    let certs = store.meta.scan(&keys.sub("cert"), store.page, between).await?;
    // group -> (marker id -> certifiers)
    let mut by_group: BTreeMap<Id, BTreeMap<Id, Vec<WorkspaceId>>> = BTreeMap::new();
    for (k, v) in certs {
        let (_, g, w): (String, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let Ok(c) = Cert::from_bytes(&v) else { continue };
        if c.body.group.0[..] != g[..] || c.body.writer.0[..] != w[..] {
            continue;
        }
        if !store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            continue;
        }
        by_group.entry(c.body.group).or_default().entry(c.body.marker).or_default().push(c.body.writer);
    }
    let mut d = Discovery::default();
    for (g, markers) in by_group {
        match store.marker(&g).await? {
            Some((mid, m)) if markers.contains_key(&mid) => {
                d.groups.insert(g, Published { marker_id: mid, marker: m, certifiers: markers[&mid].clone() });
            }
            _ => d.dangling_certs += 1,
        }
    }
    // Diagnostics: marker keys without certificates.
    let markers = store.meta.scan(&keys.sub("marker"), store.page, |_| None).await?;
    for (k, _) in markers {
        let (_, g): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let g = Id(g[..].try_into().map_err(|_| StoreError::Invalid("group id".into()))?);
        if !d.groups.contains_key(&g) {
            d.ignored_markers.push(g);
        }
    }
    for p in d.groups.values() {
        for rid in &p.marker.revisions {
            if let Some(r) = store.revision(rid).await? {
                d.revisions.insert(*rid, r);
            }
        }
    }
    d.heads = reconstruct_heads(&d.revisions);
    d.conflicts = d.heads.iter().filter(|(_, h)| h.len() > 1).map(|(n, _)| n.clone()).collect();
    discover_tombstones(store, &mut d).await?;
    d.superseded = superseded_groups(store, &d.revisions).await?;
    let paths: BTreeSet<String> = d.groups.values().map(|p| p.marker.file_path.clone()).collect();
    for path in paths {
        let seq = render(&d, &path);
        d.files.insert(path, seq);
    }
    Ok(d)
}

/// Tombstones by certificates (`tcert/` scan), as markers are discovered by `cert/`.
async fn discover_tombstones(store: &Store, d: &mut Discovery) -> Result<()> {
    let keys = &store.meta.keys;
    let mut by_t: BTreeMap<Id, Vec<TombstoneCert>> = BTreeMap::new();
    if cfg!(feature = "mutate-tombstone-raw-scan") {
        // Mutation: read raw tombstone keys as evidence.
        for (k, _) in store.meta.scan(&keys.sub("tombstone"), store.page, |_| None).await? {
            let (_, t): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
            by_t.entry(Id(t[..].try_into().map_err(|_| StoreError::Invalid("tombstone id".into()))?)).or_default();
        }
    }
    for (k, v) in store.meta.scan(&keys.sub("tcert"), store.page, |_| None).await? {
        let (_, t, w): (String, Bytes, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let Ok(c) = TombstoneCert::from_bytes(&v) else { continue };
        if c.body.tombstone.0[..] != t[..] || c.body.writer.0[..] != w[..] || !store.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            continue;
        }
        by_t.entry(c.body.tombstone).or_default().push(c);
    }
    for (tid, certs) in by_t {
        let Some(t) = store.tombstone(&tid).await? else { continue };
        let certifiers: Vec<WorkspaceId> = certs.iter().filter(|c| c.body.target == t.target).map(|c| c.body.writer).collect();
        if certifiers.is_empty() && !cfg!(feature = "mutate-tombstone-raw-scan") {
            continue;
        }
        d.tombstones.insert(tid, PublishedTombstone { tombstone: t, certifiers });
    }
    for (k, _) in store.meta.scan(&keys.sub("tombstone"), store.page, |_| None).await? {
        let (_, t): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let t = Id(t[..].try_into().map_err(|_| StoreError::Invalid("tombstone id".into()))?);
        if !d.tombstones.contains_key(&t) {
            d.ignored_tombstones.push(t);
        }
    }
    Ok(())
}

/// Groups superseded by a discovered revision: the groups of all its transitive revision
/// ancestors. Ancestors are read from the store's revision objects, which T1 (and the
/// anti-entropy receive) only write after their parents (admitted ancestor closure), so the
/// walk never depends on which groups are discovered.
pub async fn superseded_groups(store: &Store, revs: &BTreeMap<Id, Revision>) -> Result<BTreeSet<Id>> {
    let mut out = BTreeSet::new();
    let mut seen: BTreeSet<Id> = BTreeSet::new();
    let mut todo: Vec<Id> = revs.values().flat_map(|r| r.parents.iter().copied()).collect();
    while let Some(p) = todo.pop() {
        if !seen.insert(p) {
            continue;
        }
        let r = match revs.get(&p) {
            Some(r) => r.clone(),
            None => match store.revision(&p).await? {
                Some(r) => r,
                None => continue,
            },
        };
        out.insert(r.group);
        todo.extend(r.parents.iter().copied());
    }
    Ok(out)
}

type Key = (u64, [u8; 16]);

fn key_of(m: &Marker) -> Key {
    (m.lamport, m.author.0)
}

/// The carried root path (file start first). A marker without one is its own root.
fn root_path_of(m: &Marker) -> Vec<Key> {
    if m.root_path.is_empty() {
        vec![key_of(m)]
    } else {
        m.root_path.iter().map(|(_, l, a)| (*l, a.0)).collect()
    }
}

/// Workspaces `PathLt`: a proper prefix first; at the first difference the larger key first.
pub fn path_lt(p: &[Key], q: &[Key]) -> bool {
    match (p.split_first(), q.split_first()) {
        (None, None) => false,
        (None, Some(_)) => true,
        (Some(_), None) => false,
        (Some((x, p)), Some((y, q))) => if x == y { path_lt(p, q) } else { y < x },
    }
}

/// Workspaces `PosLt` as an ordering.
pub fn pos_cmp(a: &Marker, b: &Marker) -> std::cmp::Ordering {
    let (pa, pb) = (root_path_of(a), root_path_of(b));
    if pa == pb {
        key_of(a).cmp(&key_of(b))
    } else if path_lt(&pa, &pb) {
        std::cmp::Ordering::Less
    } else {
        std::cmp::Ordering::Greater
    }
}

/// Is a discovered group live (rendered)? Known, not tombstoned, not superseded.
pub fn live(d: &Discovery, g: &Id) -> bool {
    let Some(p) = d.groups.get(g) else { return false };
    let tombstoned = d.tombstones.values().any(|t| t.tombstone.target == *g && t.tombstone.file_path == p.marker.file_path);
    (!tombstoned || cfg!(feature = "mutate-render-ignores-tombstones"))
        && (!d.superseded.contains(g) || cfg!(feature = "mutate-render-ignores-supersession"))
}

/// The rendered sequence of `path`: its live groups in `PosLt` order.
pub fn render(d: &Discovery, path: &str) -> Vec<Id> {
    let mut gs: Vec<&Published> = d.groups.iter().filter(|(g, p)| p.marker.file_path == path && live(d, g)).map(|(_, p)| p).collect();
    gs.sort_by(|a, b| pos_cmp(&a.marker, &b.marker));
    gs.iter().map(|p| p.marker.group).collect()
}

#[derive(Clone, Debug)]
pub struct RecordStatus {
    pub record: CatalogRecord,
    pub ready: bool,
    pub buildable: bool,
    pub admissible: bool,
    /// Why the record is not ready / not admissible.
    pub reasons: Vec<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Recovery {
    pub records: BTreeMap<Id, RecordStatus>,
    /// Records whose bytes did not decode or verify.
    pub undecodable: usize,
    pub heads: Vec<Id>,
    /// Automatic selection: the unique head, if there is one.
    pub selected: Option<Id>,
    pub conflict: bool,
}

impl Recovery {
    pub fn admissible(&self) -> Vec<Id> {
        self.records.iter().filter(|(_, s)| s.admissible).map(|(c, _)| *c).collect()
    }
}

async fn readiness(store: &Store, c: &Id, rec: &CatalogRecord) -> Result<(bool, bool, Vec<String>)> {
    let mut why = Vec::new();
    // Token: issued by the authority to this holder.
    match store.token(rec.token.rank).await? {
        Some(e) if e.token.body.token == rec.token && store.ring.verify_authority(&e.token.id(), &e.token.sig) => {}
        _ => why.push(format!("token rank {} not issued to the holder", rec.token.rank)),
    }
    if store.valid_rcert(c, rec).await?.is_none() {
        why.push("no commit certificate".into());
    }
    if store.valid_ocert(Kind::Snapshot, &rec.snapshot).await?.is_none() {
        why.push("no snapshot certificate".into());
    }
    let mut buildable = false;
    match store.s3.get_object::<Snapshot>(Kind::Snapshot, &rec.snapshot).await {
        Ok(Some(snap)) => {
            if snap.workspace != rec.workspace {
                why.push("snapshot names another workspace".into());
            }
            for rid in &snap.contents {
                match store.revision(rid).await? {
                    None => why.push(format!("revision {rid:?} absent")),
                    Some(r) => {
                        for (k, id) in [(Kind::Group, r.group), (Kind::Capsule, r.capsule)] {
                            if store.valid_ocert(k, &id).await?.is_none() {
                                why.push(format!("no {} certificate for {id:?}", k.name()));
                            }
                        }
                    }
                }
            }
            for (what, id) in [("sourceRoot", snap.source_root), ("buildReceipt", snap.build_receipt)] {
                if store.valid_ocert(Kind::Manifest, &id).await?.is_none() {
                    why.push(format!("no {what} certificate"));
                }
            }
            match store.s3.get_object::<Manifest>(Kind::Manifest, &snap.build_receipt).await {
                Ok(Some(Manifest::BuildReceipt { verdict: BuildVerdict::Ok, .. })) => buildable = true,
                Ok(_) => why.push("build receipt missing or not ok".into()),
                Err(e) => why.push(format!("build receipt undecodable: {e}")),
            }
        }
        Ok(None) => why.push("snapshot bytes missing or corrupt".into()),
        Err(e) => why.push(format!("snapshot undecodable: {e}")),
    }
    let ready = !why.iter().any(|w| !w.starts_with("build receipt"));
    Ok((ready, buildable, why))
}

/// Enumerate catalogue records and select by certificates, for `workspace`.
pub async fn recover_catalog(store: &Store, workspace: WorkspaceId) -> Result<Recovery> {
    let keys = &store.meta.keys;
    let kvs = store.meta.scan(&keys.sub("catalog"), store.page, |_| None).await?;
    let mut out = Recovery::default();
    for (k, v) in kvs {
        let (_, cb): (String, Bytes) = keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
        let Ok(rec) = SignedRecord::from_bytes(&v) else {
            out.undecodable += 1;
            continue;
        };
        let c = rec.id();
        if c.0[..] != cb[..] || !store.ring.verify_writer(&rec.body.token.holder, &c, &rec.sig) {
            out.undecodable += 1;
            continue;
        }
        let (ready, buildable, mut reasons) = readiness(store, &c, &rec.body).await?;
        if rec.body.workspace != workspace {
            reasons.push("another workspace".into());
        }
        out.records.insert(c, RecordStatus { record: rec.body, ready, buildable, admissible: false, reasons });
    }
    // Admissibility: the record and every ancestor (predecessor chain).
    let ids: Vec<Id> = out.records.keys().copied().collect();
    for c in &ids {
        let mut cur = Some(*c);
        let mut ok = true;
        let mut seen = BTreeSet::new();
        while let Some(x) = cur {
            if !seen.insert(x) {
                ok = false; // a cycle cannot arise from content addressing; reject anyway
                break;
            }
            match out.records.get(&x) {
                Some(s) if s.ready && s.buildable && s.record.workspace == workspace => cur = s.record.predecessor,
                _ => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok && out.records[c].ready {
            out.records.get_mut(c).unwrap().reasons.push("an ancestor is not admissible".into());
        }
        out.records.get_mut(c).unwrap().admissible = ok;
    }
    let adm: BTreeSet<Id> = out.admissible().into_iter().collect();
    let preds: BTreeSet<Id> = adm.iter().filter_map(|c| out.records[c].record.predecessor).collect();
    out.heads = adm.iter().filter(|c| !preds.contains(c)).copied().collect();
    out.conflict = out.heads.len() > 1;
    out.selected = (out.heads.len() == 1).then(|| out.heads[0]);
    Ok(out)
}
