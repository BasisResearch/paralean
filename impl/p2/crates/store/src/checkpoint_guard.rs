//! OPEN-26's catalogue commit predicate. All mutable metadata is read through the
//! same FDB transaction that writes the commit certificate. Published group IDs and
//! revision IDs remain in the registry after a file position is tombstoned.

use std::collections::{BTreeMap, BTreeSet};

use foundationdb::Transaction;

use crate::error::{GuardFailure, Result};
use crate::id::{Id, ReplicaId};
use crate::meta::{range, Envelope, Keys};
use crate::objects::{Cert, Marker, Object, Revision, Snapshot, Tombstone, TombstoneCert};
use crate::receipt::SignedJob;
use crate::sign::KeyRing;

const MAX_REGISTRY_ROWS: usize = 10_000;

async fn rows(trx: &Transaction, sub: foundationdb::tuple::Subspace) -> Result<Vec<(Vec<u8>, Vec<u8>)>> {
    let (begin, end) = sub.range();
    let found = range(trx, begin, end, MAX_REGISTRY_ROWS + 1).await?;
    if found.more() || found.len() > MAX_REGISTRY_ROWS {
        return Err(GuardFailure::CheckpointRegistryUnreadable.into());
    }
    Ok(found.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect())
}

fn inline(v: &[u8]) -> Result<Vec<u8>> {
    // A blob's bytes cannot be read from S3 inside this FDB transaction. Fail closed;
    // a later compact metadata index can lift this explicit limit.
    match Envelope::decode(v)? {
        Envelope::Inline(bytes) => Ok(bytes),
        Envelope::Blob { .. } => Err(GuardFailure::CheckpointRegistryUnreadable.into()),
    }
}

pub(crate) async fn check(trx: &Transaction, k: &Keys, snapshot: &Snapshot, ring: &KeyRing, replica: ReplicaId) -> Result<()> {
    let revisions: BTreeMap<Id, Revision> = rows(trx, k.sub("revision")).await?
        .into_iter().map(|(key, value)| {
            let r = Revision::from_preimage(&inline(&value)?)?;
            if key != k.revision(&r.id()) { return Err(GuardFailure::CheckpointRegistryUnreadable.into()); }
            Ok((r.id(), r))
        }).collect::<Result<_>>()?;

    let mut certified = BTreeSet::new();
    for (key, value) in rows(trx, k.sub("cert")).await? {
        let c = Cert::from_bytes(&value)?;
        if key == k.cert(&c.body.group, &c.body.writer) && c.body.replica == replica &&
            ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            certified.insert((c.body.group, c.body.marker));
        }
    }
    let mut certified_variants = BTreeSet::new();
    for (key, value) in rows(trx, k.sub("vcer")).await? {
        let c = Cert::from_bytes(&value)?;
        if key == k.variant_cert(&c.body.group, &c.body.marker, &c.body.writer) && c.body.replica == replica &&
            ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            certified_variants.insert((c.body.group, c.body.marker));
        }
    }
    let mut markers: BTreeMap<Id, Vec<Marker>> = BTreeMap::new();
    for (key, value) in rows(trx, k.sub("marker")).await? {
        let m = Marker::from_preimage(&inline(&value)?)?;
        if key != k.marker(&m.group) { return Err(GuardFailure::CheckpointRegistryUnreadable.into()); }
        if certified.contains(&(m.group, m.id())) { markers.entry(m.group).or_default().push(m); }
    }
    for (key, value) in rows(trx, k.sub("mvariant")).await? {
        let m = Marker::from_preimage(&inline(&value)?)?;
        if key != k.marker_variant(&m.group, &m.id()) { return Err(GuardFailure::CheckpointRegistryUnreadable.into()); }
        if certified_variants.contains(&(m.group, m.id())) { markers.entry(m.group).or_default().push(m); }
    }
    if markers.values().any(|ms| ms.windows(2).any(|w| w[0].revisions != w[1].revisions)) {
        return Err(GuardFailure::CheckpointRegistryUnreadable.into());
    }
    // Capsule IDs are expected to identify one published declaration group
    // (`declId` is carried in a P1 capsule). If malformed input reuses a
    // capsule across groups, requiring every matching group is conservative.
    let mut capsule_groups: BTreeMap<Id, BTreeSet<Id>> = BTreeMap::new();
    for (group, group_markers) in &markers {
        for rid in &group_markers[0].revisions {
            let r = revisions.get(rid).ok_or(GuardFailure::CheckpointRegistryUnreadable)?;
            if r.group != *group { return Err(GuardFailure::CheckpointRegistryUnreadable.into()); }
            capsule_groups.entry(r.capsule).or_default().insert(*group);
        }
    }

    let mut certified_tombs = BTreeSet::new();
    for (key, value) in rows(trx, k.sub("tcert")).await? {
        let c = TombstoneCert::from_bytes(&value)?;
        if key == k.tcert(&c.body.tombstone, &c.body.writer) && c.body.replica == replica &&
            ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
            certified_tombs.insert(c.body.tombstone);
        }
    }
    let mut tombstones = Vec::new();
    for (key, value) in rows(trx, k.sub("tombstone")).await? {
        let t = Tombstone::from_preimage(&inline(&value)?)?;
        if key != k.tombstone(&t.id()) { return Err(GuardFailure::CheckpointRegistryUnreadable.into()); }
        if certified_tombs.contains(&t.id()) { tombstones.push(t); }
    }

    let selected_ids: BTreeSet<_> = snapshot.contents.iter().copied().collect();
    let mut selected_groups = BTreeSet::new();
    for rid in &snapshot.contents {
        let r = revisions.get(rid).ok_or(GuardFailure::CheckpointRegistryUnreadable)?;
        if !markers.get(&r.group).is_some_and(|ms| ms.iter().any(|m| m.revisions.contains(rid))) {
            return Err(GuardFailure::CheckpointRegistryUnreadable.into());
        }
        selected_groups.insert(r.group);
    }
    let mut selected = BTreeMap::new();
    let mut selected_group_capsules = BTreeMap::new();
    for group in selected_groups {
        let group_markers = &markers[&group];
        let published_members = &group_markers[0].revisions;
        if !cfg!(feature = "mutate-checkpoint-partial-group") &&
            (!published_members.iter().all(|rid| selected_ids.contains(rid)) ||
            selected_ids.iter().any(|rid| revisions.get(rid).is_some_and(|r| r.group == group && !published_members.contains(rid)))) {
            return Err(GuardFailure::CheckpointPartialGroup(group).into());
        }
        let members: Vec<_> = if cfg!(feature = "mutate-checkpoint-partial-group") {
            published_members.iter().filter(|rid| selected_ids.contains(rid)).copied().collect()
        } else { published_members.clone() };
        for rid in &members {
            let r = &revisions[rid];
            if selected_group_capsules.insert(group, r.capsule).is_some_and(|old| old != r.capsule) {
                return Err(GuardFailure::CheckpointRegistryUnreadable.into());
            }
            if selected.insert(r.name.clone(), group).is_some() &&
                !cfg!(feature = "mutate-checkpoint-no-buildable") {
                return Err(GuardFailure::CheckpointDuplicateName(r.name.clone()).into());
            }
        }
    }

    // T1/T9 persist the controller's signed job evidence for each published
    // package. Its `deps` are the exact capsule closure checked at staging.
    // Resolve them against the full atomic groups selected above.
    let mut jobs: BTreeMap<Id, SignedJob> = BTreeMap::new();
    for (key, value) in rows(trx, k.sub("jobproof")).await? {
        let job = SignedJob::from_bytes(&value)?;
        let group = job.body.group;
        let Some(group_markers) = markers.get(&group) else { continue; };
        if !job.issued_by(ring) { continue; }
        let (_, raw_group, raw_marker, _):
            (String, foundationdb::tuple::Bytes, foundationdb::tuple::Bytes, foundationdb::tuple::Bytes) =
            k.root.unpack(&key).map_err(|_| GuardFailure::CheckpointRegistryUnreadable)?;
        if raw_group[..] != group.0[..] || !group_markers.iter().any(|m| raw_marker[..] == m.id().0[..]) {
            continue;
        }
        if let Some(old) = jobs.insert(group, job.clone()) {
            if old.body.deps != job.body.deps || old.body.capsule != job.body.capsule {
                return Err(GuardFailure::CheckpointRegistryUnreadable.into());
            }
        }
    }
    if !cfg!(feature = "mutate-checkpoint-no-deps") {
        for (&group, &capsule) in &selected_group_capsules {
            let job = jobs.get(&group).ok_or(GuardFailure::CheckpointRegistryUnreadable)?;
            if job.body.capsule != capsule { return Err(GuardFailure::CheckpointRegistryUnreadable.into()); }
            for dep in &job.body.deps {
                if !capsule_groups.get(dep).is_some_and(|groups|
                    groups.iter().all(|g| selected_group_capsules.contains_key(g))) {
                    return Err(GuardFailure::CheckpointDependencyMissing { group, capsule: *dep }.into());
                }
            }
        }
    }

    // A revision may supersede its parent directly or through a chain. A group is
    // superseded as a whole even if the revision changes only one of its names.
    let published: BTreeSet<_> = markers.keys().copied().collect();
    let mut superseded = BTreeSet::new();
    for r in revisions.values() {
        if !published.contains(&r.group) || !markers[&r.group].iter().any(|m| m.revisions.contains(&r.id())) { continue; }
        let mut pending = r.parents.clone();
        let mut seen = BTreeSet::new();
        while let Some(parent) = pending.pop() {
            if !seen.insert(parent) { continue; }
            let ancestor = revisions.get(&parent).ok_or(GuardFailure::CheckpointRegistryUnreadable)?;
            superseded.insert(ancestor.group);
            pending.extend(ancestor.parents.iter().copied());
        }
    }
    let live: BTreeSet<_> = markers.iter().filter_map(|(g, ms)| {
        if superseded.contains(g) { return None; }
        let has_position = ms.iter().any(|m| !tombstones.iter().any(|t|
            t.target == *g && t.file_path == m.file_path &&
            t.position.is_none_or(|p| p == m.id())));
        has_position.then_some(*g)
    }).collect();

    if !cfg!(feature = "mutate-checkpoint-no-current") {
        for (name, group) in selected {
            let heads: BTreeSet<_> = revisions.values().filter(|r| r.name == name && live.contains(&r.group) &&
                    markers[&r.group].iter().any(|m| m.revisions.contains(&r.id())))
                .map(|r| r.group).collect();
            // A deleted file position does not erase a registry group or a
            // historical snapshot. It only stops competing as a live head.
            // An otherwise unopposed deleted group remains a valid selection.
            if heads != BTreeSet::from([group]) && !(heads.is_empty() && !superseded.contains(&group)) {
                return Err(GuardFailure::CheckpointNotCurrent { group, name }.into());
            }
        }
    }
    Ok(())
}
