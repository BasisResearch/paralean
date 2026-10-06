//! Tombstones (§11.4) against the real services: a typed store kind, published by T8 with
//! its certificate in the same transaction (as markers by T1), discovered by certificates
//! only, and honoured by rendering after recovery. Workspaces models a tombstone as a
//! revision of its target that is never rendered (`tombstone_not_rendered`,
//! `superseded_not_rendered`, `delete_frees_name`); the fixtures below are its
//! counterparts, plus the certificate rules of AckCertificates applied to tombstones.

mod common;

use common::*;
use paralean_store::recovery::{discover, recover_catalog};
use paralean_store::*;

const F: &str = "Test/Del.lean";

/// Publish a fresh group in `F` after `anchor`.
async fn insert(e: &Env, wi: usize, tag: &str, anchor: Option<&Marker>, lamport: u64) -> Package {
    let mut p = fixture::package(tag, e.w[wi].id, &e.validator, &Name::parse(&format!("Del.{tag}")), vec![], None, lamport);
    fixture::place(&mut p, F, anchor, None);
    e.w[wi].publish(&p).await.unwrap();
    p
}

fn g(p: &Package) -> Id {
    p.group.id()
}

// ---------------------------------------------------------------------------------------
/// Workspaces `tombstone_not_rendered`, `superseded_not_rendered`, `revision_in_place`; §11.4
/// "a tombstone never removes the group from the registry, from snapshots, or as a
/// dependency". After losing every local handle, discovery and rendering reproduce the file
/// without the deleted and the superseded declaration, and catalogue recovery still adopts
/// a checkpoint holding the deleted one.
#[tokio::test]
async fn fixture_tombstoned_and_superseded_leave_the_rendered_file() {
    let cfg = StoreConfig::from_env(&common::deployment("tomb-render")).unwrap();
    let e = Env::open(cfg.clone(), 2, Faults::none());
    let a = insert(&e, 0, "a", None, 1).await;
    let b = insert(&e, 0, "b", Some(&a.marker), 2).await;
    let c = insert(&e, 1, "c", Some(&b.marker), 3).await;
    // A concurrent insertion at the file start by another author: larger key, renders first.
    let z = insert(&e, 1, "z", None, 4).await;
    let d0 = discover(&e.store).await.unwrap();
    assert_eq!(d0.files[F], vec![g(&z), g(&a), g(&b), g(&c)]);

    // The author deletes b.
    let t = fixture::tombstone_of(&b.marker, 5);
    assert!(e.w[0].tombstone(&t).await.unwrap());
    // a is revised by a' (a revision takes its lineage root's place).
    let mut a2 = fixture::package("a2", e.w[0].id, &e.validator, &Name::parse("Del.a"), vec![rev_id(&a)], None, 6);
    fixture::place(&mut a2, F, None, Some(&a.marker));
    e.w[0].publish(&a2).await.unwrap();
    // A checkpoint holding the deleted group still commits: tombstones are not registry facts.
    let tok = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let rec = e.w[0].commit_checkpoint(&fixture::checkpoint(e.w[0].id, vec![rev_id(&b)], None, tok, "with-b")).await.unwrap();

    // Recovery: every handle and local ID is gone; reopen from configuration and keys.
    drop(e);
    let r = Env::open(cfg, 2, Faults::none());
    let d = discover(&r.store).await.unwrap();
    assert_eq!(d.tombstones.len(), 1);
    assert_eq!(d.tombstones[&t.id()].certifiers, vec![r.w[0].id]);
    assert!(d.superseded.contains(&g(&a)));
    assert_eq!(d.files[F], vec![g(&z), g(&a2), g(&c)], "b deleted, a replaced by a' in a's place");
    // The registry is unchanged by the tombstone: b's revision is still the head of its name.
    assert_eq!(d.heads[&Name::parse("Del.b")], vec![rev_id(&b)]);
    assert_eq!(d.heads[&Name::parse("Del.a")], vec![rev_id(&a2)]);
    let rc = recover_catalog(&r.store, r.w[0].id).await.unwrap();
    assert_eq!(rc.selected, Some(rec), "{:?}", rc.records);
    let audit = r.audit_ok().await;
    assert!(audit.uncertified_tombstones.is_empty());
    assert_eq!(audit.counts["tombstones"], 1);
}

// ---------------------------------------------------------------------------------------
/// AckCertificates `guard_necessity` for tombstones: a staged tombstone and a raw tombstone
/// key with exactly the bytes T8 writes, but no certificate, are ignored by discovery; the
/// target stays rendered. Only the certified T8 deletes it.
#[tokio::test]
async fn fixture_uncertified_tombstone_is_ignored() {
    let e = Env::new("tomb-raw", 1);
    let a = insert(&e, 0, "a", None, 1).await;
    let b = insert(&e, 0, "b", Some(&a.marker), 2).await;
    let t = fixture::tombstone_of(&b.marker, 3);
    let tid = t.id();
    e.store.s3.put(Kind::StagedTombstone, &t.preimage()).await.unwrap();
    let v = e.store.stage_value(tid, t.preimage()).await.unwrap();
    e.store.meta.raw_set(e.store.meta.keys.tombstone(&tid), v).await.unwrap();
    let d = discover(&e.store).await.unwrap();
    assert!(d.tombstones.is_empty());
    assert_eq!(d.ignored_tombstones, vec![tid]);
    assert_eq!(d.files[F], vec![g(&a), g(&b)], "an uncertified tombstone deletes nothing");
    let ra = audit::audit(&e.store).await.unwrap();
    assert_eq!(ra.uncertified_tombstones, vec![tid]);
    assert!(ra.ok(), "{:?}", ra.violations);
    // The raw key is not this writer's publication: T8 refuses to certify it.
    assert_eq!(guard_of(e.w[0].tombstone(&t).await), GuardFailure::TombstoneExists { tombstone: tid });
    // A real deletion (a later tombstone) goes through T8 and is discovered.
    let t2 = fixture::tombstone_of(&b.marker, 4);
    e.w[0].tombstone(&t2).await.unwrap();
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.files[F], vec![g(&a)]);
}

// ---------------------------------------------------------------------------------------
/// T8's guards: the target is published *and certified* here (a raw marker is not
/// evidence), in the tombstone's file, older, by the deleting author (OPEN-19 default), not
/// a target-name group, and a named receipt exists. A failed T8 writes nothing.
#[tokio::test]
async fn t8_tombstone_guards() {
    let e = Env::new("tomb-guards", 2);
    let a = insert(&e, 0, "a", None, 5).await;
    let keys0 = key_count(&e).await;
    // Not newer than the target.
    assert_eq!(guard_of(e.w[0].tombstone(&fixture::tombstone_of(&a.marker, 5)).await), GuardFailure::TombstoneNotNewer { lamport: 5, target: 5 });
    // Another file.
    let mut t = fixture::tombstone_of(&a.marker, 6);
    t.file_path = "Other.lean".into();
    assert!(matches!(guard_of(e.w[0].tombstone(&t).await), GuardFailure::TombstoneFileMismatch { .. }));
    // Another author (writer 1, its own agent ID) and a writer claiming the author's agent ID.
    let mut t = fixture::tombstone_of(&a.marker, 6);
    t.author = AgentId::derive("someone else");
    assert_eq!(guard_of(e.w[0].tombstone(&t).await), GuardFailure::TombstoneNotAuthor);
    assert_eq!(guard_of(e.w[1].tombstone(&fixture::tombstone_of(&a.marker, 6)).await), GuardFailure::TombstoneNotAuthor);
    // An absent receipt.
    let mut t = fixture::tombstone_of(&a.marker, 6);
    t.receipt = Some(Id([7; 32]));
    assert_eq!(guard_of(e.w[0].tombstone(&t).await), GuardFailure::TombstoneReceiptAbsent(Id([7; 32])));
    // A group with only a raw marker key (never published): uncertified, refused.
    let p = e.plain_package(0, "Del.raw", "raw");
    let mv = e.store.stage_value(p.marker.id(), p.marker.preimage()).await.unwrap();
    for r in &p.revisions {
        let rv = e.store.stage_value(r.id(), r.preimage()).await.unwrap();
        e.store.meta.raw_set(e.store.meta.keys.revision(&r.id()), rv).await.unwrap();
    }
    e.store.meta.raw_set(e.store.meta.keys.marker(&g(&p)), mv).await.unwrap();
    assert_eq!(guard_of(e.w[0].tombstone(&fixture::tombstone_of(&p.marker, 9)).await), GuardFailure::Uncertified(g(&p)));
    assert_eq!(key_count(&e).await, keys0 + 2, "only the raw fixture keys were added");
    assert!(discover(&e.store).await.unwrap().tombstones.is_empty());
    // A target-name group: TargetNames has no deletion.
    let x = Name::parse("Target.x");
    e.ctl.reassign(&x, e.w[0].id, b"assign").await.unwrap();
    let (tp, _) = e.publish_target(0, &x, "tx").await.unwrap();
    assert_eq!(guard_of(e.w[0].tombstone(&fixture::tombstone_of(&tp.marker, 9)).await), GuardFailure::TombstoneOfTarget(x));
    // The valid deletion, then an idempotent repeat.
    let t = fixture::tombstone_of(&a.marker, 6);
    assert!(e.w[0].tombstone(&t).await.unwrap());
    assert!(!e.w[0].tombstone(&t).await.unwrap(), "repeat finds the effect");
    let ra = audit::audit(&e.store).await.unwrap();
    assert!(ra.ok(), "{:?}", ra.violations);
    assert_eq!(ra.uncertified_markers, vec![g(&p)]);
}

/// Count every FDB key of the deployment.
async fn key_count(e: &Env) -> usize {
    e.store.meta.scan(&e.store.meta.keys.root, 10_000, |_| None).await.unwrap().len()
}

// ---------------------------------------------------------------------------------------
/// Faults: unknown commit results of T8 (landed or not) are resolved by the idempotent
/// retry; a crash between the staged S3 copy and T8 leaves nothing discoverable; a crash
/// right after T8 leaves the tombstone certified (`published_certified` for tombstones: no
/// window without a certificate, TLA `target_stranded_head` analogue).
#[tokio::test]
async fn tombstone_faults_resolve() {
    let faults = Faults::none();
    let e = Env::with_faults("tomb-faults", 1, faults.clone());
    let mut prev: Option<Marker> = None;
    let mut ps = Vec::new();
    for i in 0..4 {
        let p = insert(&e, 0, &format!("f{i}"), prev.as_ref(), 1 + i as u64).await;
        prev = Some(p.marker.clone());
        ps.push(p);
    }
    for (i, f) in [CommitFault::UnknownCommitted, CommitFault::UnknownNotCommitted].into_iter().enumerate() {
        faults.on_commit(Some(Txn::T8Tombstone), 0, f);
        e.w[0].tombstone(&fixture::tombstone_of(&ps[i].marker, 10)).await.unwrap();
    }
    assert_eq!(faults.stats().get("unknown-result-resolved").copied(), Some(2));
    // Crash after the staged copy, before T8: nothing to discover; the retry deletes.
    faults.crash_at("tombstone:after-staged", 0);
    let t2 = fixture::tombstone_of(&ps[2].marker, 10);
    assert!(e.w[0].tombstone(&t2).await.unwrap_err().is_crash());
    assert!(e.store.s3.get(Kind::StagedTombstone, &t2.id()).await.unwrap().is_some());
    let d = discover(&e.store).await.unwrap();
    assert!(d.files[F].contains(&g(&ps[2])) && d.ignored_tombstones.is_empty());
    e.w[0].tombstone(&t2).await.unwrap();
    // Crash right after T8: the tombstone is already certified.
    faults.crash_at("tombstone:before-cert", 0);
    assert!(e.w[0].tombstone(&fixture::tombstone_of(&ps[3].marker, 10)).await.unwrap_err().is_crash());
    let ra = audit::audit(&e.store).await.unwrap();
    assert!(ra.uncertified_tombstones.is_empty(), "a published tombstone is certified");
    ra.assert_ok();
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.tombstones.len(), 4);
    assert!(d.files.get(F).is_none_or(|f| f.is_empty()), "{:?}", d.files);
}

// ---------------------------------------------------------------------------------------
/// A concurrent revision and tombstone of one group (Workspaces: both supersede it): the
/// revision renders in the group's place, the tombstone deletes only its target, and the
/// tombstoned author's name passes to the next candidate (`delete_frees_name`, registry-free
/// part: rendering).
#[tokio::test]
async fn fixture_concurrent_revision_and_tombstone() {
    let e = Env::new("tomb-conc", 2);
    let a = insert(&e, 0, "a", None, 1).await;
    let b = insert(&e, 1, "b", Some(&a.marker), 2).await;
    let mut b2 = fixture::package("b2", e.w[1].id, &e.validator, &Name::parse("Del.b"), vec![rev_id(&b)], None, 3);
    fixture::place(&mut b2, F, None, Some(&b.marker));
    e.w[1].publish(&b2).await.unwrap();
    e.w[1].tombstone(&fixture::tombstone_of(&b.marker, 4)).await.unwrap();
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.files[F], vec![g(&a), g(&b2)]);
    // Deleting the revision empties b's lineage; a stays.
    e.w[1].tombstone(&fixture::tombstone_of(&b2.marker, 5)).await.unwrap();
    assert_eq!(discover(&e.store).await.unwrap().files[F], vec![g(&a)]);
    e.audit_ok().await;
}
