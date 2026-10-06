//! Regression fixtures from docs/plan.md P2 and store.md "P2 obligations", run against the
//! real FoundationDB and Garage services. Each converts a model counterexample or witness
//! into a concrete store execution.

mod common;

use common::*;
use paralean_store::recovery::{discover, recover_catalog};
use paralean_store::*;

fn x() -> Name {
    Name::parse("Target.x")
}

/// Count every FDB key of the deployment (to show an operation had no metadata effect).
async fn key_count(e: &Env) -> usize {
    e.store.meta.scan(&e.store.meta.keys.root, 10_000, |_| None).await.unwrap().len()
}

// ---------------------------------------------------------------------------------------
/// CatalogFencing `stale_writer_rejected`, TLA `fencing_unfenced_commit`: a writer whose
/// token was superseded cannot commit; recovery selects the new holder's record.
#[tokio::test]
async fn fixture_stale_writer_after_rotation() {
    let e = Env::new("fx-stale", 2);
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let base = e.w[0].commit_checkpoint(&one_snapshot(&e, 0, "base", t1, None).await).await.unwrap();
    // A prepares its next checkpoint under rank 1; the controller hands the fence to B.
    let cp_a = one_snapshot(&e, 0, "a", t1, Some(base)).await;
    let t2 = e.ctl.rotate(e.w[1].id, b"r2").await.unwrap();
    let g = guard_of(e.w[0].commit_checkpoint(&cp_a).await);
    assert_eq!(g, GuardFailure::StaleToken { rank: 1, fence: 2 });
    // B, the new holder, commits.
    let cp_b = one_snapshot(&e, 1, "b", t2, None).await;
    let b = e.w[1].commit_checkpoint(&cp_b).await.unwrap();
    let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
    // B's record has workspace = B's ID (records carry the writer), so recover for B.
    let rb = recover_catalog(&e.store, e.w[1].id).await.unwrap();
    assert!(rb.records[&b].ready, "{:?}", rb.records[&b].reasons);
    assert_eq!(r.selected, Some(base), "A's own chain stops at its last committed record");
    assert!(r.records.values().filter(|s| s.record.workspace == e.w[0].id).all(|s| s.record.token.rank == 1));
    assert_eq!(r.records.values().filter(|s| s.record.workspace == e.w[0].id).count(), 1, "A's stale record was never written");
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// CatalogFencing `late_ack_and_repair_execution`, CatalogCertificates
/// `stale_stays_uncertified`: a put of the record before the rotation, acknowledged after
/// it. The record's staging T5 commits, its reply is lost, the fence rotates, and the
/// retry finds the bytes (an unconditional acknowledgement). The commit T5 is then retried
/// and aborts on the fence: the record exists without a commit certificate and is never
/// adopted.
#[tokio::test]
async fn fixture_put_before_rotation_acked_after() {
    let faults = Faults::none();
    let e = Env::with_faults("fx-lateack", 2, faults.clone());
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let base = e.w[0].commit_checkpoint(&one_snapshot(&e, 0, "base", t1, None).await).await.unwrap();
    let cp = one_snapshot(&e, 0, "late", t1, Some(base)).await;
    let snap = prepare_snapshot(&e, 0, &cp).await;
    let rec = e.w[0].sign_record(snap, Some(base), t1);
    faults.on_commit(
        Some(Txn::T5Stage),
        0,
        CommitFault::UnknownThen { committed: true, hook: rotate_hook(&e.ctl, e.w[1].id, "r2") },
    );
    // The staging write resolves its unknown outcome after the rotation: bytes present.
    assert!(!e.w[0].stage_record(&rec).await.unwrap(), "retry found the effect: no second write");
    assert_eq!(e.store.fence().await.unwrap(), 2);
    assert!(e.store.record(&rec.id()).await.unwrap().is_some());
    // The commit aborts on the new fence (in its body, before any commit is attempted).
    assert_eq!(guard_of(e.w[0].commit_record(&rec).await), GuardFailure::StaleToken { rank: 1, fence: 2 });
    let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
    let st = &r.records[&rec.id()];
    assert!(!st.ready && !st.admissible);
    assert!(st.reasons.iter().any(|w| w == "no commit certificate"), "{:?}", st.reasons);
    assert_eq!(r.selected, Some(base));
    assert!(faults.stats().get("unknown-result-resolved").copied().unwrap_or(0) >= 1);
    e.audit_ok().await;

    // store.md's narrative with the single T5 of the table: an unknown-outcome T5 that
    // committed before the rotation leaves the record *and* its commit certificate; the
    // retry finds the certificate and succeeds, and the record is adopted (correctly: it was
    // fenced at its commit version). Only a T5 that did not commit is retried into an abort.
    let cp2 = one_snapshot(&e, 1, "c2", e.ctl.rotate(e.w[1].id, b"r2").await.unwrap(), None).await;
    let t3 = e.store.token(2).await.unwrap().unwrap().token.body.token;
    let snap2 = prepare_snapshot(&e, 1, &cp2).await;
    let rec2 = e.w[1].sign_record(snap2, None, t3);
    faults.on_commit(
        Some(Txn::T5Commit),
        0,
        CommitFault::UnknownThen { committed: true, hook: rotate_hook(&e.ctl, e.w[0].id, "r3") },
    );
    assert!(!e.w[1].commit_record(&rec2).await.unwrap(), "retry found the commit certificate");
    assert!(recover_catalog(&e.store, e.w[1].id).await.unwrap().records[&rec2.id()].admissible);
    let t4 = e.ctl.rotate(e.w[1].id, b"r3b").await.unwrap();
    let snap3 = prepare_snapshot(&e, 1, &one_snapshot(&e, 1, "c3", t4, None).await).await;
    let rec3 = e.w[1].sign_record(snap3, None, t4);
    faults.on_commit(
        Some(Txn::T5Commit),
        0,
        CommitFault::UnknownThen { committed: false, hook: rotate_hook(&e.ctl, e.w[0].id, "r4") },
    );
    assert!(matches!(guard_of(e.w[1].commit_record(&rec3).await), GuardFailure::StaleToken { .. }));
    assert!(e.store.record(&rec3.id()).await.unwrap().is_none());
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// store.md "Unfenced repair": a re-PUT of an S3 object after a rotation is allowed and
/// has no catalogue effect; readiness returns once the bytes are back.
#[tokio::test]
async fn fixture_repair_copy_after_rotation() {
    let e = Env::new("fx-repair", 2);
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let cp = one_snapshot(&e, 0, "rep", t1, None).await;
    let c = e.w[0].commit_checkpoint(&cp).await.unwrap();
    let snap = e.store.record(&c).await.unwrap().unwrap().body.snapshot;
    // A second deployment holds a copy of the snapshot bytes (a surviving replica).
    let mut cfg = e.cfg.clone();
    cfg.deployment = common::deployment("fx-repair-src");
    cfg.s3.prefix = format!("{}/", cfg.deployment);
    let src = Env::open(cfg, 1, Faults::none());
    src.store.s3.put_object(Kind::Snapshot, &cp.snapshot).await.unwrap();
    // The local copy is corrupted at rest; the record stops being ready.
    e.store.s3.corrupt_at_rest(Kind::Snapshot, &snap, b"rotten").await.unwrap();
    let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
    assert_eq!(r.selected, None);
    // Rotation, then the repair copy: unfenced, verified bytes, no metadata change.
    e.ctl.rotate(e.w[1].id, b"r2").await.unwrap();
    let before = key_count(&e).await;
    e.w[1].repair_object(&src.store, Kind::Snapshot, &snap).await.unwrap();
    assert_eq!(key_count(&e).await, before, "a repair copy has no catalogue effect");
    let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
    assert_eq!(r.selected, Some(c));
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// AckCertificates `guard_necessity`, TLA `cert_scan_raw_marker`: a staged marker can have
/// exactly the bytes of a published one. Discovery reads certificates only.
#[tokio::test]
async fn fixture_staged_marker_byte_identical_to_published() {
    // Deployment A: the publication fails at T1 (reassignment), leaving the staged copy.
    let a = Env::new("fx-staged-a", 2);
    a.ctl.reassign(&x(), a.w[0].id, b"assign").await.unwrap();
    let p = a.prepare(0, &x(), "same", 1).await.unwrap();
    a.ctl.reassign(&x(), a.w[1].id, b"handover").await.unwrap();
    assert!(matches!(guard_of(a.w[0].publish(&p).await), GuardFailure::NotOwner { .. }));
    // Deployment B: the same package publishes.
    let mut cfg = a.cfg.clone();
    cfg.deployment = common::deployment("fx-staged-b");
    cfg.s3.prefix = format!("{}/", cfg.deployment);
    let b = Env::open(cfg, 2, Faults::none());
    b.ctl.reassign(&x(), b.w[0].id, b"assign").await.unwrap();
    b.w[0].publish(&p).await.unwrap();
    let g = p.group.id();
    let mid = p.marker.id();
    let staged = a.store.s3.get(Kind::StagedMarker, &mid).await.unwrap().unwrap();
    let published_value = b.store.meta.get(b.store.meta.keys.marker(&g)).await.unwrap().unwrap();
    let published = b.store.open_value(&published_value).await.unwrap().unwrap();
    assert_eq!(staged, published, "staged and published markers are byte-identical");
    // Even a raw marker key with those bytes in A (no certificate) is ignored.
    a.store.meta.raw_set(a.store.meta.keys.marker(&g), published_value.clone()).await.unwrap();
    let da = discover(&a.store).await.unwrap();
    assert!(!da.groups.contains_key(&g));
    assert_eq!(da.ignored_markers, vec![g]);
    assert_eq!(guard_of(a.w[1].certify(&g).await), GuardFailure::Uncertified(g));
    let db = discover(&b.store).await.unwrap();
    assert!(db.groups.contains_key(&g));
    assert_eq!(db.heads[&x()], vec![rev_id(&p)]);
    // A's audit reports the raw marker as uncertified (and nothing else).
    let ra = paralean_store::audit::audit(&a.store).await.unwrap();
    assert_eq!(ra.uncertified_markers, vec![g]);
    assert!(ra.ok(), "{:?}", ra.violations);
    b.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// CatalogCertificates `uncertified_not_committed`, TLA `fencing_stale_selected`: a record
/// whose bytes and every object certificate survive, but which never got a commit
/// certificate, is never adopted, however often its bytes are re-acknowledged.
#[tokio::test]
async fn fixture_zombie_record_never_adopted() {
    let e = Env::new("fx-zombie", 2);
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let base = e.w[0].commit_checkpoint(&one_snapshot(&e, 0, "base", t1, None).await).await.unwrap();
    let cp = one_snapshot(&e, 0, "zombie", t1, Some(base)).await;
    let snap = prepare_snapshot(&e, 0, &cp).await;
    let z = e.w[0].sign_record(snap, Some(base), t1);
    e.w[0].stage_record(&z).await.unwrap();
    e.ctl.rotate(e.w[1].id, b"r2").await.unwrap();
    // Re-acknowledging the existing bytes after the rotation is allowed (no write).
    assert!(!e.w[0].stage_record(&z).await.unwrap());
    // Commit is fenced; no repair can create the missing commit certificate.
    assert!(matches!(guard_of(e.w[0].commit_record(&z).await), GuardFailure::StaleToken { .. }));
    let r = e.w[1].repair_cert(&e.store, CertKey::Commit { catalog: z.id() }).await;
    assert_eq!(guard_of(r), GuardFailure::RepairSourceMissing);
    for _ in 0..2 {
        let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
        let s = &r.records[&z.id()];
        assert!(!s.admissible && s.reasons.contains(&"no commit certificate".to_string()));
        assert_eq!(r.selected, Some(base));
    }
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// TargetNames `handover_witness`, TLA `target_stranded_head`: a target published just
/// before a handover is the recorded head, is certified by its own publication (no window
/// without a certificate), and the new owner, with no local state, discovers it and
/// revises it.
#[tokio::test]
async fn fixture_target_published_just_before_handover() {
    let e = Env::new("fx-handover", 2);
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    let (p1, _) = e.publish_target(0, &x(), "p1").await.unwrap();
    let stale = e.prepare(0, &x(), "p1-next", 2).await.unwrap(); // prepared before the handover
    assert!(!e.store.certs(&p1.group.id()).await.unwrap().is_empty(), "certified at publication");
    let ep = e.ctl.reassign(&x(), e.w[1].id, b"handover").await.unwrap();
    let rec = e.store.target(&x()).await.unwrap().unwrap();
    assert_eq!((rec.owner, rec.epoch, rec.head), (e.w[1].id, ep, Some(rev_id(&p1))));
    // The new owner starts with nothing local: discovery finds the head by certificates.
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.heads[&x()], vec![rev_id(&p1)]);
    let p2 = e.prepare(1, &x(), "p2", 3).await.unwrap();
    assert_eq!(p2.revisions[0].parents, vec![rev_id(&p1)]);
    e.w[1].publish(&p2).await.unwrap();
    // The zombie owner's proof is rejected.
    assert!(matches!(guard_of(e.w[0].publish(&stale).await), GuardFailure::NotOwner { .. }));
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.heads[&x()], vec![rev_id(&p2)]);
    assert!(d.conflicts.is_empty());
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// CatalogCertificates `orphan_record_cert_rejected`, TLA `fencing_commit_orphan`: a commit
/// over a parent that was acknowledged but never committed (its writer was fenced out) is
/// rejected.
#[tokio::test]
async fn fixture_orphan_commit_rejected() {
    let e = Env::new("fx-orphan", 2);
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let cp = one_snapshot(&e, 0, "parent", t1, None).await;
    let snap = prepare_snapshot(&e, 0, &cp).await;
    let parent = e.w[0].sign_record(snap, None, t1);
    e.w[0].stage_record(&parent).await.unwrap(); // acknowledged, not committed
    let t2 = e.ctl.rotate(e.w[1].id, b"r2").await.unwrap();
    let child_cp = one_snapshot(&e, 1, "child", t2, Some(parent.id())).await;
    let g = guard_of(e.w[1].commit_checkpoint(&child_cp).await);
    assert_eq!(g, GuardFailure::ParentUncommitted(parent.id()));
    let r = recover_catalog(&e.store, e.w[1].id).await.unwrap();
    assert!(r.records.values().all(|s| !s.admissible));
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// TargetNames `stale_publication_blocked`, HARDENED `stale_owner_publish_blocked`.
#[tokio::test]
async fn fixture_stale_owner_publish_after_reassignment() {
    let e = Env::new("fx-staleowner", 2);
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    let p = e.prepare(0, &x(), "old", 1).await.unwrap();
    e.ctl.reassign(&x(), e.w[1].id, b"to-b").await.unwrap();
    assert_eq!(guard_of(e.w[0].publish(&p).await), GuardFailure::NotOwner { name: x() });
    // Even after the name comes back, the proof prepared under epoch 0 stays stale.
    e.ctl.reassign(&x(), e.w[0].id, b"back-to-a").await.unwrap();
    assert_eq!(guard_of(e.w[0].publish(&p).await), GuardFailure::StaleEpoch { name: x(), prepared: 0, current: 2 });
    let g = p.group.id();
    assert!(e.store.marker(&g).await.unwrap().is_none());
    assert!(e.store.certs(&g).await.unwrap().is_empty());
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, None);
    e.audit_ok().await;
}

// ---------------------------------------------------------------------------------------
/// Plan P2 gate, HARDENED `hardened_certified_recovery`: checkpoint recovery after losing
/// the desktop's last manifest hash, by enumeration (paginated scans with a tiny page),
/// with distractors: a zombie record, another workspace's chain, a stale writer's record.
#[tokio::test]
async fn fixture_checkpoint_recovery_after_losing_last_manifest_hash() {
    let mut cfg = StoreConfig::from_env(&common::deployment("fx-recovery")).unwrap();
    cfg.page = 2; // force many pages
    let e = Env::open(cfg.clone(), 2, Faults::none());
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let mut last = None;
    let mut contents = Vec::new();
    for i in 0..3 {
        let p = e.plain_package(0, &format!("Chain.n{i}"), &format!("chain{i}"));
        e.w[0].publish(&p).await.unwrap();
        contents.push(rev_id(&p));
        let cp = fixture::checkpoint(e.w[0].id, contents.clone(), last, t1, &format!("cp{i}"));
        last = Some(e.w[0].commit_checkpoint(&cp).await.unwrap());
    }
    // The workspace's writer re-acquires the fence and commits once more.
    let t3 = e.ctl.rotate(e.w[0].id, b"r3").await.unwrap();
    let p = e.plain_package(0, "Chain.n3", "chain3");
    e.w[0].publish(&p).await.unwrap();
    contents.push(rev_id(&p));
    let head = e.w[0].commit_checkpoint(&fixture::checkpoint(e.w[0].id, contents.clone(), last, t3, "cp3")).await.unwrap();
    // Distractors.
    let zcp = one_snapshot(&e, 0, "zombie", t3, Some(head)).await;
    let zsnap = prepare_snapshot(&e, 0, &zcp).await;
    e.w[0].stage_record(&e.w[0].sign_record(zsnap, Some(head), t3)).await.unwrap();
    let t4 = e.ctl.rotate(e.w[1].id, b"r4").await.unwrap();
    e.w[1].commit_checkpoint(&one_snapshot(&e, 1, "other", t4, None).await).await.unwrap();

    // The desktop is lost: drop every handle and every local ID. Reopen from configuration
    // and keys only.
    drop(e);
    let r2 = Env::open(cfg, 2, Faults::none());
    let ws = r2.w[0].id;
    let t3 = r2.store.token(2).await.unwrap().unwrap().token.body.token;
    let rec = recover_catalog(&r2.store, ws).await.unwrap();
    assert_eq!(rec.selected, Some(head), "{:#?}", rec.records);
    assert!(!rec.conflict);
    let sel = r2.store.record(&head).await.unwrap().unwrap();
    assert_eq!(sel.body.token, t3, "the selected record was committed under its own fence");
    // The selected snapshot's contents are rediscovered by certificates and fetched by ID.
    let snap: Snapshot = r2.store.s3.get_object(Kind::Snapshot, &sel.body.snapshot).await.unwrap().unwrap();
    assert_eq!(snap.contents, {
        let mut c = contents.clone();
        c.sort();
        c
    });
    let d = discover(&r2.store).await.unwrap();
    for rid in &snap.contents {
        let rv = &d.revisions[rid];
        assert!(d.groups.contains_key(&rv.group));
        assert!(r2.store.s3.get(Kind::Group, &rv.group).await.unwrap().is_some());
        assert_eq!(d.heads[&rv.name], vec![*rid]);
    }
    r2.audit_ok().await;
}
