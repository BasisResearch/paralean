//! Client-side fault injection against the real services: crashes between payload and
//! metadata, injected `commit_unknown_result` on every transaction type, rotation and
//! reassignment between a read and a commit, duplicate and reordered retries, S3 timeouts
//! with and without the object landing, corrupt reads, concurrent writers and a paginated
//! scan across concurrent publications. After every scenario the whole-store audit must
//! pass, in particular "no metadata key names an object absent from S3".

mod common;

use std::sync::Arc;

use common::*;
use paralean_store::recovery::{discover, discover_with, recover_catalog};
use paralean_store::*;

fn x() -> Name {
    Name::parse("Target.x")
}

// ------------------------------------------------------------------ crashes

#[tokio::test]
async fn crash_between_payload_and_metadata_then_restart() {
    let e = Env::new("fi-crash", 1);
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    let points: Vec<(&str, Box<dyn Fn(&Arc<Faults>)>)> = vec![
        ("after-payload", Box::new(|f: &Arc<Faults>| f.crash_at("publish:after-payload", 0))),
        ("after-staged-marker", Box::new(|f: &Arc<Faults>| f.crash_at("publish:after-staged-marker", 0))),
        ("s3-put-landed", Box::new(|f: &Arc<Faults>| f.on_put(Some(Kind::Capsule), 0, PutFault::CrashAfterLanded))),
        ("t1-before-commit", Box::new(|f: &Arc<Faults>| f.on_commit(Some(Txn::T1Publish), 0, CommitFault::CrashBeforeCommit))),
        ("t1-after-commit", Box::new(|f: &Arc<Faults>| f.on_commit(Some(Txn::T1Publish), 0, CommitFault::CrashAfterCommit))),
    ];
    for (i, (label, arm)) in points.iter().enumerate() {
        let faults = Faults::none();
        arm(&faults);
        let crashing = e.writer_with(0, faults);
        let p = e.prepare(0, &x(), &format!("crash{i}"), i as u64).await.unwrap();
        let r = crashing.publish(&p).await;
        assert!(matches!(r, Err(StoreError::Crashed(_))), "{label}: {r:?}");
        e.audit_ok().await; // nothing names an unacknowledged object
        // The restarted writer (no local state beyond the package it re-derives) retries.
        let o = e.w[0].publish(&p).await.unwrap();
        assert_eq!(o.fresh, *label != "t1-after-commit", "{label}");
        assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(&p)));
        e.audit_ok().await;
    }
}

/// TLA `target_stranded_head` / `cert_stranded_publication`: the publisher dies right
/// after its publication. Its certificate was written by the publication itself, so the
/// head stays discoverable and the new owner can revise it. (Under the lagging design,
/// `--features mutate-cert-outside-publish`, this test must fail.)
#[tokio::test]
async fn publisher_crash_right_after_publish_leaves_head_discoverable() {
    let e = Env::new("fi-stranded", 2);
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    let faults = Faults::none();
    faults.crash_at("publish:before-cert", 0);
    let p = e.prepare(0, &x(), "p1", 1).await.unwrap();
    let _ = e.writer_with(0, faults).publish(&p).await; // dies after T1, if the point exists
    e.ctl.reassign(&x(), e.w[1].id, b"handover").await.unwrap();
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.heads.get(&x()), Some(&vec![rev_id(&p)]), "the recorded head is discoverable");
    let a = paralean_store::audit::audit(&e.store).await.unwrap();
    assert!(a.uncertified_markers.is_empty(), "published group without a certificate: {:?}", a.uncertified_markers);
    let p2 = e.prepare(1, &x(), "p2", 2).await.unwrap();
    e.w[1].publish(&p2).await.unwrap();
    e.audit_ok().await;
}

#[tokio::test]
async fn crash_during_checkpoint_then_retry() {
    let e = Env::new("fi-crash-cp", 1);
    let tok = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let mut pred = None;
    let arms: Vec<Box<dyn Fn(&Arc<Faults>)>> = vec![
        Box::new(|f| f.crash_at("checkpoint:before-snapshot", 0)),
        Box::new(|f| f.crash_at("checkpoint:before-record", 0)),
        Box::new(|f| f.on_commit(Some(Txn::T6ObjectCert), 2, CommitFault::CrashAfterCommit)),
        Box::new(|f| f.on_commit(Some(Txn::T5Commit), 0, CommitFault::CrashBeforeCommit)),
        Box::new(|f| f.on_commit(Some(Txn::T5Commit), 0, CommitFault::CrashAfterCommit)),
    ];
    for (i, arm) in arms.iter().enumerate() {
        let cp = one_snapshot(&e, 0, &format!("cp{i}"), tok, pred).await;
        let faults = Faults::none();
        arm(&faults);
        let r = e.writer_with(0, faults).commit_checkpoint(&cp).await;
        assert!(matches!(r, Err(StoreError::Crashed(_))), "arm {i}: {r:?}");
        e.audit_ok().await;
        let c = e.w[0].commit_checkpoint(&cp).await.unwrap();
        pred = Some(c);
        assert_eq!(recover_catalog(&e.store, e.w[0].id).await.unwrap().selected, Some(c));
    }
    e.audit_ok().await;
}

// ------------------------------------------------------------------ unknown results

#[tokio::test]
async fn unknown_commit_result_on_every_transaction() {
    for committed in [true, false] {
        let faults = Faults::none();
        let e = Env::with_faults(&format!("fi-unknown-{committed}"), 2, faults.clone());
        let f = if committed { CommitFault::UnknownCommitted } else { CommitFault::UnknownNotCommitted };
        for t in [Txn::T1Publish, Txn::T2Certify, Txn::T3Rotate, Txn::T4Reassign, Txn::T5Stage, Txn::T5Commit, Txn::T6ObjectCert, Txn::T7Repair] {
            faults.on_commit(Some(t), 0, f.clone());
        }
        // T4 (create) and T3.
        assert_eq!(e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap(), 0);
        assert_eq!(e.store.target(&x()).await.unwrap().unwrap().epoch, 0);
        let tok = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
        assert_eq!((tok.rank, e.store.fence().await.unwrap()), (1, 1), "rank issued once");
        // T1.
        let (p, o) = e.publish_target(0, &x(), "p").await.unwrap();
        assert_eq!(o.fresh, !committed);
        // T2.
        e.w[1].certify(&p.group.id()).await.unwrap();
        assert_eq!(e.store.certs(&p.group.id()).await.unwrap().len(), 2);
        // T6, T5 (stage then commit) through a checkpoint.
        let cp = one_snapshot(&e, 0, "cp", tok, None).await;
        let snap = prepare_snapshot(&e, 0, &cp).await;
        let rec = e.w[0].sign_record(snap, None, tok);
        e.w[0].stage_record(&rec).await.unwrap();
        e.w[0].commit_record(&rec).await.unwrap();
        assert_eq!(recover_catalog(&e.store, e.w[0].id).await.unwrap().selected, Some(rec.id()));
        // T7: repair a certificate into a second deployment holding the marker bytes.
        let mut cfg = e.cfg.clone();
        cfg.deployment = common::deployment("fi-unknown-dst");
        let dst = Env::open(cfg, 2, faults.clone());
        let g = p.group.id();
        let mv = e.store.meta.get(e.store.meta.keys.marker(&g)).await.unwrap().unwrap();
        dst.store.meta.raw_set(dst.store.meta.keys.marker(&g), mv).await.unwrap();
        dst.w[0].repair_cert(&e.store, CertKey::Publication { group: g, writer: e.w[0].id }).await.unwrap();
        assert_eq!(dst.store.certs(&g).await.unwrap().len(), 1);
        let st = faults.stats();
        let injected: u64 = st.iter().filter(|(k, _)| k.starts_with("commit:")).map(|(_, v)| *v).sum();
        assert_eq!(injected, 8, "every transaction type got an unknown result: {st:?}");
        e.audit_ok().await;
    }
}

#[tokio::test]
async fn rotation_and_reassignment_between_read_and_commit() {
    let faults = Faults::none();
    let e = Env::with_faults("fi-interleave", 2, faults.clone());
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    // T1: reassignment lands between T1's reads and its commit: the commit conflicts, the
    // retry re-reads the record and aborts.
    let p = e.prepare(0, &x(), "p", 1).await.unwrap();
    faults.on_commit(Some(Txn::T1Publish), 0, CommitFault::Interleave(reassign_hook(&e.ctl, x(), e.w[1].id, "mid")));
    assert!(matches!(guard_of(e.w[0].publish(&p).await), GuardFailure::NotOwner { .. }));
    assert!(e.store.certs(&p.group.id()).await.unwrap().is_empty());
    // T5: rotation between the fence read and the commit.
    let tok = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let cp = one_snapshot(&e, 0, "cp", tok, None).await;
    let snap = prepare_snapshot(&e, 0, &cp).await;
    let rec = e.w[0].sign_record(snap, None, tok);
    faults.on_commit(Some(Txn::T5Commit), 0, CommitFault::Interleave(rotate_hook(&e.ctl, e.w[1].id, "mid")));
    assert_eq!(guard_of(e.w[0].commit_record(&rec).await), GuardFailure::StaleToken { rank: 1, fence: 2 });
    assert!(e.store.record(&rec.id()).await.unwrap().is_none());
    // T3: a concurrent rotation between read and commit: both get distinct ranks.
    faults.on_commit(Some(Txn::T3Rotate), 0, CommitFault::Interleave(rotate_hook(&e.ctl, e.w[0].id, "inner")));
    let outer = e.ctl.rotate(e.w[1].id, b"outer").await.unwrap();
    assert_eq!(outer.rank, 4);
    assert_eq!(e.store.token(3).await.unwrap().unwrap().request, b"inner".to_vec());
    e.audit_ok().await;
}

// ------------------------------------------------------------------ retries

#[tokio::test]
async fn duplicate_and_reordered_retries() {
    let e = Env::new("fi-retries", 2);
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    // Duplicate concurrent publishes of one package: exactly one is fresh.
    let p1 = e.prepare(0, &x(), "p1", 1).await.unwrap();
    let (a, b) = tokio::join!(e.w[0].publish(&p1), e.w[0].publish(&p1));
    let (a, b) = (a.unwrap(), b.unwrap());
    assert!(a.fresh ^ b.fresh, "{a:?} {b:?}");
    // p2 revises p1; then a late retry of p1's publish arrives: effect present, head stays.
    let p2 = e.prepare(0, &x(), "p2", 2).await.unwrap();
    e.w[0].publish(&p2).await.unwrap();
    assert!(!e.w[0].publish(&p1).await.unwrap().fresh);
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(&p2)));
    // A reordered T4 retry (an older request after a newer one) does not revert ownership.
    e.ctl.reassign(&x(), e.w[1].id, b"to-b").await.unwrap();
    e.ctl.reassign(&x(), e.w[0].id, b"to-a").await.unwrap();
    assert_eq!(e.ctl.reassign(&x(), e.w[1].id, b"to-b").await.unwrap(), 1);
    let r = e.store.target(&x()).await.unwrap().unwrap();
    assert_eq!((r.owner, r.epoch), (e.w[0].id, 2));
    // A reordered T3 retry returns its original rank and issues nothing new.
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let t2 = e.ctl.rotate(e.w[1].id, b"r2").await.unwrap();
    assert_eq!(e.ctl.rotate(e.w[0].id, b"r1").await.unwrap(), t1);
    assert_eq!(e.store.fence().await.unwrap(), t2.rank);
    // A late retry of a committed T5 after a newer commit and rotation: effect present.
    let cp = one_snapshot(&e, 1, "cp", t2, None).await;
    let c = e.w[1].commit_checkpoint(&cp).await.unwrap();
    let rec = e.store.record(&c).await.unwrap().unwrap();
    e.ctl.rotate(e.w[0].id, b"r3").await.unwrap();
    let again = e.w[1].sign_record(rec.body.snapshot, None, t2);
    assert!(!e.w[1].commit_record(&again).await.unwrap());
    // Duplicate certificate writes.
    for _ in 0..3 {
        e.w[1].certify(&p1.group.id()).await.unwrap();
    }
    assert_eq!(e.store.certs(&p1.group.id()).await.unwrap().len(), 2);
    e.audit_ok().await;
}

#[tokio::test]
async fn s3_put_timeouts_with_and_without_landing() {
    let faults = Faults::none();
    let e = Env::with_faults("fi-s3timeout", 1, faults.clone());
    faults.on_put(Some(Kind::Group), 0, PutFault::TimeoutNotLanded);
    faults.on_put(Some(Kind::Group), 0, PutFault::TimeoutLanded);
    faults.on_put(Some(Kind::Capsule), 0, PutFault::TimeoutLanded);
    faults.on_put(Some(Kind::StagedMarker), 0, PutFault::TimeoutNotLanded);
    let p = e.plain_package(0, "N", "g");
    e.w[0].publish(&p).await.unwrap();
    let st = faults.stats();
    assert_eq!(st.get("put:TimeoutLanded"), Some(&2));
    assert_eq!(st.get("put:TimeoutNotLanded"), Some(&2));
    e.audit_ok().await;
}

// ------------------------------------------------------------------ corrupt reads

#[tokio::test]
async fn corrupt_bytes_on_read_count_as_missing() {
    let faults = Faults::none();
    let e = Env::with_faults("fi-corrupt", 1, faults.clone());
    let tok = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let c = e.w[0].commit_checkpoint(&one_snapshot(&e, 0, "cp", tok, None).await).await.unwrap();
    // One corrupt snapshot read during recovery: the record is not ready in that scan.
    faults.on_get(Some(Kind::Snapshot), 0, GetFault::Corrupt);
    let r = recover_catalog(&e.store, e.w[0].id).await.unwrap();
    assert_eq!(r.selected, None);
    assert!(r.records[&c].reasons.iter().any(|w| w.contains("snapshot bytes missing or corrupt")));
    assert_eq!(recover_catalog(&e.store, e.w[0].id).await.unwrap().selected, Some(c));
    // A corrupt read of a payload is not an acknowledgement: no object certificate.
    let o = Opaque::new(Kind::Capsule, b"fresh".to_vec());
    e.store.s3.put_opaque(&o).await.unwrap();
    faults.on_get(Some(Kind::Capsule), 0, GetFault::Corrupt);
    assert!(matches!(guard_of(e.w[0].certify_existing(Kind::Capsule, &o.id()).await), GuardFailure::NotAcknowledged { .. }));
    assert!(faults.stats().get("hash-mismatch-on-read").copied().unwrap_or(0) >= 2);
    // Oversized marker (deep rootPath): spilled to a blob; corrupting the blob at rest
    // makes the group undiscoverable rather than wrong.
    let mut p = e.plain_package(0, "Deep", "deep");
    p.marker.root_path = (0..3000).map(|i| (Id([(i % 251) as u8; 32]), i, AgentId::derive("a"))).collect();
    e.w[0].publish(&p).await.unwrap();
    let g = p.group.id();
    let v = e.store.meta.get(e.store.meta.keys.marker(&g)).await.unwrap().unwrap();
    assert_eq!(v[0], 1, "marker value is a blob reference");
    assert!(discover(&e.store).await.unwrap().groups.contains_key(&g));
    let blob = Id(v[33..65].try_into().unwrap());
    e.store.s3.corrupt_at_rest(Kind::Blob, &blob, b"rot").await.unwrap();
    let d = discover(&e.store).await.unwrap();
    assert!(!d.groups.contains_key(&g));
    assert_eq!(d.dangling_certs, 1);
    let r = paralean_store::audit::audit(&e.store).await.unwrap();
    assert!(r.violations.iter().any(|v| v.contains("blob")), "audit flags the corrupt blob: {:?}", r.violations);
}

// ------------------------------------------------------------------ concurrency

#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn concurrent_writers_multi_threaded() {
    let e = Arc::new(Env::new("fi-concurrent", 4));
    e.ctl.reassign(&x(), e.w[0].id, b"assign").await.unwrap();
    let mut hs = Vec::new();
    // The owner races several proofs against one head: CAS lets exactly one per head win.
    for i in 0..6 {
        let e = e.clone();
        hs.push(tokio::spawn(async move {
            let mut wins = 0;
            for j in 0..5 {
                let Ok(p) = e.prepare(0, &x(), &format!("race{i}-{j}"), (i * 10 + j) as u64).await else { continue };
                match e.w[0].publish(&p).await {
                    Ok(_) => wins += 1,
                    Err(StoreError::Guard(GuardFailure::HeadMoved { .. })) => {}
                    Err(err) => panic!("{err}"),
                }
            }
            wins
        }));
    }
    // Non-owners never publish a target proof.
    for wi in 1..4 {
        let e = e.clone();
        hs.push(tokio::spawn(async move {
            let pt = PreparedTarget { name: x(), epoch: 0, head: None };
            let p = fixture::package(&format!("intruder{wi}"), e.w[wi].id, &e.validator, &x(), vec![], Some(pt), 1);
            assert!(e.w[wi].publish(&p).await.is_err());
            // ...but publish free names and certify each other's groups.
            for j in 0..5 {
                let p = e.plain_package(wi, &format!("Free.w{wi}.n{j}"), &format!("free{wi}-{j}"));
                e.w[wi].publish(&p).await.unwrap();
            }
            0
        }));
    }
    // Concurrent rotations and commits by whoever holds the fence.
    for wi in 1..4 {
        let e = e.clone();
        hs.push(tokio::spawn(async move {
            let mut pred = None;
            for j in 0..3 {
                let tok = e.ctl.rotate(e.w[wi].id, format!("rot{wi}-{j}").as_bytes()).await.unwrap();
                let cp = one_snapshot(&e, wi, &format!("cc{wi}-{j}"), tok, pred).await;
                match e.w[wi].commit_checkpoint(&cp).await {
                    Ok(c) => pred = Some(c),
                    Err(StoreError::Guard(GuardFailure::StaleToken { .. })) => {}
                    Err(StoreError::Guard(GuardFailure::ParentUncommitted(_))) => {}
                    Err(err) => panic!("{err}"),
                }
            }
            0
        }));
    }
    let mut wins = 0;
    for h in hs {
        wins += h.await.unwrap();
    }
    assert!(wins >= 1);
    let d = discover(&e.store).await.unwrap();
    let heads = &d.heads[&x()];
    assert_eq!(heads.len(), 1, "one head for the target");
    assert_eq!(Some(heads[0]), e.store.target(&x()).await.unwrap().unwrap().head);
    let target_revs = d.revisions.values().filter(|r| r.name == x()).count();
    assert_eq!(target_revs, wins, "every winning proof is published and chained");
    e.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn paginated_scan_across_concurrent_publications() {
    let mut cfg = StoreConfig::from_env(&common::deployment("fi-scan")).unwrap();
    cfg.page = 3;
    let e = Arc::new(Env::open(cfg, 2, Faults::none()));
    let mut before = Vec::new();
    for i in 0..10 {
        let p = e.plain_package(0, &format!("S.n{i}"), &format!("s{i}"));
        e.w[0].publish(&p).await.unwrap();
        before.push(p.group.id());
    }
    let e2 = e.clone();
    let counter = Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let d = discover_with(&e.store, move |page| {
        let e2 = e2.clone();
        let counter = counter.clone();
        Some(Box::pin(async move {
            // Publish two more groups between pages of the certificate scan.
            for k in 0..2 {
                let n = counter.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                let p = e2.plain_package(1, &format!("S.late{page}.{k}"), &format!("late{n}"));
                e2.w[1].publish(&p).await.unwrap();
            }
        }) as futures::future::BoxFuture<'static, ()>)
    })
    .await
    .unwrap();
    // Everything committed before the scan started is found ...
    for g in &before {
        assert!(d.groups.contains_key(g));
    }
    // ... and everything found is published (certified marker present).
    for g in d.groups.keys() {
        assert!(!e.store.certs(g).await.unwrap().is_empty());
    }
    e.audit_ok().await;
}
