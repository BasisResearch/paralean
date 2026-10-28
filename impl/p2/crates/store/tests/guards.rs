//! Unit tests for each transaction guard (T1–T7) and the payload-store rules, against the
//! real FoundationDB and Garage services.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use common::*;
use paralean_store::*;

fn x() -> Name {
    Name::parse("Target.x")
}

async fn assigned(name: &str, n: usize) -> Env {
    let e = Env::new(name, n);
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    e
}

// ------------------------------------------------------------------ T1

#[tokio::main(flavor = "current_thread")]
async fn t1_publish_writes_marker_cert_head_atomically() {
    let faults = Faults::none();
    let e = Env::with_faults("t1ok", 1, faults.clone());
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let before = real_commit_unknowns(&faults);
    let (p, o) = e.publish_target(0, &x(), "p1").await.unwrap();
    assert_fresh_or_real_unknown(o.fresh, before, &faults);
    let g = p.group.id();
    let (mid, _) = e.store.marker(&g).await.unwrap().unwrap();
    assert_eq!(mid, o.marker);
    assert_eq!(e.store.certs(&g).await.unwrap().len(), 1, "publisher's certificate in the same transaction");
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(&p)));
    // Idempotent: a retry finds the effect and writes nothing.
    let o2 = e.w[0].publish(&p).await.unwrap();
    assert!(!o2.fresh);
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn t1_rejects_non_owner() {
    let e = assigned("t1owner", 2).await;
    let p = e.prepare(0, &x(), "p1", 1).await.unwrap();
    // Writer 1 tries to publish writer 0's prepared proof under its own identity.
    let mut p1 = fixture::package("p1b", e.w[1].id, &e.validator, &x(), vec![], p.targets.first().cloned(), 1);
    p1.targets[0].epoch = 0;
    let g = guard_of(e.w[1].publish(&p1).await);
    assert!(matches!(g, GuardFailure::NotOwner { .. }), "{g:?}");
    assert!(e.store.marker(&p1.group.id()).await.unwrap().is_none(), "aborted T1 writes nothing");
    assert_eq!(guard_of(e.w[1].prepare_target(&x()).await), GuardFailure::NotOwner { name: x() });
}

#[tokio::main(flavor = "current_thread")]
async fn t1_rejects_stale_epoch_after_reassignment() {
    let e = assigned("t1epoch", 2).await;
    let p = e.prepare(0, &x(), "p1", 1).await.unwrap();
    e.ctl.reassign(&x(), e.w[0].id, b"reassign-same-owner").await.unwrap(); // epoch 1, same owner
    let g = guard_of(e.w[0].publish(&p).await);
    assert_eq!(g, GuardFailure::StaleEpoch { name: x(), prepared: 0, current: 1 });
    let g0 = p.group.id();
    assert!(e.store.marker(&g0).await.unwrap().is_none());
    assert!(e.store.certs(&g0).await.unwrap().is_empty(), "a failed publish never certifies (§8.2)");
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn t1_head_compare_and_swap() {
    let e = assigned("t1cas", 1).await;
    // Two proofs prepared against the same (empty) head; the second publish must fail.
    let a = e.prepare(0, &x(), "a", 1).await.unwrap();
    let b = e.prepare(0, &x(), "b", 2).await.unwrap();
    e.w[0].publish(&a).await.unwrap();
    let g = guard_of(e.w[0].publish(&b).await);
    assert_eq!(g, GuardFailure::HeadMoved { name: x(), prepared: None, current: Some(rev_id(&a)) });
    // A proof that claims the right head but does not list it as a parent.
    let mut c = e.prepare(0, &x(), "c", 3).await.unwrap();
    c = fixture::package("c", e.w[0].id, &e.validator, &x(), vec![], c.targets.first().cloned(), 3);
    assert_eq!(guard_of(e.w[0].publish(&c).await), GuardFailure::NotRevisingHead(x()));
    // The correct revision publishes.
    let d = e.prepare(0, &x(), "d", 4).await.unwrap();
    e.w[0].publish(&d).await.unwrap();
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(&d)));
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn t1_rejects_unadmitted_parent_bad_receipt_and_duplicates() {
    let e = Env::new("t1misc", 1);
    // Unknown parent revision.
    let p = fixture::package("u", e.w[0].id, &e.validator, &Name::parse("N"), vec![Id([7; 32])], None, 1);
    assert_eq!(guard_of(e.w[0].publish(&p).await), GuardFailure::UnknownParentRevision(Id([7; 32])));
    // Receipt by an untrusted validator.
    let rogue = Signer::derive("rogue-validator");
    let p = fixture::package("r", e.w[0].id, &rogue, &Name::parse("N"), vec![], None, 1);
    assert!(matches!(guard_of(e.w[0].publish(&p).await), GuardFailure::ReceiptRejected(_)));
    // No target record.
    let pt = PreparedTarget { name: x(), epoch: 0, head: None };
    let p = fixture::package("t", e.w[0].id, &e.validator, &x(), vec![], Some(pt), 1);
    assert_eq!(guard_of(e.w[0].publish(&p).await), GuardFailure::NoTargetRecord(x()));
    // The same group under a different marker.
    let p = e.plain_package(0, "M", "same");
    e.w[0].publish(&p).await.unwrap();
    let mut p2 = p.clone();
    p2.marker.lamport = 99;
    assert!(matches!(guard_of(e.w[0].publish(&p2).await), GuardFailure::AlreadyPublished { .. }));
    e.audit_ok().await;
}

// ------------------------------------------------------------------ T2

#[tokio::main(flavor = "current_thread")]
async fn t2_certify_requires_published_and_certified() {
    let faults = Faults::none();
    let e = Env::with_faults("t2", 2, faults.clone());
    let p = e.plain_package(0, "N", "g");
    let g = p.group.id();
    assert_eq!(guard_of(e.w[1].certify(&g).await), GuardFailure::NotPublished(g));
    e.w[0].publish(&p).await.unwrap();
    let before = real_commit_unknowns(&faults);
    let fresh = e.w[1].certify(&g).await.unwrap();
    assert_fresh_or_real_unknown(fresh, before, &faults);
    assert!(!e.w[1].certify(&g).await.unwrap(), "idempotent");
    let certs = e.store.certs(&g).await.unwrap();
    assert_eq!(certs.len(), 2);
    assert!(certs.iter().any(|c| c.body.writer == e.w[1].id && c.body.marker == p.marker.id()));
    // A raw marker key with no certificate is not evidence of publication.
    let q = e.plain_package(0, "N2", "raw");
    let qg = q.group.id();
    let v = e.store.stage_value(q.marker.id(), q.marker.preimage()).await.unwrap();
    e.store.meta.raw_set(e.store.meta.keys.marker(&qg), v).await.unwrap();
    assert_eq!(guard_of(e.w[1].certify(&qg).await), GuardFailure::Uncertified(qg));
}

// ------------------------------------------------------------------ T3

#[tokio::main(flavor = "current_thread")]
async fn t3_rotation_issues_each_rank_once() {
    let e = Env::new("t3", 2);
    let t1 = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    assert_eq!(t1.rank, 1);
    assert_eq!(e.ctl.rotate(e.w[0].id, b"r1").await.unwrap(), t1, "same request: same rank");
    // Concurrent rotations: every rank issued once (read-modify-write, not an atomic add).
    let mut hs = Vec::new();
    for i in 0..12 {
        let ctl = e.ctl.clone();
        let w = e.w[i % 2].id;
        hs.push(tokio::spawn(async move { ctl.rotate(w, format!("c{i}").as_bytes()).await.unwrap() }));
    }
    let mut ranks: Vec<u64> = Vec::new();
    for h in hs {
        ranks.push(h.await.unwrap().rank);
    }
    ranks.sort();
    assert_eq!(ranks, (2..=13).collect::<Vec<_>>());
    assert_eq!(e.store.fence().await.unwrap(), 13);
    e.audit_ok().await;
}

// ------------------------------------------------------------------ T4

#[tokio::main(flavor = "current_thread")]
async fn t4_reassign_bumps_epoch_keeps_head() {
    let e = assigned("t4", 2).await;
    let (p, _) = e.publish_target(0, &x(), "p1").await.unwrap();
    let ep = e.ctl.reassign(&x(), e.w[1].id, b"to-w1").await.unwrap();
    assert_eq!(ep, 1);
    assert_eq!(e.ctl.reassign(&x(), e.w[1].id, b"to-w1").await.unwrap(), 1, "same request: no second bump");
    let r = e.store.target(&x()).await.unwrap().unwrap();
    assert_eq!((r.owner, r.epoch, r.head), (e.w[1].id, 1, Some(rev_id(&p))));
}

// ------------------------------------------------------------------ T5

#[tokio::main(flavor = "current_thread")]
async fn t5_fenced_commit_and_its_guards() {
    let faults = Faults::none();
    let e = Env::with_faults("t5", 2, faults.clone());
    let tok = e.ctl.rotate(e.w[0].id, b"r1").await.unwrap();
    let cp = one_snapshot(&e, 0, "a", tok, None).await;
    let c = e.w[0].commit_checkpoint(&cp).await.unwrap();
    assert!(e.store.meta.get(e.store.meta.keys.rcert(&c)).await.unwrap().is_some());
    // Idempotent.
    let rec = e.w[0].sign_record(e.store.record(&c).await.unwrap().unwrap().body.snapshot, None, tok);
    assert!(!e.w[0].commit_record(&rec).await.unwrap());

    // Manifest (snapshot) uncertified: a record naming an uncertified snapshot.
    let bogus = e.w[0].sign_record(Id([9; 32]), Some(c), tok);
    assert_eq!(guard_of(e.w[0].commit_record(&bogus).await), GuardFailure::ManifestUncertified(Id([9; 32])));

    // Token for a rank whose holder is someone else.
    let forged = TokenRef { rank: tok.rank, holder: e.w[1].id };
    let rec2 = e.w[1].sign_record(rec.body.snapshot, None, forged);
    assert_eq!(guard_of(e.w[1].commit_record(&rec2).await), GuardFailure::TokenNotIssued(tok.rank));

    // Parent not committed: stage a record (fenced first write) without committing it.
    let cp2 = one_snapshot(&e, 0, "b", tok, None).await;
    let snap2 = cp2.snapshot.clone();
    let st = &e.store;
    for m in [&cp2.source_root, &cp2.build_receipt] {
        let a = st.s3.put_object(Kind::Manifest, m).await.unwrap();
        e.w[0].certify_object(a).await.unwrap();
    }
    let a = st.s3.put_object(Kind::Snapshot, &snap2).await.unwrap();
    e.w[0].certify_object(a).await.unwrap();
    let staged = e.w[0].sign_record(a.id(), Some(c), tok);
    let before = real_commit_unknowns(&faults);
    let fresh = e.w[0].stage_record(&staged).await.unwrap();
    assert_fresh_or_real_unknown(fresh, before, &faults);
    assert_eq!(e.store.record(&staged.id()).await.unwrap(), Some(staged.clone()));
    let child = e.w[0].sign_record(a.id(), Some(staged.id()), tok);
    assert_eq!(guard_of(e.w[0].commit_record(&child).await), GuardFailure::ParentUncommitted(staged.id()));

    // Stale token after rotation: both the staging write and the commit abort.
    e.ctl.rotate(e.w[1].id, b"r2").await.unwrap();
    assert_eq!(guard_of(e.w[0].commit_record(&staged).await), GuardFailure::StaleToken { rank: 1, fence: 2 });
    let fresh = e.w[0].sign_record(a.id(), None, tok);
    assert_eq!(guard_of(e.w[0].stage_record(&fresh).await), GuardFailure::StaleToken { rank: 1, fence: 2 });
    e.audit_ok().await;
}

// ------------------------------------------------------------------ T6

#[tokio::main(flavor = "current_thread")]
async fn t6_object_certificate_follows_acknowledgement() {
    let faults = Faults::none();
    let e = Env::with_faults("t6", 1, faults.clone());
    let o = Opaque::new(Kind::Capsule, b"cap".to_vec());
    // Without an acknowledgement there is no Acked value: certify_existing fails.
    assert!(matches!(
        guard_of(e.w[0].certify_existing(Kind::Capsule, &o.id()).await),
        GuardFailure::NotAcknowledged { .. }
    ));
    let a = e.store.s3.put_opaque(&o).await.unwrap();
    let before = real_commit_unknowns(&faults);
    let fresh = e.w[0].certify_object(a).await.unwrap();
    assert_fresh_or_real_unknown(fresh, before, &faults);
    assert!(!e.w[0].certify_object(a).await.unwrap(), "idempotent");
    assert!(e.store.valid_ocert(Kind::Capsule, &o.id()).await.unwrap().is_some());
}

// ------------------------------------------------------------------ T7

#[tokio::main(flavor = "current_thread")]
async fn t7_repair_is_unfenced_signed_and_needs_existing_bytes() {
    // Two deployments stand for the original replica and a replacement holding a copy of
    // the same bytes (same σ: the replica identity is part of the certificate body).
    let src = Env::new("t7src", 1);
    let mut cfg = src.cfg.clone();
    cfg.deployment = common::deployment("t7dst");
    let faults = Faults::none();
    let dst = Env::open(cfg, 1, faults.clone());
    let p = src.plain_package(0, "N", "g");
    let g = p.group.id();
    src.w[0].publish(&p).await.unwrap();
    let key = CertKey::Publication { group: g, writer: src.w[0].id };
    // The replacement lacks the marker bytes: repair refused.
    assert_eq!(guard_of(dst.w[0].repair_cert(&src.store, key.clone()).await), GuardFailure::RepairNoExistingBytes);
    // Copy the marker bytes (existing bytes), rotate the fence, then repair: unfenced, works.
    let mv = src.store.meta.get(src.store.meta.keys.marker(&g)).await.unwrap().unwrap();
    dst.store.meta.raw_set(dst.store.meta.keys.marker(&g), mv).await.unwrap();
    dst.ctl.rotate(dst.w[0].id, b"rot").await.unwrap();
    let before = real_commit_unknowns(&faults);
    let fresh = dst.w[0].repair_cert(&src.store, key.clone()).await.unwrap();
    assert_fresh_or_real_unknown(fresh, before, &faults);
    assert!(!dst.w[0].repair_cert(&src.store, key).await.unwrap(), "idempotent");
    assert_eq!(dst.store.certs(&g).await.unwrap().len(), 1);
    // Another deployment (another abstract replica σ') holding the same bytes is not a
    // replacement of σ: copying σ's certificate there would certify on σ's behalf.
    let other = Env::new("t7other", 1);
    assert_ne!(other.store.replica, src.store.replica);
    let mv = src.store.meta.get(src.store.meta.keys.marker(&g)).await.unwrap().unwrap();
    other.store.meta.raw_set(other.store.meta.keys.marker(&g), mv).await.unwrap();
    let r = other.w[0].repair_cert(&src.store, CertKey::Publication { group: g, writer: src.w[0].id }).await;
    assert_eq!(guard_of(r), GuardFailure::RepairInvalid("certificate names another replica".into()));
    // A forged certificate (bad signature) in the source is refused.
    let forged = Cert::sign(
        CertBody { replica: src.store.replica, marker: p.marker.id(), group: g, writer: src.w[0].id },
        &Signer::derive("not-w0"),
    );
    let fake_writer = WorkspaceId::derive("w0"); // same identity, wrong key
    src.store.meta.raw_set(src.store.meta.keys.cert(&g, &fake_writer), forged.to_bytes()).await.ok();
    let mut cfg2 = src.cfg.clone();
    cfg2.deployment = common::deployment("t7dst2");
    let dst2 = Env::open(cfg2, 1, Faults::none());
    let mv = src.store.meta.get(src.store.meta.keys.marker(&g)).await.unwrap().unwrap();
    dst2.store.meta.raw_set(dst2.store.meta.keys.marker(&g), mv).await.unwrap();
    let r = dst2.w[0].repair_cert(&src.store, CertKey::Publication { group: g, writer: fake_writer }).await;
    assert!(matches!(guard_of(r), GuardFailure::RepairInvalid(_)));
}

// ------------------------------------------------------------------ payload store rules

#[tokio::main(flavor = "current_thread")]
async fn s3_checksum_delete_and_corruption() {
    let e = Env::new("s3", 1);
    let o = Opaque::new(Kind::Chunk, b"chunk bytes".to_vec());
    let a = e.store.s3.put_opaque(&o).await.unwrap();
    assert_eq!(a.id(), o.id());
    // The stored bytes are the preimage: their SHA-256 is the ID.
    let got = e.store.s3.get(Kind::Chunk, &o.id()).await.unwrap().unwrap();
    assert_eq!(id::sha256(&got), o.id().0);
    // The store rejects a body whose digest differs from x-amz-checksum-sha256.
    let other = Opaque::new(Kind::Chunk, b"other".to_vec());
    let err = e.store.s3.put_with_wrong_checksum(Kind::Chunk, &other.id(), b"not the preimage").await;
    assert!(err.is_err(), "store accepted a mislabelled body");
    assert!(e.store.s3.get(Kind::Chunk, &other.id()).await.unwrap().is_none());
    // Deletes are denied.
    let d = e.store.s3.try_delete(Kind::Chunk, &o.id()).await;
    assert!(d.is_err(), "delete was allowed");
    assert!(e.store.s3.get(Kind::Chunk, &o.id()).await.unwrap().is_some());
    // Overwriting with other bytes or copying another object over it is refused, and an
    // identical re-PUT (a retry) is allowed.
    let (put, copy) = e.store.s3.try_overwrite(Kind::Chunk, &o.id(), b"rot", &other.id()).await;
    e.store.s3.put_opaque(&other).await.unwrap();
    let (_, copy_existing) = e.store.s3.try_overwrite(Kind::Chunk, &o.id(), b"rot", &other.id()).await;
    assert!(put.is_err() && copy.is_err() && copy_existing.is_err(), "gateway allowed an overwrite: {put:?} {copy_existing:?}");
    assert_eq!(e.store.s3.get(Kind::Chunk, &o.id()).await.unwrap().unwrap(), got);
    e.store.s3.put_opaque(&o).await.unwrap();
    // Corrupt bytes at rest read as missing; a repair re-PUT restores them.
    e.store.s3.corrupt_at_rest(Kind::Chunk, &o.id(), b"garbage").await.unwrap();
    assert!(e.store.s3.get(Kind::Chunk, &o.id()).await.unwrap().is_none());
    e.store.s3.put_opaque(&o).await.unwrap();
    assert!(e.store.s3.get(Kind::Chunk, &o.id()).await.unwrap().is_some());
}

// ------------------------------------------------------------------ scans

/// Regression (found by `scripts/fdb-kill-test.sh`): FDB returns partial range batches
/// (byte limits) with `more = true`. A scan that stops at a short batch silently drops keys,
/// which breaks `scan_between` / `certScanValue_covers`. 2000 keys of 400 bytes exceed one
/// batch.
#[tokio::main(flavor = "current_thread")]
async fn paginated_scan_follows_partial_batches() {
    let e = Env::new("scan", 1);
    let sub = e.store.meta.keys.sub("scantest");
    for chunk in 0..10u64 {
        let mut trx = e.store.meta.db.create_trx().unwrap();
        let mut committed = false;
        for _ in 0..60 {
            // A commit_unknown_result can mean these writes already landed. Replaying
            // the same fixed keys and values after on_error is therefore idempotent.
            for i in 0..200u64 {
                trx.set(&sub.pack(&(chunk * 200 + i)), &[0xab; 400]);
            }
            match trx.commit().await {
                Ok(_) => { committed = true; break; }
                Err(error) => trx = error.on_error().await.unwrap(),
            }
        }
        assert!(committed, "scan setup chunk {chunk} did not commit after retries");
    }
    for page in [3usize, 500, 10_000] {
        let kvs = e.store.meta.scan(&sub, page, |_| None).await.unwrap();
        assert_eq!(kvs.len(), 2000, "page {page}");
    }
}

/// Rebind a prepared target package's job to `statement` (as a controller stamps it) and
/// re-issue its receipt and marker.
fn with_statement(e: &Env, mut p: Package, statement: &[u8]) -> Package {
    let mut body = p.job.body.clone();
    for t in &mut body.targets {
        t.statement = statement.to_vec();
    }
    p.job = SignedJob::sign(body, &e.authority());
    p.receipt = fixture::receipt_for(&p.job, &e.validator, Verdict::Accepted);
    p.marker.receipt = p.receipt.id();
    p
}

/// W2 A-4. Once the authority pins a target's statement, T1 advances the head only with a
/// job bound to exactly that statement: an owner's empty or other statement (e.g. a proof
/// of `True` named as the target) is refused and the head stays.
#[tokio::main(flavor = "current_thread")]
async fn t1_requires_the_pinned_target_statement() {
    let e = assigned("t1statement", 1).await;
    let pinned = [0x5a; 32];
    assert!(e.ctl.pin_statement(&x(), &pinned).await.unwrap());
    assert!(!e.ctl.pin_statement(&x(), &pinned).await.unwrap(), "re-pinning the same statement is idempotent");
    assert!(e.ctl.pin_statement(&x(), &[0x11; 32]).await.is_err(), "the pin is write-once");
    assert!(e.ctl.pin_statement(&Name::parse("Target.short"), &[1; 31]).await.is_err());
    assert_eq!(e.store.meta.target_statement(&x()).await.unwrap(), Some(pinned.to_vec()));
    for (tag, statement) in [("empty", vec![]), ("other", vec![0x11; 32])] {
        let p = with_statement(&e, e.prepare(0, &x(), tag, 1).await.unwrap(), &statement);
        assert_eq!(guard_of(e.w[0].publish(&p).await), GuardFailure::TargetStatement(x()), "{tag}");
        assert!(e.store.marker(&p.group.id()).await.unwrap().is_none());
        assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, None);
    }
    let p = with_statement(&e, e.prepare(0, &x(), "pinned", 1).await.unwrap(), &pinned);
    e.w[0].publish(&p).await.unwrap();
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(&p)));
    e.audit_ok().await;
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("t1_publish_writes_marker_cert_head_atomically", || { t1_publish_writes_marker_cert_head_atomically(); Ok(()) }),
        libtest_mimic::Trial::test("t1_rejects_non_owner", || { t1_rejects_non_owner(); Ok(()) }),
        libtest_mimic::Trial::test("t1_rejects_stale_epoch_after_reassignment", || { t1_rejects_stale_epoch_after_reassignment(); Ok(()) }),
        libtest_mimic::Trial::test("t1_head_compare_and_swap", || { t1_head_compare_and_swap(); Ok(()) }),
        libtest_mimic::Trial::test("t1_rejects_unadmitted_parent_bad_receipt_and_duplicates", || { t1_rejects_unadmitted_parent_bad_receipt_and_duplicates(); Ok(()) }),
        libtest_mimic::Trial::test("t2_certify_requires_published_and_certified", || { t2_certify_requires_published_and_certified(); Ok(()) }),
        libtest_mimic::Trial::test("t3_rotation_issues_each_rank_once", || { t3_rotation_issues_each_rank_once(); Ok(()) }),
        libtest_mimic::Trial::test("t4_reassign_bumps_epoch_keeps_head", || { t4_reassign_bumps_epoch_keeps_head(); Ok(()) }),
        libtest_mimic::Trial::test("t5_fenced_commit_and_its_guards", || { t5_fenced_commit_and_its_guards(); Ok(()) }),
        libtest_mimic::Trial::test("t6_object_certificate_follows_acknowledgement", || { t6_object_certificate_follows_acknowledgement(); Ok(()) }),
        libtest_mimic::Trial::test("t7_repair_is_unfenced_signed_and_needs_existing_bytes", || { t7_repair_is_unfenced_signed_and_needs_existing_bytes(); Ok(()) }),
        libtest_mimic::Trial::test("s3_checksum_delete_and_corruption", || { s3_checksum_delete_and_corruption(); Ok(()) }),
        libtest_mimic::Trial::test("paginated_scan_follows_partial_batches", || { paginated_scan_follows_partial_batches(); Ok(()) }),
        libtest_mimic::Trial::test("t1_requires_the_pinned_target_statement", || { t1_requires_the_pinned_target_statement(); Ok(()) }),
    ]);
}
