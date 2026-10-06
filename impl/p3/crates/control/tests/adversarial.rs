//! Adversarial validation against the live P2 services (impl/p3/scripts/test.sh). Every
//! attack must fail closed: no marker, no head move, a clean audit. Attacks on T1 itself
//! use `publish_skipping_staging_check`, so the publication transaction's own receipt check
//! is what refuses them; impl/p3/scripts/check-mutations.sh removes each check and requires
//! the named test to fail.

mod common;

use std::time::Duration;

use common::*;
use paralean_control::controller::{ControlRequest, ControlResponse, TargetReq};
use paralean_control::worker::WorkerError;
use paralean_store::receipt::{Revocation, SignedRevocation};
use paralean_store::*;
use paralean_validator_api::{published_receipt, PublishedReceiptError};

fn n(s: &str) -> Name {
    Name::parse(s)
}

/// Upload a group's payloads (what `WorkerNode::validate` does before asking).
async fn upload(w: &Writer, g: &paralean_control::p1::P1Group) {
    w.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
}

/// Both the worker-side staging check and T1 refuse `pkg` with `want`; nothing is published.
async fn refused_both_ways(w: &Writer, pkg: &Package, want: impl Fn(&GuardFailure) -> bool, what: &str) {
    let g1 = guard(w.publish(pkg).await);
    assert!(want(&g1), "{what}: staging check gave {g1:?}");
    let g2 = guard(w.publish_skipping_staging_check(pkg).await);
    assert!(want(&g2), "{what}: T1 gave {g2:?}");
    assert!(!published(&w.store, &pkg.group.id()).await, "{what}: published");
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn end_to_end_target_work_publishes_with_bound_receipts() {
    let c = Cluster::start("e2e", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let target = n("F04.red_ne_green");
    let r = c
        .call(ControlRequest::SubmitWork { request: "e2e/red".into(), target: target.to_string(), memory_mb: 1024 })
        .await;
    assert_eq!(r, ControlResponse::Queued);
    let work = w.poll().await.unwrap().expect("work");
    assert_eq!(work.target, target);
    let out = w.prove(&work).await.unwrap();
    assert!(out.fresh);
    let rec = c.store.target(&target).await.unwrap().unwrap();
    assert_eq!((rec.owner, rec.epoch), (w.id(), work.epoch));
    assert!(rec.head.is_some());
    // The target and its three dependencies are published, each with a receipt that
    // re-verifies (binding, pins, signature by a configured validator, not revoked).
    let g = w.group_declaring(&target).unwrap().clone();
    let closure = paralean_control::p1::closure(&w.groups, &g.gid).unwrap();
    assert_eq!(closure.len(), 4);
    for gid in &closure {
        let d = &w.groups[gid];
        let (rc, job) = published_receipt(&c.store, &d.decl).await.unwrap();
        assert_eq!(rc.body.verdict, Verdict::Accepted);
        assert_eq!(job.body.group, d.decl);
        assert!(c.vsigners.iter().any(|s| s.public() == rc.body.validator_key));
        if *gid == g.gid {
            assert_eq!(job.body.targets.len(), 1);
            assert_eq!((job.body.targets[0].name.clone(), job.body.targets[0].epoch), (target.clone(), work.epoch));
            assert_eq!(hex::encode(&job.body.targets[0].statement), g.statement(&target).unwrap());
        }
    }
    let a = c.audit_ok().await;
    assert!(a.suspect_receipts.is_empty());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn forged_receipts_fail_closed() {
    let c = Cluster::start("forged", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    let (r, j) = w.validate(&g, "forged/genuine", &[], 0).await.unwrap();
    let rogue = Signer::derive("rogue");
    let (_, wsigner) = c.kf.workspace("w0").unwrap();
    let rejected = |f: &GuardFailure| matches!(f, GuardFailure::ReceiptRejected(_));

    // (a) Signed by a key outside the validator set, naming that key.
    let mut body = r.body.clone();
    body.validator_key = rogue.public();
    let a = Receipt::sign(body, &rogue);
    refused_both_ways(&w.writer, &w.package(&g, a, j.clone(), vec![]), rejected, "rogue key").await;
    // (b) Names a configured validator key, signed by another key.
    let b = Receipt { body: r.body.clone(), sig: Receipt::sign(r.body.clone(), &rogue).sig };
    refused_both_ways(&w.writer, &w.package(&g, b, j.clone(), vec![]), rejected, "wrong signer").await;
    // (c) A genuine receipt whose body was changed after signing.
    let mut cc = r.clone();
    cc.body.axioms.push(n("sorryAx"));
    refused_both_ways(&w.writer, &w.package(&g, cc, j.clone(), vec![]), rejected, "altered body").await;
    // (d) The worker certifies itself: its own key as validator.
    let mut body = r.body.clone();
    body.validator_key = wsigner.public();
    let d = Receipt::sign(body, &wsigner);
    refused_both_ways(&w.writer, &w.package(&g, d, j.clone(), vec![]), rejected, "self-signed").await;
    // (e) A genuine receipt with the envelope re-signed by the worker (not the controller).
    let e = paralean_store::receipt::SignedJob::sign(j.body.clone(), &wsigner);
    refused_both_ways(
        &w.writer,
        &w.package(&g, r.clone(), e, vec![]),
        |f| *f == GuardFailure::ReceiptBinding(BindingFault::JobNotIssued),
        "forged envelope",
    )
    .await;
    // The genuine receipt still publishes.
    w.writer.publish(&w.package(&g, r, j, vec![])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn receipt_for_another_group_policy_checker_base_or_target_fails_closed() {
    let c = Cluster::start("othergroup", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let small = w.group_declaring(&n("F01.small")).unwrap().clone();
    let two = w.group_declaring(&n("F01.two_eq")).unwrap().clone();
    let (r, j) = w.validate(&small, "og/small", &[], 0).await.unwrap();
    // Another group's receipt and envelope.
    refused_both_ways(
        &w.writer,
        &w.package(&two, r.clone(), j.clone(), vec![]),
        |f| matches!(f, GuardFailure::ReceiptRejected(_)),
        "other group",
    )
    .await;
    // A misbehaving validator (it holds a configured key) signs a receipt whose slots differ
    // from the envelope it answers.
    let v = &c.vsigners[0];
    let mut variants: Vec<(&str, ReceiptBody, BindingFault)> = Vec::new();
    let mut b = r.body.clone();
    b.validator_key = v.public();
    let mut x = b.clone();
    x.policy = strict_policy().id();
    variants.push(("policy", x, BindingFault::Policy));
    let mut x = b.clone();
    x.validator_bin = CheckerVersion::fixture().id().0.to_vec();
    variants.push(("checker", x, BindingFault::Checker));
    let mut x = b.clone();
    x.base = Id([9; 32]);
    variants.push(("base", x, BindingFault::Base));
    let mut x = b.clone();
    x.target = paralean_store::receipt::target_slot(&[TargetBinding { name: n("F01.small"), epoch: 0, statement: vec![] }]);
    variants.push(("target", x, BindingFault::Target));
    let mut x = b.clone();
    x.request = None;
    variants.push(("no request", x, BindingFault::Request));
    for (what, body, fault) in variants {
        let rc = Receipt::sign(body, v);
        refused_both_ways(&w.writer, &w.package(&small, rc, j.clone(), vec![]), |f| *f == GuardFailure::ReceiptBinding(fault), what).await;
    }
    w.writer.publish(&w.package(&small, r, j, vec![])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn receipt_under_an_unpinned_policy_fails_closed() {
    // The controller stamps a policy the publishers do not pin: the validator enforces it
    // and signs, but no worker stages and T1 refuses.
    let o = Opts { policy: strict_policy(), pinned_policies: vec![paralean_store::receipt::Policy::v1()], ..Opts::default() };
    let c = Cluster::start("unpinned", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    // The controller checks every receipt it records against the pins: it records none.
    match w.validate(&g, "unpinned/small", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Inconclusive { reason })) => assert!(reason.contains("not bound"), "{reason}"),
        other => panic!("{other:?}"),
    }
    // A validator asked directly signs (it enforces the strict policy) ...
    let env = paralean_store::receipt::JobEnvelope {
        request: b"unpinned/direct".to_vec(),
        group: g.decl,
        capsule: g.capsule_id(),
        deps: vec![],
        base: paralean_control::checker::base_id(&c.checker.lean_githash),
        policy: strict_policy().id(),
        checker: c.validators[0].checker_id(),
        worker: w.id(),
        targets: vec![],
        deadline_ms: 120_000,
        memory_mb: 0,
    };
    let j = SignedJob::sign(env, &c.kf.authority_signer().unwrap());
    let resp = paralean_validator_api::validate(&c.vaddrs[0], &j, Duration::from_secs(300)).await.unwrap();
    let paralean_validator_api::ValidatorResponse::Receipt { receipt } = resp else { panic!("{resp:?}") };
    let r = paralean_validator_api::decode_receipt(&receipt).unwrap();
    assert_eq!((r.body.policy, r.body.verdict.clone()), (strict_policy().id(), Verdict::Accepted));
    // ... but no worker stages it and T1 refuses it.
    refused_both_ways(
        &w.writer,
        &w.package(&g, r, j, vec![]),
        |f| *f == GuardFailure::ReceiptBinding(BindingFault::PolicyNotPinned),
        "unpinned policy",
    )
    .await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn receipt_for_another_epoch_fails_closed() {
    let c = Cluster::start("epoch", Opts::default()).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let t = n("F01.uses_small");
    let e0 = c.assign(&t.to_string(), w0.id()).await;
    let pt0 = w0.writer.prepare_target(&t).await.unwrap();
    assert_eq!(pt0.epoch, e0);
    let g = w0.group_declaring(&t).unwrap().clone();
    w0.publish_deps(&g).await.unwrap();
    let stmt = g.statement(&t).unwrap();
    let (r, j) = w0.validate(&g, "epoch/0", &[(t.clone(), stmt.clone())], 0).await.unwrap();
    // Away and back: the record's epoch moves twice; w0 owns it again.
    c.assign(&t.to_string(), w1.id()).await;
    let e2 = c.assign(&t.to_string(), w0.id()).await;
    assert_eq!(e2, e0 + 2);
    let pt2 = w0.writer.prepare_target(&t).await.unwrap();
    // Prepared under the current epoch with a receipt bound to the old one.
    refused_both_ways(
        &w0.writer,
        &w0.package(&g, r.clone(), j.clone(), vec![pt2.clone()]),
        |f| *f == GuardFailure::ReceiptBinding(BindingFault::Epoch),
        "old-epoch receipt",
    )
    .await;
    // Prepared under the old epoch: the receipt matches, the epoch fence refuses.
    let g1 = guard(w0.writer.publish(&w0.package(&g, r, j, vec![pt0])).await);
    assert!(matches!(g1, GuardFailure::StaleEpoch { .. }), "{g1:?}");
    // A receipt for the current epoch publishes.
    let (r2, j2) = w0.validate(&g, "epoch/2", &[(t.clone(), stmt)], 0).await.unwrap();
    assert_eq!(j2.body.targets[0].epoch, e2);
    w0.writer.publish(&w0.package(&g, r2, j2, vec![pt2])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn receipt_for_another_or_cancelled_request_fails_closed() {
    let c = Cluster::start("request", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.small")).unwrap().clone();
    let (r1, j1) = w.validate(&g, "req/1", &[], 0).await.unwrap();
    let (r2, j2) = w.validate(&g, "req/2", &[], 0).await.unwrap();
    assert_ne!(j1.id(), j2.id());
    // Receipt of request 1 with the envelope of request 2.
    refused_both_ways(
        &w.writer,
        &w.package(&g, r1.clone(), j2.clone(), vec![]),
        |f| *f == GuardFailure::ReceiptBinding(BindingFault::Request),
        "other request",
    )
    .await;
    // Request 1 is cancelled after its receipt was issued: T1 reads the cancellation.
    assert_eq!(c.call(ControlRequest::Cancel { request: "req/1".into() }).await, ControlResponse::Cancelled);
    let f = guard(w.writer.publish(&w.package(&g, r1, j1, vec![])).await);
    assert_eq!(f, GuardFailure::JobCancelled(b"req/1".to_vec()));
    assert!(!published(&c.store, &g.decl).await);
    // A cancelled request gets no new receipt either.
    match w.validate(&g, "req/1", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Cancelled)) => {}
        other => panic!("{other:?}"),
    }
    w.writer.publish(&w.package(&g, r2, j2, vec![])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn revoked_or_retired_validator_key_fails_closed() {
    let c = Cluster::start("revoke", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let small = w.group_declaring(&n("F01.small")).unwrap().clone();
    let two = w.group_declaring(&n("F01.two_eq")).unwrap().clone();
    let le = w.group_declaring(&n("F01.le_succ_self")).unwrap().clone();
    let (r, j) = w.validate(&small, "rv/small", &[], 0).await.unwrap();
    let key = r.body.validator_key;
    // A group published, before the revocation, with a receipt by the same key (the
    // controller spreads requests over both validators).
    let mut i = 0;
    let (r0, j0) = loop {
        let (r0, j0) = w.validate(&two, &format!("rv/two-{i}"), &[], 0).await.unwrap();
        if r0.body.validator_key == key {
            break (r0, j0);
        }
        i += 1;
        assert!(i < 6);
    };
    w.writer.publish(&w.package(&two, r0, j0, vec![])).await.unwrap();
    // Revoke that key (R1, signed by the authority).
    let auth = c.kf.authority_signer().unwrap();
    let rev = SignedRevocation::sign(Revocation { key, reason: "test: compromised".into() }, &auth);
    assert!(c.store.meta.revoke_validator(&rev).await.unwrap());
    // Its receipt no longer publishes (the staging check is pure; T1 reads the revocation).
    let f = guard(w.writer.publish(&w.package(&small, r, j, vec![])).await);
    assert_eq!(f, GuardFailure::ValidatorRevoked(key));
    assert!(!published(&c.store, &small.decl).await);
    // The revoked validator refuses new work; the controller moves on to the other one.
    let (r2, j2) = w.validate(&small, "rv/small-2", &[], 0).await.unwrap();
    assert_ne!(r2.body.validator_key, key);
    w.writer.publish(&w.package(&small, r2, j2, vec![])).await.unwrap();
    // The group published before the revocation stays published; the audit marks it suspect
    // and consumers refuse its receipt.
    let a = c.audit_ok().await;
    assert_eq!(a.suspect_receipts, vec![two.decl]);
    assert!(matches!(published_receipt(&c.store, &two.decl).await, Err(PublishedReceiptError::Revoked)));
    // Rotation: a ring that no longer lists the other key (retired) refuses its receipts.
    let (r3, j3) = w.validate(&le, "rv/le", &[], 0).await.unwrap();
    let mut ring = c.kf.ring();
    ring.validators.retain(|k| *k != r3.body.validator_key);
    let retired = w.writer.with_store(c.store_with_ring(ring));
    let p = w.package(&le, r3.clone(), j3.clone(), vec![]);
    let f = guard(retired.publish_skipping_staging_check(&p).await);
    assert!(matches!(f, GuardFailure::ReceiptRejected(_)), "{f:?}");
    w.writer.publish(&p).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn worker_that_skips_validation_cannot_publish() {
    let c = Cluster::start("skip", Opts::default()).await;
    let neg = negative_store(&c.tmp.join("neg"));
    let w = c.worker(0, 8192, &neg).await;
    let mut rejected = 0;
    for (name, _) in [("N1.bad", "sorry"), ("N2.cheat", "axiom"), ("N3.bad", "kernel"), ("N6.bad", "native_decide")] {
        let g = w.group_declaring(&n(name)).unwrap().clone();
        upload(&w.writer, &g).await;
        // The validator re-checks with the stock kernel and refuses to accept.
        let resp = c
            .call(ControlRequest::Validate {
                worker: w.id().hex(),
                request: format!("skip/{name}"),
                group: g.decl.hex(),
                capsule: g.capsule_id().hex(),
                deps: vec![],
                targets: vec![],
                memory_mb: 0,
                deadline_ms: 0,
            })
            .await;
        let ControlResponse::Receipt { receipt, job } = resp else { panic!("{name}: {resp:?}") };
        let r = Receipt::from_bytes(&hex::decode(receipt).unwrap()).unwrap();
        let j = SignedJob::from_bytes(&hex::decode(job).unwrap()).unwrap();
        assert!(matches!(r.body.verdict, Verdict::Rejected(_)), "{name}: {:?}", r.body.verdict);
        rejected += 1;
        // The worker publishes anyway, holding the rejection.
        refused_both_ways(&w.writer, &w.package(&g, r, j, vec![]), |f| matches!(f, GuardFailure::ReceiptNotAccepted(_)), name).await;
    }
    assert_eq!(rejected, 4);
    // N2.bad depends on the unpublished axiom group: the validator refuses outright.
    let g = w.group_declaring(&n("N2.bad")).unwrap().clone();
    match w.validate(&g, "skip/N2.bad", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Refused { reason })) => assert!(reason.contains("dependency"), "{reason}"),
        other => panic!("{other:?}"),
    }
    // A valid group's accepted receipt reused for a bad group.
    let cw = c.worker(1, 8192, &core_store()).await;
    let good = cw.group_declaring(&n("F01.small")).unwrap().clone();
    let (r, j) = cw.validate(&good, "skip/good", &[], 0).await.unwrap();
    let bad = w.group_declaring(&n("N3.bad")).unwrap().clone();
    refused_both_ways(&w.writer, &w.package(&bad, r, j, vec![]), |f| matches!(f, GuardFailure::ReceiptRejected(_)), "borrowed receipt").await;
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn stale_owner_after_lease_expiry_cannot_publish() {
    let c = Cluster::start("stale", Opts { lease_ms: 800, ..Opts::default() }).await;
    let a = c.worker_without_heartbeat(0, 8192, &core_store()).await;
    let b = c.worker(1, 8192, &core_store()).await;
    let ha = a.spawn_heartbeats(Duration::from_millis(200));
    let t = n("F01.uses_small");
    c.call(ControlRequest::SubmitWork { request: "stale/t".into(), target: t.to_string(), memory_mb: 512 }).await;
    let work = a.poll().await.unwrap().expect("a gets the work");
    let pt = a.writer.prepare_target(&t).await.unwrap();
    assert_eq!(pt.epoch, work.epoch);
    let g = a.group_declaring(&t).unwrap().clone();
    a.publish_deps(&g).await.unwrap();
    let stmt = g.statement(&t).unwrap();
    let (r, j) = a.validate(&g, "stale/a", &[(t.clone(), stmt.clone())], 0).await.unwrap();
    // A stops heartbeating (crashed or partitioned) but keeps its receipt.
    ha.abort();
    let deadline = std::time::Instant::now() + Duration::from_secs(10);
    let rec = loop {
        let rec = c.store.target(&t).await.unwrap().unwrap();
        if rec.owner != a.id() {
            break rec;
        }
        assert!(std::time::Instant::now() < deadline, "target was never reassigned");
        tokio::time::sleep(Duration::from_millis(100)).await;
    };
    assert_eq!(rec.owner, b.id());
    assert!(rec.epoch > work.epoch);
    // The stale owner's publication is fenced by the store.
    let f = guard(a.writer.publish(&a.package(&g, r, j, vec![pt])).await);
    assert!(matches!(f, GuardFailure::NotOwner { .. } | GuardFailure::StaleEpoch { .. }), "{f:?}");
    // Re-reading the record: it is no longer the owner.
    assert!(matches!(guard(a.writer.prepare_target(&t).await), GuardFailure::NotOwner { .. }));
    // Back from its partition it re-registers; the controller refuses a target job.
    assert!(matches!(a.register().await.unwrap(), ControlResponse::Registered { .. }));
    let _ha2 = a.spawn_heartbeats(Duration::from_millis(200));
    match a.validate(&g, "stale/a-again", &[(t.clone(), stmt)], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Refused { reason })) => assert!(reason.contains("does not own"), "{reason}"),
        other => panic!("{other:?}"),
    }
    // It asks for a target-free check of the same group and publishes without listing the
    // target: T1 sees the target record and refuses.
    let (r, j) = a.validate(&g, "stale/a-sneak", &[], 0).await.unwrap();
    let p = a.package(&g, r, j, vec![]);
    assert_eq!(guard(a.writer.publish(&p).await), GuardFailure::UndeclaredTarget(t.clone()));
    assert!(!published(&c.store, &g.decl).await);
    // The new owner proves it.
    let wb = b.poll().await.unwrap().expect("b gets the reassigned work");
    assert_eq!(wb.epoch, rec.epoch);
    b.prove(&wb).await.unwrap();
    let rec = c.store.target(&t).await.unwrap().unwrap();
    assert!(rec.head.is_some());
    let rev = c.store.revision(&rec.head.unwrap()).await.unwrap().unwrap();
    assert_eq!(rev.workspace, b.id());
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn dependency_must_be_published_with_a_receipt() {
    let c = Cluster::start("deps", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let g = w.group_declaring(&n("F01.uses_small")).unwrap().clone();
    // F01.small is uploaded but not published: the validator refuses.
    let small = w.group_declaring(&n("F01.small")).unwrap().clone();
    w.writer.store.s3.put_opaque(&small.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&small.capsule_object()).await.unwrap();
    match w.validate(&g, "deps/early", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Refused { reason })) => assert!(reason.contains("dependency"), "{reason}"),
        other => panic!("{other:?}"),
    }
    w.publish_deps(&g).await.unwrap();
    let (r, j) = w.validate(&g, "deps/late", &[], 0).await.unwrap();
    w.writer.publish(&w.package(&g, r, j, vec![])).await.unwrap();
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn validator_enforces_the_envelope_policy() {
    let o = Opts {
        policy: strict_policy(),
        pinned_policies: vec![paralean_store::receipt::Policy::v1(), strict_policy()],
        ..Opts::default()
    };
    let c = Cluster::start("policy", o).await;
    let w = c.worker(0, 8192, &core_store()).await;
    // F06.fib_pos uses Classical.choice (allowed by v1, which P1's own audit applies); the
    // strict policy refuses it.
    let g = w.group_declaring(&n("F06.fib_pos")).unwrap().clone();
    w.publish_deps(&g).await.unwrap();
    match w.validate(&g, "policy/fib_pos", &[], 0).await {
        Err(WorkerError::NoReceipt(ControlResponse::Receipt { receipt, .. })) => {
            let r = Receipt::from_bytes(&hex::decode(receipt).unwrap()).unwrap();
            let Verdict::Rejected(why) = r.body.verdict else { panic!() };
            assert!(why.contains("Classical.choice"), "{why}");
        }
        other => panic!("{other:?}"),
    }
    // A propext-only group is accepted under the same policy.
    let g = w.group_declaring(&n("F02.classify_two")).unwrap().clone();
    w.publish_deps(&g).await.unwrap();
    let (r, j) = w.validate(&g, "policy/classify_two", &[], 0).await.unwrap();
    assert_eq!(r.body.axioms, vec![n("propext")]);
    w.writer.publish(&w.package(&g, r, j, vec![])).await.unwrap();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn changed_target_statement_is_rejected() {
    let c = Cluster::start("statement", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let t = n("F01.uses_small");
    c.assign(&t.to_string(), w.id()).await;
    let g = w.group_declaring(&t).unwrap().clone();
    w.publish_deps(&g).await.unwrap();
    upload(&w.writer, &g).await;
    // The target contract pins another statement hash than the group's.
    let wrong = "00".repeat(32);
    let resp = c
        .call(ControlRequest::Validate {
            worker: w.id().hex(),
            request: "statement/wrong".into(),
            group: g.decl.hex(),
            capsule: g.capsule_id().hex(),
            deps: vec![w.groups[&paralean_control::p1::closure(&w.groups, &g.gid).unwrap()[0]].capsule_id().hex()],
            targets: vec![TargetReq { name: t.to_string(), statement: wrong }],
            memory_mb: 0,
            deadline_ms: 0,
        })
        .await;
    let ControlResponse::Receipt { receipt, .. } = resp else { panic!("{resp:?}") };
    let r = Receipt::from_bytes(&hex::decode(receipt).unwrap()).unwrap();
    assert!(matches!(r.body.verdict, Verdict::Rejected(_)), "{:?}", r.body.verdict);
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn job_issuer_keys_sign_target_free_envelopes_only() {
    let issuer = Signer::derive("p3-issuer-0");
    let c = Cluster::start("issuer", Opts { job_issuers: vec![issuer.clone()], ..Opts::default() }).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let small = w.group_declaring(&n("F01.small")).unwrap().clone();
    upload(&w.writer, &small).await;
    let env = |request: &str, g: &paralean_control::p1::P1Group, deps: Vec<Id>, targets: Vec<TargetBinding>| paralean_store::receipt::JobEnvelope {
        request: request.as_bytes().to_vec(),
        group: g.decl,
        capsule: g.capsule_id(),
        deps,
        base: paralean_control::checker::base_id(&c.checker.lean_githash),
        policy: paralean_store::receipt::Policy::v1().id(),
        checker: c.validators[0].checker_id(),
        worker: w.id(),
        targets,
        deadline_ms: 120_000,
        memory_mb: 0,
    };
    let ask = |j: SignedJob| {
        let addr = c.vaddrs[0].clone();
        async move {
            match paralean_validator_api::validate(&addr, &j, Duration::from_secs(300)).await.unwrap() {
                paralean_validator_api::ValidatorResponse::Receipt { receipt } => Ok(paralean_validator_api::decode_receipt(&receipt).unwrap()),
                other => Err(other),
            }
        }
    };
    // A working copy issues a target-free envelope with its issuer key: the validator
    // checks it and the receipt publishes.
    let j = SignedJob::sign(env("issuer/small", &small, vec![], vec![]), &issuer);
    let r = ask(j.clone()).await.unwrap();
    w.writer.publish(&w.package(&small, r, j, vec![])).await.unwrap();
    // A key that is not a configured issuer: the validator refuses.
    let other = Signer::derive("not-an-issuer");
    let two = w.group_declaring(&n("F01.two_eq")).unwrap().clone();
    upload(&w.writer, &two).await;
    assert!(matches!(ask(SignedJob::sign(env("issuer/two", &two, vec![], vec![]), &other)).await, Err(paralean_validator_api::ValidatorResponse::Refused { .. })));
    // An issuer-signed envelope binding a target (even at the owner's current epoch):
    // validators sign it, but no worker stages it and T1 refuses it.
    let t = n("F01.uses_small");
    let epoch = c.assign(&t.to_string(), w.id()).await;
    let g = w.group_declaring(&t).unwrap().clone();
    upload(&w.writer, &g).await;
    let tb = TargetBinding { name: t.clone(), epoch, statement: hex::decode(g.statement(&t).unwrap()).unwrap() };
    let j = SignedJob::sign(env("issuer/target", &g, vec![small.capsule_id()], vec![tb]), &issuer);
    let r = ask(j.clone()).await.unwrap();
    assert_eq!(r.body.verdict, Verdict::Accepted);
    let pt = w.writer.prepare_target(&t).await.unwrap();
    refused_both_ways(&w.writer, &w.package(&g, r, j, vec![pt]), |f| *f == GuardFailure::ReceiptBinding(BindingFault::JobNotIssued), "issuer-signed target envelope").await;
    c.audit_ok().await;
}
