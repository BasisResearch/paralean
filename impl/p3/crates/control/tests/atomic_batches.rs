//! Atomic batches (T12; docs/atomic-pub-log.md) validated through the controller's
//! `ValidateBatch` against the live services, with real P1 groups. A batch publishes all its
//! members or none. Attacks on T12 itself use `publish_batch_skipping_staging_check`, so the
//! batch transaction's own per-member checks are what refuse them;
//! impl/p3/scripts/check-mutations.sh removes each check and requires the named test to fail.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::sync::atomic::Ordering;
use std::time::Duration;

use common::*;
use paralean_control::controller::{BatchMemberReq, ControlRequest, ControlResponse, TargetReq};
use paralean_control::p1::{self, P1Group};
use paralean_control::worker::WorkerNode;
use paralean_store::receipt::{JobEnvelope, SignedJob};
use paralean_store::*;
use paralean_validator_api::{rpc, ValidatorRequest, ValidatorResponse};

fn n(s: &str) -> Name {
    Name::parse(s)
}

/// A publication member: `g` by `w`, its dependency closure as job dependencies. Uploads
/// the payloads first, as `WorkerNode::validate` does.
async fn publication(w: &WorkerNode, g: &P1Group, request: &str, targets: &[(Name, String)]) -> BatchMemberReq {
    w.writer.store.s3.put_opaque(&g.group_object()).await.unwrap();
    w.writer.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    let order = p1::closure(&w.groups, &g.gid).unwrap();
    BatchMemberReq::Publish {
        worker: w.id().hex(),
        request: request.into(),
        group: g.decl.hex(),
        capsule: g.capsule_id().hex(),
        deps: order[..order.len() - 1].iter().map(|gid| w.groups[gid].capsule_id().hex()).collect(),
        targets: targets.iter().map(|(t, s)| TargetReq { name: t.to_string(), statement: s.clone() }).collect(),
    }
}

/// The controller's answer to a batch validation: the intent and, per publication member,
/// its receipt and envelope.
struct Validated {
    intent: SignedBatch,
    receipts: Vec<Receipt>,
    jobs: Vec<SignedJob>,
}

fn decode(resp: ControlResponse) -> Validated {
    let ControlResponse::BatchReceipts { intent, receipts, jobs } = resp else { panic!("batch validation: {resp:?}") };
    Validated {
        intent: SignedBatch::from_bytes(&hex::decode(intent).unwrap()).unwrap(),
        receipts: receipts.iter().map(|r| Receipt::from_bytes(&hex::decode(r).unwrap()).unwrap()).collect(),
        jobs: jobs.iter().map(|j| SignedJob::from_bytes(&hex::decode(j).unwrap()).unwrap()).collect(),
    }
}

fn validate_batch(coordinator: &WorkerNode, request: &str, members: Vec<BatchMemberReq>) -> ControlRequest {
    ControlRequest::ValidateBatch { coordinator: coordinator.id().hex(), request: request.into(), members }
}

/// A publication item with its own writer's certificate.
fn item(w: &WorkerNode, package: Package) -> BatchItem {
    BatchItem::Publish { cert: w.writer.sign_batch_publication(&package), writer: w.id(), package }
}

/// Nothing of the batch is visible: no member marker, no batch record.
async fn assert_none(store: &Store, groups: &[Id], intent: &SignedBatch, what: &str) {
    for g in groups {
        assert!(!published(store, g).await, "{what}: a member of a refused batch is published");
    }
    assert!(store.batch(&intent.id()).await.unwrap().is_none(), "{what}: batch record");
}

/// Both the worker-side staging check and T12 refuse `b` with `want`; nothing is published.
async fn refused_both_ways(store: &Store, b: &BatchPackage, groups: &[Id], want: impl Fn(&GuardFailure) -> bool, what: &str) {
    let g1 = guard(store.publish_batch(b).await);
    assert!(want(&g1), "{what}: staging check gave {g1:?}");
    let g2 = guard(store.publish_batch_skipping_staging_check(b).await);
    assert!(want(&g2), "{what}: T12 gave {g2:?}");
    assert_none(store, groups, &b.intent, what).await;
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn batch_of_dependent_groups_by_two_workspaces_publishes_all_members() {
    let c = Cluster::start("batch-all", Opts::default()).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let small = w0.group_declaring(&n("F01.small")).unwrap().clone();
    let uses = w1.group_declaring(&n("F01.uses_small")).unwrap().clone();
    let two = w0.group_declaring(&n("F01.two_eq")).unwrap().clone();
    assert_eq!(p1::closure(&w1.groups, &uses.gid).unwrap(), vec![small.gid.clone(), uses.gid.clone()]);
    // w0 published two_eq earlier; the batch deletes it.
    let (r, j) = w0.validate(&two, "all/two", &[], 0).await.unwrap();
    let old = w0.package(&two, r, j, vec![]);
    w0.writer.publish(&old).await.unwrap();
    // w1 owns the target F01.uses_small, whose proof depends on w0's small in the same batch.
    let t = n("F01.uses_small");
    c.assign(&t.to_string(), w1.id()).await;
    let pt = w1.writer.prepare_target(&t).await.unwrap();
    let members = vec![
        publication(&w0, &small, "all/small", &[]).await,
        publication(&w1, &uses, "all/uses", &[(t.clone(), uses.statement(&t).unwrap())]).await,
        BatchMemberReq::Tombstone { worker: w0.id().hex(), target: two.decl.hex(), position: old.marker.id().hex() },
    ];
    // Only a registered coordinator, within the bounds.
    let w2 = c.writer(2).id;
    let unregistered = ControlRequest::ValidateBatch { coordinator: w2.hex(), request: "all".into(), members: members.clone() };
    assert!(matches!(c.call(unregistered).await, ControlResponse::Refused { reason } if reason.contains("not registered")));
    let many = vec![members[0].clone(); MAX_BATCH_MEMBERS + 1];
    assert!(matches!(c.call(validate_batch(&w0, "all/many", many)).await, ControlResponse::Refused { .. }));
    let mut long = members.clone();
    let BatchMemberReq::Publish { request, .. } = &mut long[0] else { unreachable!() };
    *request = "x".repeat(paralean_control::controller::MAX_REQUEST_ID + 1);
    assert!(matches!(c.call(validate_batch(&w0, "all/long", long)).await, ControlResponse::Refused { reason } if reason.contains("longer")));

    let resp = c.call(validate_batch(&w0, "all", members.clone())).await;
    let v = decode(resp.clone());
    let id = v.intent.id();
    assert!(v.intent.issued_by_controller(&c.store.ring));
    assert_eq!(v.intent.body.members, vec![
        BatchMember::Publish { group: small.decl, writer: w0.id() },
        BatchMember::Publish { group: uses.decl, writer: w1.id() },
        BatchMember::Tombstone { target: two.decl, position: Some(old.marker.id()), writer: w0.id() },
    ]);
    assert_eq!(v.receipts.len(), 2);
    for (r, j) in v.receipts.iter().zip(&v.jobs) {
        assert_eq!(r.body.verdict, Verdict::Accepted);
        assert_eq!(j.body.batch, Some(id));
    }
    assert_eq!((v.jobs[1].body.worker, v.jobs[1].body.targets[0].epoch), (w1.id(), pt.epoch));
    // A retry gets the recorded receipts without another check.
    let checks: u64 = c.validators.iter().map(|v| v.checks_run.load(Ordering::SeqCst)).sum();
    assert_eq!(c.call(validate_batch(&w0, "all", members)).await, resp);
    assert_eq!(c.validators.iter().map(|v| v.checks_run.load(Ordering::SeqCst)).sum::<u64>(), checks);

    let p0 = w0.package(&small, v.receipts[0].clone(), v.jobs[0].clone(), vec![]);
    let p1 = w1.package(&uses, v.receipts[1].clone(), v.jobs[1].clone(), vec![pt]);
    // A bound member cannot be published alone.
    assert_eq!(guard(w0.writer.publish(&p0).await), GuardFailure::BatchBinding(small.decl));
    let tomb = Tombstone {
        file_path: old.marker.file_path.clone(), target: two.decl, lamport: old.marker.lamport + 100,
        author: old.marker.author, receipt: None, position: Some(old.marker.id()), batch: Some(id),
    };
    let b = BatchPackage { intent: v.intent.clone(), items: vec![
        item(&w0, p0),
        item(&w1, p1.clone()),
        BatchItem::Tombstone { cert: w0.writer.sign_batch_tombstone(&tomb), tombstone: tomb.clone(), writer: w0.id(), grant: None },
    ] };
    assert!(c.store.publish_batch(&b).await.unwrap().fresh);
    for g in [small.decl, uses.decl] {
        assert!(published(&c.store, &g).await, "a member of the committed batch is not published");
    }
    assert!(c.store.tombstone(&tomb.id()).await.unwrap().is_some());
    assert_eq!(c.store.batch(&id).await.unwrap().expect("batch record").entries.len(), 3);
    assert_eq!(c.store.target(&t).await.unwrap().unwrap().head, Some(p1.revisions[0].id()));
    c.audit_ok().await;
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn stale_owner_on_one_member_rejects_the_whole_batch() {
    let c = Cluster::start("batch-stale", Opts::default()).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let small = w0.group_declaring(&n("F01.small")).unwrap().clone();
    let uses = w1.group_declaring(&n("F01.uses_small")).unwrap().clone();
    let t = n("F01.uses_small");
    let stmt = uses.statement(&t).unwrap();
    c.assign(&t.to_string(), w1.id()).await;
    let pt = w1.writer.prepare_target(&t).await.unwrap();
    let members = vec![
        publication(&w0, &small, "stale/small", &[]).await,
        publication(&w1, &uses, "stale/uses", &[(t.clone(), stmt.clone())]).await,
    ];
    let v = decode(c.call(validate_batch(&w0, "stale", members)).await);
    // The target moves to w0 between validation and publication.
    c.assign(&t.to_string(), w0.id()).await;
    let b = BatchPackage { intent: v.intent.clone(), items: vec![
        item(&w0, w0.package(&small, v.receipts[0].clone(), v.jobs[0].clone(), vec![])),
        item(&w1, w1.package(&uses, v.receipts[1].clone(), v.jobs[1].clone(), vec![pt])),
    ] };
    let f = guard(c.store.publish_batch(&b).await);
    assert!(matches!(f, GuardFailure::NotOwner { .. } | GuardFailure::StaleEpoch { .. }), "{f:?}");
    // The other member, valid alone, is not published either.
    assert_none(&c.store, &[small.decl, uses.decl], &v.intent, "stale owner").await;
    assert!(c.store.target(&t).await.unwrap().unwrap().head.is_none());
    // The controller binds no target its member's worker does not own.
    let again = vec![
        publication(&w0, &small, "stale/small-2", &[]).await,
        publication(&w1, &uses, "stale/uses-2", &[(t.clone(), stmt)]).await,
    ];
    match c.call(validate_batch(&w0, "stale-2", again)).await {
        ControlResponse::Refused { reason } => assert!(reason.contains("does not own"), "{reason}"),
        other => panic!("{other:?}"),
    }
    c.audit_ok().await;
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn forged_rejected_or_misbound_batch_member_receipts_fail_closed() {
    let c = Cluster::start("batch-forged", Opts::default()).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let small = w0.group_declaring(&n("F01.small")).unwrap().clone();
    let uses = w1.group_declaring(&n("F01.uses_small")).unwrap().clone();
    let members = vec![
        publication(&w0, &small, "forged/small", &[]).await,
        publication(&w1, &uses, "forged/uses", &[]).await,
    ];
    let v = decode(c.call(validate_batch(&w0, "forged", members)).await);
    let (r, j) = (v.receipts[0].clone(), v.jobs[0].clone());
    let groups = [small.decl, uses.decl];
    let auth = c.kf.authority_signer().unwrap();
    let rogue = Signer::derive("rogue");
    // The first member's receipt and envelope replaced; the second member unchanged.
    let batch = |r: Receipt, j: SignedJob| BatchPackage { intent: v.intent.clone(), items: vec![
        item(&w0, w0.package(&small, r, j, vec![])),
        item(&w1, w1.package(&uses, v.receipts[1].clone(), v.jobs[1].clone(), vec![])),
    ] };
    // (a) Signed by a key outside the validator set, naming that key.
    let mut body = r.body.clone();
    body.validator_key = rogue.public();
    let forged = Receipt::sign(body, &rogue);
    refused_both_ways(&c.store, &batch(forged, j.clone()), &groups, |f| matches!(f, GuardFailure::ReceiptRejected(_)), "rogue key").await;
    // (b) A rejection, signed by a configured validator.
    let mut body = r.body.clone();
    body.validator_key = c.vsigners[0].public();
    body.verdict = Verdict::Rejected("test: rejected".into());
    let rejected = Receipt::sign(body, &c.vsigners[0]);
    refused_both_ways(&c.store, &batch(rejected, j.clone()), &groups, |f| matches!(f, GuardFailure::ReceiptNotAccepted(_)), "rejected").await;
    // (c) The other member's receipt and envelope.
    refused_both_ways(&c.store, &batch(v.receipts[1].clone(), v.jobs[1].clone()), &groups,
        |f| matches!(f, GuardFailure::ReceiptRejected(_)), "other group").await;
    // (d) A genuine receipt with another envelope of the same group and batch.
    let mut env = j.body.clone();
    env.request = b"forged/other-envelope".to_vec();
    refused_both_ways(&c.store, &batch(r.clone(), SignedJob::sign(env, &auth)), &groups,
        |f| *f == GuardFailure::ReceiptBinding(BindingFault::Request), "other envelope").await;
    // (e) A receipt for an envelope of no batch (a validator signs whatever it checked).
    let mut env = j.body.clone();
    env.batch = None;
    let unbound = SignedJob::sign(env, &auth);
    let rc = paralean_store::fixture::receipt_for(&unbound, &c.vsigners[0], Verdict::Accepted);
    refused_both_ways(&c.store, &batch(rc, unbound), &groups, |f| *f == GuardFailure::BatchBinding(small.decl), "unbound envelope").await;
    // The genuine batch publishes.
    c.store.publish_batch(&batch(r, j)).await.unwrap();
    for g in groups {
        assert!(published(&c.store, &g).await);
    }
    c.audit_ok().await;
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn batch_member_receipt_for_another_epoch_fails_closed() {
    let c = Cluster::start("batch-epoch", Opts::default()).await;
    let w0 = c.worker(0, 8192, &core_store()).await;
    let w1 = c.worker(1, 8192, &core_store()).await;
    let small = w0.group_declaring(&n("F01.small")).unwrap().clone();
    let uses = w1.group_declaring(&n("F01.uses_small")).unwrap().clone();
    let t = n("F01.uses_small");
    let stmt = uses.statement(&t).unwrap();
    let e0 = c.assign(&t.to_string(), w1.id()).await;
    let pt0 = w1.writer.prepare_target(&t).await.unwrap();
    let members = |tag: &'static str| {
        let (w0, w1, small, uses, t, stmt) = (&w0, &w1, &small, &uses, t.clone(), stmt.clone());
        async move {
            vec![
                publication(w0, small, &format!("{tag}/small"), &[]).await,
                publication(w1, uses, &format!("{tag}/uses"), &[(t, stmt)]).await,
            ]
        }
    };
    let v = decode(c.call(validate_batch(&w0, "epoch/0", members("epoch/0").await)).await);
    assert_eq!(v.jobs[1].body.targets[0].epoch, e0);
    // Away and back: the record's epoch moves twice; w1 owns it again.
    c.assign(&t.to_string(), w0.id()).await;
    assert_eq!(c.assign(&t.to_string(), w1.id()).await, e0 + 2);
    let pt2 = w1.writer.prepare_target(&t).await.unwrap();
    let groups = [small.decl, uses.decl];
    let batch = |v: &Validated, pt: PreparedTarget| BatchPackage { intent: v.intent.clone(), items: vec![
        item(&w0, w0.package(&small, v.receipts[0].clone(), v.jobs[0].clone(), vec![])),
        item(&w1, w1.package(&uses, v.receipts[1].clone(), v.jobs[1].clone(), vec![pt])),
    ] };
    // Prepared under the current epoch with a receipt bound to the old one.
    refused_both_ways(&c.store, &batch(&v, pt2.clone()), &groups,
        |f| *f == GuardFailure::ReceiptBinding(BindingFault::Epoch), "old-epoch receipt").await;
    // Prepared under the old epoch: the receipt matches, T12's epoch fence refuses.
    let f = guard(c.store.publish_batch(&batch(&v, pt0)).await);
    assert!(matches!(f, GuardFailure::StaleEpoch { .. }), "{f:?}");
    assert_none(&c.store, &groups, &v.intent, "old epoch").await;
    // A batch validated under the current epoch publishes.
    let v2 = decode(c.call(validate_batch(&w0, "epoch/2", members("epoch/2").await)).await);
    assert_eq!(v2.jobs[1].body.targets[0].epoch, e0 + 2);
    c.store.publish_batch(&batch(&v2, pt2)).await.unwrap();
    assert!(published(&c.store, &uses.decl).await);
    c.audit_ok().await;
}

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn job_of_another_batch_cannot_serve_as_a_batch_dependency() {
    let c = Cluster::start("batch-cross", Opts { validators: vec![Mode::Real], ..Opts::default() }).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let small = w.group_declaring(&n("F01.small")).unwrap().clone();
    let uses = w.group_declaring(&n("F01.uses_small")).unwrap().clone();
    for g in [&small, &uses] {
        c.store.s3.put_opaque(&g.group_object()).await.unwrap();
        c.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    }
    let auth = c.kf.authority_signer().unwrap();
    let job = |g: &P1Group, deps: Vec<Id>, request: &str, batch: Option<Id>| SignedJob::sign(JobEnvelope {
        request: request.as_bytes().to_vec(), group: g.decl, capsule: g.capsule_id(), deps,
        base: paralean_control::checker::base_id(&c.checker.lean_githash), policy: paralean_store::receipt::Policy::v1().id(),
        checker: c.validators[0].checker_id(), worker: w.id(), targets: vec![], deadline_ms: 120_000, memory_mb: 0, batch,
    }, &auth);
    let ask = |jobs: Vec<SignedJob>| {
        let (addr, auth, key) = (c.vaddrs[0].clone(), auth.clone(), c.vsigners[0].public());
        async move {
            let req = ValidatorRequest::ValidateBatch { jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect() };
            match rpc::call_authenticated(&addr, &req, &auth, &key, Duration::from_secs(300)).await.unwrap() {
                ValidatorResponse::Batch { responses } => responses,
                other => panic!("{other:?}"),
            }
        }
    };
    let accepted = |r: &ValidatorResponse| matches!(r, ValidatorResponse::Receipt { receipt }
        if paralean_validator_api::decode_receipt(receipt).unwrap().body.verdict == Verdict::Accepted);
    let (a, b) = (Some(Id([0xa; 32])), Some(Id([0xb; 32])));
    let deps = vec![small.capsule_id()];
    // The dependency's job is bound to batch A, or to none; the dependent's to batch B.
    for (tag, bound) in [("a", a), ("none", None)] {
        let r = ask(vec![job(&small, vec![], &format!("cross/{tag}/small"), bound), job(&uses, deps.clone(), &format!("cross/{tag}/uses"), b)]).await;
        assert!(accepted(&r[0]), "{tag}: {r:?}");
        assert!(matches!(&r[1], ValidatorResponse::Refused { reason } if reason.contains("dependency")),
            "{tag}: a receipt of another batch served as a dependency: {r:?}");
    }
    // Within one batch it serves.
    let r = ask(vec![job(&small, vec![], "cross/b/small", b), job(&uses, deps, "cross/b/uses", b)]).await;
    assert!(r.iter().all(accepted), "{r:?}");
    assert!(!published(&c.store, &uses.decl).await);
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("batch_of_dependent_groups_by_two_workspaces_publishes_all_members", || { batch_of_dependent_groups_by_two_workspaces_publishes_all_members(); Ok(()) }),
        libtest_mimic::Trial::test("stale_owner_on_one_member_rejects_the_whole_batch", || { stale_owner_on_one_member_rejects_the_whole_batch(); Ok(()) }),
        libtest_mimic::Trial::test("forged_rejected_or_misbound_batch_member_receipts_fail_closed", || { forged_rejected_or_misbound_batch_member_receipts_fail_closed(); Ok(()) }),
        libtest_mimic::Trial::test("batch_member_receipt_for_another_epoch_fails_closed", || { batch_member_receipt_for_another_epoch_fails_closed(); Ok(()) }),
        libtest_mimic::Trial::test("job_of_another_batch_cannot_serve_as_a_batch_dependency", || { job_of_another_batch_cannot_serve_as_a_batch_dependency(); Ok(()) }),
    ]);
}
