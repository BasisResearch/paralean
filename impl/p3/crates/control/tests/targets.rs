//! A command that declares two public names is one target publication: both owner
//! records, epochs, receipt bindings, and heads must agree at the T1 transaction.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::time::Duration;

use common::*;
use paralean_control::controller::{ControlRequest, ControlResponse};
use paralean_store::*;

fn target_names() -> [Name; 2] {
    [Name::parse("F05.Even"), Name::parse("F05.Odd")]
}

async fn assign_group(c: &Cluster, names: &[Name; 2], owner: WorkspaceId) -> Vec<u64> {
    let response = c
        .call(ControlRequest::AssignGroup {
            targets: names.iter().map(ToString::to_string).collect(),
            worker: owner.hex(),
            request: deployment("joint-assign"), statements: vec![] })
        .await;
    let ControlResponse::AssignedGroup { epochs } = response else {
        panic!("joint target assignment: {response:?}")
    };
    assert_eq!(epochs.len(), names.len());
    for (name, epoch) in names.iter().zip(&epochs) {
        let record = c.store.target(name).await.unwrap().unwrap();
        assert_eq!((record.owner, record.epoch), (owner, *epoch));
    }
    epochs
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn two_names_in_one_group_publish_with_one_bound_receipt() {
    let c = Cluster::start("two-targets", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let names = target_names();
    let g = w.group_declaring(&names[0]).unwrap().clone();
    assert!(
        names.iter().all(|name| g.names().contains(name)),
        "fixture must declare both names in one group"
    );
    let epochs = assign_group(&c, &names, w.id()).await;
    let prepared = futures_prepare(&w.writer, &names).await;
    w.publish_deps(&g).await.unwrap();
    let statements = names
        .iter()
        .map(|name| (name.clone(), g.statement(name).unwrap()))
        .collect::<Vec<_>>();
    let (receipt, job) = w
        .validate(&g, "two-targets/1", &statements, 0)
        .await
        .unwrap();
    assert_eq!(job.body.targets.len(), 2);
    for (name, epoch) in names.iter().zip(epochs) {
        assert!(job
            .body
            .targets
            .iter()
            .any(|binding| binding.name == *name && binding.epoch == epoch));
    }
    let pkg = w.package(&g, receipt, job, prepared);
    let outcome = w.writer.publish(&pkg).await.unwrap();
    assert!(outcome.fresh);
    for name in &names {
        let revision = pkg.revisions.iter().find(|rev| &rev.name == name).unwrap();
        assert_eq!(
            c.store.target(name).await.unwrap().unwrap().head,
            Some(revision.id())
        );
    }
    c.audit_ok().await;
}

async fn futures_prepare(writer: &Writer, names: &[Name; 2]) -> Vec<PreparedTarget> {
    let mut result = Vec::new();
    for name in names {
        result.push(writer.prepare_target(name).await.unwrap());
    }
    result
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn pending_two_name_proof_is_fenced_on_handover() {
    let c = Cluster::start("two-target-handover", Opts::default()).await;
    let old = c.worker(0, 8192, &core_store()).await;
    let new = c.worker(1, 8192, &core_store()).await;
    let names = target_names();
    let g = old.group_declaring(&names[0]).unwrap().clone();
    assign_group(&c, &names, old.id()).await;
    let prepared = futures_prepare(&old.writer, &names).await;
    old.publish_deps(&g).await.unwrap();
    let statements = names
        .iter()
        .map(|name| (name.clone(), g.statement(name).unwrap()))
        .collect::<Vec<_>>();
    let (receipt, job) = old
        .validate(&g, "two-targets/pending", &statements, 0)
        .await
        .unwrap();
    let new_epochs = assign_group(&c, &names, new.id()).await;
    let rejected = guard(
        old.writer
            .publish(&old.package(&g, receipt, job, prepared))
            .await,
    );
    assert!(
        matches!(
            rejected,
            GuardFailure::NotOwner { .. } | GuardFailure::StaleEpoch { .. }
        ),
        "{rejected:?}"
    );
    for name in &names {
        assert_eq!(c.store.target(name).await.unwrap().unwrap().head, None);
    }
    let fresh = futures_prepare(&new.writer, &names).await;
    let (receipt, job) = new
        .validate(&g, "two-targets/new-owner", &statements, 0)
        .await
        .unwrap();
    assert_eq!(
        job.body
            .targets
            .iter()
            .map(|binding| binding.epoch)
            .collect::<Vec<_>>(),
        new_epochs
    );
    let pkg = new.package(&g, receipt, job, fresh);
    new.writer.publish(&pkg).await.unwrap();
    for name in &names {
        let record = c.store.target(name).await.unwrap().unwrap();
        let revision = pkg.revisions.iter().find(|rev| &rev.name == name).unwrap();
        assert_eq!((record.owner, record.head), (new.id(), Some(revision.id())));
    }
    c.audit_ok().await;
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn joint_assignment_rejects_subset_and_expires_together() {
    let c = Cluster::start("joint-expiry", Opts { lease_ms: 800, ..Opts::default() }).await;
    let old = c.worker_without_heartbeat(0, 8192, &core_store()).await;
    let names = target_names();
    let epochs = assign_group(&c, &names, old.id()).await;
    let response = c.call(ControlRequest::Assign { target: names[0].to_string(),
        worker: c.kf.workspace("w1").unwrap().0.hex(), statement: String::new() }).await;
    assert!(matches!(response, ControlResponse::Refused { .. }), "partial handover: {response:?}");
    for (name, epoch) in names.iter().zip(&epochs) {
        let record = c.store.target(name).await.unwrap().unwrap();
        assert_eq!((record.owner, record.epoch), (old.id(), *epoch));
    }

    let deadline = std::time::Instant::now() + Duration::from_secs(8);
    loop {
        let records = [c.store.target(&names[0]).await.unwrap().unwrap(),
            c.store.target(&names[1]).await.unwrap().unwrap()];
        if records[0].owner != old.id() && records[1].owner != old.id() {
            assert_eq!(records[0].owner, records[1].owner);
            assert_eq!(records[0].epoch, epochs[0] + 1);
            assert_eq!(records[1].epoch, epochs[1] + 1);
            break;
        }
        assert!(std::time::Instant::now() < deadline, "joint lease expiry did not reassign both names");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn stale_joint_assignment_request_cannot_overwrite_handover() {
    let c = Cluster::start("joint-stale-request", Opts { lease_ms: 800, ..Opts::default() }).await;
    let former = c.kf.workspace("w0").unwrap().0;
    let current = c.worker_without_heartbeat(1, 8192, &core_store()).await;
    let names = target_names();
    let request = |id: &str, owner: WorkspaceId, names: &[Name]| ControlRequest::AssignGroup {
        targets: names.iter().map(ToString::to_string).collect(), worker: owner.hex(), request: id.into(), statements: vec![] };
    assert!(matches!(c.call(request("joint/r1", former, &names)).await, ControlResponse::AssignedGroup { .. }));
    let ControlResponse::AssignedGroup { epochs } = c.call(request("joint/r2", current.id(), &names)).await else {
        panic!("handover failed")
    };
    assert!(matches!(c.call(request("joint/r1", former, &names)).await, ControlResponse::Refused { .. }));
    assert!(matches!(c.call(request("joint/r1", current.id(), &names)).await, ControlResponse::Refused { .. }));
    assert!(matches!(c.call(request("joint/r1", former, &[Name::parse("Other.name")])).await,
        ControlResponse::Refused { .. }));
    for (name, epoch) in names.iter().zip(&epochs) {
        let record = c.store.target(name).await.unwrap().unwrap();
        assert_eq!((record.owner, record.epoch), (current.id(), *epoch));
    }
    let snapshot = paralean_control::durable::Durable::new(c.store.clone(), Duration::from_millis(800))
        .load().await.unwrap().unwrap();
    let state: serde_json::Value = serde_json::from_slice(&snapshot).unwrap();
    let group = state["groups"].as_array().unwrap().iter()
        .find(|g| g["names"].as_array().is_some_and(|ns| ns.len() == 2)).unwrap();
    assert_eq!(group["request"], "joint/r2");
    assert_eq!(group["owner"], current.id().hex());

    let deadline = std::time::Instant::now() + Duration::from_secs(8);
    loop {
        let records = [c.store.target(&names[0]).await.unwrap().unwrap(),
            c.store.target(&names[1]).await.unwrap().unwrap()];
        if records[0].owner != current.id() {
            assert_eq!(records[0].owner, records[1].owner);
            assert_eq!(records[0].epoch, epochs[0] + 1);
            assert_eq!(records[1].epoch, epochs[1] + 1);
            break;
        }
        assert!(std::time::Instant::now() < deadline, "latest joint assignment did not expire together");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn singleton_group_and_work_apis_reject_overlaps_before_target_mutation() {
    let c = Cluster::start("target-api-overlap", Opts { lease_ms: 3000, ..Opts::default() }).await;
    let old = c.worker_without_heartbeat(0, 8192, &core_store()).await;
    let live = c.worker(1, 8192, &core_store()).await;
    let group_name = Name::parse("Overlap.group");
    let work_name = Name::parse("Overlap.work");
    let assigned = c.call(ControlRequest::AssignGroup {
        targets: vec![group_name.to_string()], worker: old.id().hex(),
        request: "overlap/singleton-group".into(), statements: vec![] }).await;
    assert!(matches!(assigned, ControlResponse::AssignedGroup { .. }), "{assigned:?}");
    let before_group = c.store.target(&group_name).await.unwrap().unwrap();

    let legacy = c.call(ControlRequest::Assign {
        target: group_name.to_string(), worker: live.id().hex(), statement: String::new() }).await;
    assert!(matches!(legacy, ControlResponse::Refused { .. }), "singleton group crossed Assign: {legacy:?}");
    let submit = c.call(ControlRequest::SubmitWork {
        request: "overlap/submit-group".into(), target: group_name.to_string(), memory_mb: 64,
    }).await;
    assert!(matches!(submit, ControlResponse::Refused { .. }), "singleton group crossed SubmitWork: {submit:?}");
    let after_group = c.store.target(&group_name).await.unwrap().unwrap();
    assert_eq!((after_group.owner, after_group.epoch, after_group.head),
        (before_group.owner, before_group.epoch, before_group.head));

    assert_eq!(c.call(ControlRequest::SubmitWork {
        request: "overlap/work".into(), target: work_name.to_string(), memory_mb: 64,
    }).await, ControlResponse::Queued);
    let queued_group = c.call(ControlRequest::AssignGroup {
        targets: vec![work_name.to_string()], worker: old.id().hex(),
        request: "overlap/group-while-queued".into(), statements: vec![] }).await;
    assert!(matches!(queued_group, ControlResponse::Refused { .. }),
        "queued work crossed AssignGroup: {queued_group:?}");
    let queued_legacy = c.call(ControlRequest::Assign {
        target: work_name.to_string(), worker: old.id().hex(), statement: String::new() }).await;
    assert!(matches!(queued_legacy, ControlResponse::Refused { .. }),
        "queued work crossed Assign: {queued_legacy:?}");
    assert!(c.store.target(&work_name).await.unwrap().is_none(), "queued-work rejection changed target");
    let polled = c.call(ControlRequest::Poll { worker: live.id().hex() }).await;
    assert!(matches!(&polled, ControlResponse::Work { request, .. } if request == "overlap/work"), "{polled:?}");
    let before_work = c.store.target(&work_name).await.unwrap().unwrap();
    let running_group = c.call(ControlRequest::AssignGroup {
        targets: vec![work_name.to_string()], worker: old.id().hex(),
        request: "overlap/group-while-running".into(), statements: vec![] }).await;
    assert!(matches!(running_group, ControlResponse::Refused { .. }),
        "running work crossed AssignGroup: {running_group:?}");
    let running_legacy = c.call(ControlRequest::Assign {
        target: work_name.to_string(), worker: old.id().hex(), statement: String::new() }).await;
    assert!(matches!(running_legacy, ControlResponse::Refused { .. }),
        "running work crossed Assign: {running_legacy:?}");
    let after_work = c.store.target(&work_name).await.unwrap().unwrap();
    assert_eq!((after_work.owner, after_work.epoch, after_work.head),
        (before_work.owner, before_work.epoch, before_work.head));

    let deadline = std::time::Instant::now() + Duration::from_secs(8);
    loop {
        let group = c.store.target(&group_name).await.unwrap().unwrap();
        if group.owner != old.id() { break }
        assert!(std::time::Instant::now() < deadline, "old group owner did not expire");
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    let work = c.store.target(&work_name).await.unwrap().unwrap();
    assert_eq!((work.owner, work.epoch, work.head),
        (before_work.owner, before_work.epoch, before_work.head),
        "old group owner's expiry fenced live work owner");
}

/// W2 A-4: assignment pins the target's statement, a later assignment cannot replace it,
/// and the controller stamps the pinned statement into the job whatever the worker asks.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn assignment_pins_the_statement_the_controller_stamps() {
    let c = Cluster::start("pinned-statement", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let name = Name::parse("F01.two_eq");
    let g = w.group_declaring(&name).unwrap().clone();
    let pinned = g.statement(&name).unwrap();
    let wrong = "ab".repeat(32);
    assert_ne!(pinned, wrong);
    let r = c.call(ControlRequest::Assign { target: name.to_string(), worker: w.id().hex(), statement: pinned.clone() }).await;
    assert!(matches!(r, ControlResponse::Assigned { .. }), "{r:?}");
    assert_eq!(c.store.meta.target_statement(&name).await.unwrap(), Some(hex::decode(&pinned).unwrap()));
    let r = c.call(ControlRequest::Assign { target: name.to_string(), worker: w.id().hex(), statement: wrong.clone() }).await;
    assert!(matches!(r, ControlResponse::Refused { .. }), "pin replaced: {r:?}");
    w.publish_deps(&g).await.unwrap();
    let (_, job) = w.validate(&g, "pinned-statement/1", &[(name.clone(), wrong)], 0).await.unwrap();
    assert_eq!(job.body.targets[0].statement, hex::decode(&pinned).unwrap());
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("two_names_in_one_group_publish_with_one_bound_receipt", || { two_names_in_one_group_publish_with_one_bound_receipt(); Ok(()) }),
        libtest_mimic::Trial::test("pending_two_name_proof_is_fenced_on_handover", || { pending_two_name_proof_is_fenced_on_handover(); Ok(()) }),
        libtest_mimic::Trial::test("joint_assignment_rejects_subset_and_expires_together", || { joint_assignment_rejects_subset_and_expires_together(); Ok(()) }),
        libtest_mimic::Trial::test("stale_joint_assignment_request_cannot_overwrite_handover", || { stale_joint_assignment_request_cannot_overwrite_handover(); Ok(()) }),
        libtest_mimic::Trial::test("singleton_group_and_work_apis_reject_overlaps_before_target_mutation", || { singleton_group_and_work_apis_reject_overlaps_before_target_mutation(); Ok(()) }),
        libtest_mimic::Trial::test("assignment_pins_the_statement_the_controller_stamps", || { assignment_pins_the_statement_the_controller_stamps(); Ok(()) }),
    ]);
}
