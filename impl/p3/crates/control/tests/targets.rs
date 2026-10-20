//! A command that declares two public names is one target publication: both owner
//! records, epochs, receipt bindings, and heads must agree at the T1 transaction.

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
            request: deployment("joint-assign"),
        })
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

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
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

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
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

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn joint_assignment_rejects_subset_and_expires_together() {
    let c = Cluster::start("joint-expiry", Opts { lease_ms: 800, ..Opts::default() }).await;
    let old = c.worker_without_heartbeat(0, 8192, &core_store()).await;
    let names = target_names();
    let epochs = assign_group(&c, &names, old.id()).await;
    let response = c.call(ControlRequest::Assign { target: names[0].to_string(),
        worker: c.kf.workspace("w1").unwrap().0.hex() }).await;
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

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn stale_joint_assignment_request_cannot_overwrite_handover() {
    let c = Cluster::start("joint-stale-request", Opts { lease_ms: 800, ..Opts::default() }).await;
    let former = c.kf.workspace("w0").unwrap().0;
    let current = c.worker_without_heartbeat(1, 8192, &core_store()).await;
    let names = target_names();
    let request = |id: &str, owner: WorkspaceId, names: &[Name]| ControlRequest::AssignGroup {
        targets: names.iter().map(ToString::to_string).collect(), worker: owner.hex(), request: id.into(),
    };
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
