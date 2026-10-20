//! A command that declares two public names is one target publication: both owner
//! records, epochs, receipt bindings, and heads must agree at the T1 transaction.

mod common;

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
