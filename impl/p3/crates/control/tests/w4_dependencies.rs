//! Cross-shard publication through the unchanged authoritative P2 dependency fence.
mod common;
use std::time::Duration;
use paralean_control::durable::Durable;
use paralean_store::*;
use paralean_store::receipt::SignedJob;

fn rebind(package: &mut Package, validator: &Signer) {
    package.job = SignedJob::sign(package.job.body.clone(), &fixture::authority());
    package.receipt = fixture::receipt_for(&package.job, validator, Verdict::Accepted);
    package.marker.receipt = package.receipt.id();
    package.marker.revisions = package.revisions.iter().map(Revision::id).collect();
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn dependency_across_shards_remains_required_after_handover() {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&common::deployment("w4-dependencies")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let (workspace, signer) = keys.workspace("w0").unwrap();
    let writer = Writer::new(store.clone(), workspace, signer);
    let validator = keys.validator_signer("v0").unwrap();
    let a = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 2);
    let b = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let aterm = a.acquire_or_renew().await.unwrap().unwrap().term;
    let bterm = b.acquire_or_renew().await.unwrap().unwrap().term;
    let base_name = Name::parse("W4.base");
    let dependent_name = Name::parse("W4.dependent");
    a.assign_group(&[base_name.clone()], workspace, b"base", aterm).await.unwrap();
    b.assign_group(&[dependent_name.clone()], workspace, b"dependent", bterm).await.unwrap();
    assert_eq!(a.shard_for_target(&base_name).await.unwrap(), 0);
    assert_eq!(a.shard_for_target(&dependent_name).await.unwrap(), 1);
    let mut base = fixture::package("w4/base", workspace, &validator, &base_name, vec![],
        Some(writer.prepare_target(&base_name).await.unwrap()), 1);
    base.capsule = Opaque::new(Kind::Capsule,
        serde_json::to_vec(&serde_json::json!({"declId": base.group.id().hex()})).unwrap());
    base.revisions[0].capsule = base.capsule.id();
    base.job.body.capsule = base.capsule.id();
    rebind(&mut base, &validator);
    store.s3.put_opaque(&base.capsule).await.unwrap();
    let mut dependent = fixture::package("w4/dependent", workspace, &validator, &dependent_name, vec![],
        Some(writer.prepare_target(&dependent_name).await.unwrap()), 2);
    dependent.job.body.deps = vec![base.capsule.id()];
    rebind(&mut dependent, &validator);

    for _ in 0..8 { b.tick().await.unwrap(); }
    let replacement = Durable::new_shard(store.clone(), Duration::from_millis(500), 1, 2);
    let replacement_term = replacement.acquire_or_renew().await.unwrap().unwrap().term;
    assert!(replacement_term > bterm);
    assert!(b.record_receipt(b"stale", &dependent.receipt, bterm).await.is_err());
    replacement.record_receipt(b"dependent", &dependent.receipt, replacement_term).await.unwrap();
    for bypass in [false, true] {
        let outcome = if bypass { writer.publish_skipping_staging_check(&dependent).await }
            else { writer.publish(&dependent).await };
        assert!(matches!(outcome, Err(StoreError::Guard(GuardFailure::NotPublished(_)
            | GuardFailure::Uncertified(_)))), "cross-shard prerequisite bypass: {outcome:?}");
    }
    assert!(store.target(&dependent_name).await.unwrap().unwrap().head.is_none());
    writer.publish(&base).await.unwrap();
    writer.publish(&dependent).await.unwrap();
    assert!(store.target(&base_name).await.unwrap().unwrap().head.is_some());
    assert!(store.target(&dependent_name).await.unwrap().unwrap().head.is_some());
    audit::audit(&store).await.unwrap().assert_ok();
}
