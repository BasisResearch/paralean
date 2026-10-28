//! P5's task bridge and W4 controller shards share one per-target claim, so
//! neither reassigns (T4) a target the other schedules.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;
use std::time::Duration;
use paralean_control::durable::{claim_for_task, Durable};
use paralean_store::*;

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn task_and_shard_claims_are_mutually_exclusive() {
    let keys = KeyFile::demo(2);
    let store = Store::open(&StoreConfig::from_env(&common::deployment("p5-claims")).unwrap(),
        keys.ring(), Faults::none()).unwrap();
    let (workspace, _) = keys.workspace("w0").unwrap();
    let shard = Durable::new_shard(store.clone(), Duration::from_millis(500), 0, 1);
    let term = shard.acquire_or_renew().await.unwrap().unwrap().term;

    // A shard-owned target refuses a P5 claim, before any T4 write.
    let owned = Name::parse("Claims.shard");
    let epochs = shard.assign_group(&[owned.clone()], workspace, b"shard", term).await.unwrap();
    let refused = claim_for_task(&store, &owned).await;
    assert!(refused.as_ref().is_err_and(|e| e.contains("controller shard")));
    assert_eq!(store.target(&owned).await.unwrap().unwrap().epoch, epochs[0]);

    // A P5-claimed target refuses shard assignment; repeated P5 claims succeed.
    let task = Name::parse("Claims.task");
    claim_for_task(&store, &task).await.unwrap();
    claim_for_task(&store, &task).await.unwrap();
    let stolen = shard.assign_group(&[task.clone()], workspace, b"steal", term).await;
    assert!(stolen.is_err());
    assert!(store.target(&task).await.unwrap().is_none());
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("task_and_shard_claims_are_mutually_exclusive", || { task_and_shard_claims_are_mutually_exclusive(); Ok(()) }),
    ]);
}
