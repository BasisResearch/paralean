//! FoundationDB controller lease and snapshot invariants, using a fresh deployment.

mod common;

use std::time::Duration;

use common::deployment;
use paralean_control::durable::Durable;
use paralean_store::*;

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn large_snapshot_roundtrips_and_old_leader_writes_are_fenced() {
    let cfg = StoreConfig::from_env(&deployment("durable-chunks")).unwrap();
    let keys = KeyFile::demo(2);
    let store = Store::open(&cfg, keys.ring(), Faults::none()).unwrap();
    let old = Durable::new(store.clone(), Duration::from_millis(500));
    let next = Durable::new(store.clone(), Duration::from_millis(500));
    let first = old.acquire_or_renew().await.unwrap().unwrap();
    assert!(next.acquire_or_renew().await.unwrap().is_none());

    // Three 60 KiB chunks, plus a tail: FDB cannot store this as one value.
    let bytes = (0..180_123usize).map(|i| ((i * 131 + i / 977) % 251) as u8).collect::<Vec<_>>();
    old.save(&bytes, first.term).await.unwrap();
    assert_eq!(old.load().await.unwrap(), Some(bytes.clone()));
    assert_eq!(next.load().await.unwrap(), Some(bytes));

    tokio::time::sleep(Duration::from_millis(650)).await;
    let second = next.acquire_or_renew().await.unwrap().unwrap();
    assert!(second.term > first.term);
    assert!(old.save(b"stale state", first.term).await.is_err());
    assert!(old.assign_group(&[Name::parse("Durable.target")], keys.workspace("w0").unwrap().0,
        b"stale assignment", first.term).await.is_err());
    let (worker, _) = keys.workspace("w0").unwrap();
    let receipt = fixture::package("stale-receipt", worker, &Signer::derive("validator"),
        &Name::parse("Durable.free"), vec![], None, 1).receipt;
    assert!(old.record_receipt(b"stale-j2", &receipt, first.term).await.is_err());
    assert!(store.meta.get(store.meta.keys.job_receipt(b"stale-j2")).await.unwrap().is_none());

    next.save(b"new leader state", second.term).await.unwrap();
    assert_eq!(old.load().await.unwrap(), Some(b"new leader state".to_vec()));
    assert_eq!(next.assign_group(&[Name::parse("Durable.target")], worker, b"new assignment", second.term).await.unwrap(), vec![0]);
}
