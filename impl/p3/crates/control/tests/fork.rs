//! Validators running the Paralean fork (impl/p1 built against fork/, hooks on through
//! `Paralean/Fork.lean`) instead of the stock binary. Opt-in: set `PARALEAN_P3_FORK_BIN`
//! and `PARALEAN_P3_FORK_PREFIX` (impl/p3/scripts/test.sh does when a fork build exists,
//! and captures F01 and F04 with it into `.runs/p1-fork-core`).

mod common;

use common::*;
use paralean_control::controller::{ControlRequest, ControlResponse};
use paralean_store::*;

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn fork_validators_check_and_sign() {
    let Some(fork) = fork_checker() else {
        eprintln!("skipped: PARALEAN_P3_FORK_BIN / PARALEAN_P3_FORK_PREFIX not set");
        return;
    };
    let version = fork.version().unwrap();
    assert_eq!(version.mode, "fork");
    let c = Cluster::start("fork", Opts { checker: Some(fork), ..Opts::default() }).await;
    assert_eq!(c.validators[0].checker_id(), version.id());
    // A target with three dependencies, captured with the fork: four fork-checked receipts.
    // (Stock-captured groups with derived instances do not replay on the fork, whose
    // canonical instance names differ: such a group is rejected, never accepted.)
    let store = std::env::var("PARALEAN_P3_FORK_STORE").map(std::path::PathBuf::from).unwrap_or(repo().join(".runs/p1-fork-core/store"));
    let w = c.worker(0, 8192, &store).await;
    let t = Name::parse("F04.red_ne_green");
    c.call(ControlRequest::SubmitWork { request: "fork/red".into(), target: t.to_string(), memory_mb: 512 }).await;
    let work = w.poll().await.unwrap().unwrap();
    w.prove(&work).await.unwrap();
    let g = w.group_declaring(&t).unwrap();
    let (r, _) = paralean_validator_api::published_receipt(&c.store, &g.decl).await.unwrap();
    assert_eq!(r.body.validator_bin, version.id().0.to_vec());
    // The kernel-skipped ill-typed theorem is rejected by the fork's kernel as well.
    let neg = negative_store(&c.tmp.join("neg"));
    let nw = c.worker(1, 8192, &neg).await;
    let bad = nw.group_declaring(&Name::parse("N3.bad")).unwrap().clone();
    nw.writer.store.s3.put_opaque(&bad.group_object()).await.unwrap();
    nw.writer.store.s3.put_opaque(&bad.capsule_object()).await.unwrap();
    let resp = c
        .call(ControlRequest::Validate {
            worker: nw.id().hex(),
            request: "fork/n3".into(),
            group: bad.decl.hex(),
            capsule: bad.capsule_id().hex(),
            deps: vec![],
            targets: vec![],
            memory_mb: 0,
            deadline_ms: 0,
        })
        .await;
    let ControlResponse::Receipt { receipt, .. } = resp else { panic!("{resp:?}") };
    let r = paralean_validator_api::decode_receipt(&receipt).unwrap();
    assert!(matches!(r.body.verdict, Verdict::Rejected(_)));
    c.audit_ok().await;
}
