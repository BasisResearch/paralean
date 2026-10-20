//! A batch may use receipts from earlier jobs in that batch. The warm checker must
//! discard every job's declarations and options while keeping its base import loaded.

mod common;

use std::path::PathBuf;
use std::sync::atomic::Ordering;
use std::time::Duration;

use common::*;
use paralean_control::checker::{base_id, CheckerConfig};
use paralean_control::p1::{self, P1Group};
use paralean_store::receipt::{JobEnvelope, SignedJob, TargetBinding};
use paralean_store::*;
use paralean_validator_api::{rpc, ValidatorRequest, ValidatorResponse};

fn job(c: &Cluster, w: WorkspaceId, groups: &std::collections::BTreeMap<String, P1Group>,
       g: &P1Group, request: &str, targets: Vec<TargetBinding>) -> SignedJob {
    let closure = p1::closure(groups, &g.gid).unwrap();
    let deps = closure[..closure.len() - 1].iter().map(|id| groups[id].capsule_id()).collect();
    SignedJob::sign(JobEnvelope {
        request: request.as_bytes().to_vec(), group: g.decl, capsule: g.capsule_id(), deps,
        base: base_id(&c.checker.lean_githash), policy: paralean_store::receipt::Policy::v1().id(),
        checker: c.validators[0].checker_id(), worker: w, targets, deadline_ms: 120_000, memory_mb: 4096,
    }, &c.kf.authority_signer().unwrap())
}

async fn batch(c: &Cluster, jobs: &[SignedJob]) -> Vec<ValidatorResponse> {
    let request = ValidatorRequest::ValidateBatch { jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect() };
    let authority = c.kf.authority_signer().unwrap();
    let response: ValidatorResponse = rpc::call_authenticated(&c.vaddrs[0], &request, &authority,
        &c.vsigners[0].public(), Duration::from_secs(300)).await.unwrap();
    let ValidatorResponse::Batch { responses } = response else { panic!("batch response: {response:?}") };
    responses
}

fn accepted(r: &ValidatorResponse) -> bool {
    match r {
        ValidatorResponse::Receipt { receipt } => paralean_validator_api::decode_receipt(receipt).unwrap().body.verdict == Verdict::Accepted,
        _ => false,
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn batch_retries_joined_standalone_dependency_refusal() {
    // A standalone dependent can queue behind a prerequisite before the batch
    // obtains the prerequisite receipt. Both callers then share its request slot,
    // but only the batch has a temporary accepted dependency certificate.
    let tmp = scratch("batch-joined-refusal");
    let wrapper = tmp.join("slow-checker.sh");
    std::fs::write(&wrapper, "#!/usr/bin/env bash\nsleep 1\nexec \"$PARALEAN_REAL_BIN\" \"$@\"\n").unwrap();
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
    let mut checker = CheckerConfig::from_env().unwrap();
    let real_bin = checker.bin.clone();
    checker.bin = wrapper;
    checker.env.retain(|(key, _)| key != "PARALEAN_P3_WARM_BIN");
    checker.env.push(("PARALEAN_REAL_BIN".into(), real_bin.display().to_string()));
    // The slow stand-in finds the real binary by host path and environment, which the
    // sandbox withholds; this test is about request-slot sharing, not containment.
    checker.sandbox = false;
    let c = Cluster::start("batch-joined-refusal", Opts {
        validators: vec![Mode::Real], checker: Some(checker), validator_max_running: 1,
        ..Opts::default()
    }).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let small = w.group_declaring(&Name::parse("F01.small")).unwrap();
    let dependent = w.group_declaring(&Name::parse("F01.uses_small")).unwrap();
    assert_eq!(p1::closure(&w.groups, &dependent.gid).unwrap(), vec![small.gid.clone(), dependent.gid.clone()]);
    for g in [small, dependent] {
        c.store.s3.put_opaque(&g.group_object()).await.unwrap();
        c.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
    }
    let first = job(&c, w.id(), &w.groups, small, "batch/race/small", vec![]);
    let second = job(&c, w.id(), &w.groups, dependent, "batch/race/dependent", vec![]);
    let validator = c.validators[0].clone();
    let running = tokio::spawn({ let v = validator.clone(); let j = first.clone(); async move { v.validate(j).await } });
    let deadline = tokio::time::Instant::now() + Duration::from_secs(10);
    while !matches!(validator.handle(ValidatorRequest::Status).await,
        ValidatorResponse::Status { running: 1, .. }) {
        assert!(tokio::time::Instant::now() < deadline, "prerequisite never occupied validator");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    let standalone = tokio::spawn({ let v = validator.clone(); let j = second.clone(); async move { v.validate(j).await } });
    while !matches!(validator.handle(ValidatorRequest::Status).await,
        ValidatorResponse::Status { queued: 1, .. }) {
        assert!(tokio::time::Instant::now() < deadline, "dependent never queued behind prerequisite");
        tokio::time::sleep(Duration::from_millis(5)).await;
    }
    let ordered = ValidatorRequest::ValidateBatch {
        jobs: [first, second].iter().map(|j| hex::encode(j.to_bytes())).collect(),
    };
    let batched = tokio::spawn({ let v = validator.clone(); async move { v.handle(ordered).await } });
    let standalone_response = standalone.await.unwrap();
    assert!(matches!(&standalone_response, ValidatorResponse::Refused { reason }
        if reason.contains("dependency")), "{standalone_response:?}");
    assert!(accepted(&running.await.unwrap()));
    let response = batched.await.unwrap();
    let ValidatorResponse::Batch { responses } = response else { panic!("{response:?}") };
    assert!(responses.iter().all(accepted), "batch lost temporary dependency proof: {responses:?}");
    assert_eq!(validator.checks_run.load(Ordering::SeqCst), 2);
    assert!(c.store.marker(&dependent.decl).await.unwrap().is_none());
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn dependent_batch_requires_earlier_accepted_receipts_and_deduplicates() {
    let c = Cluster::start("batch-deps", Opts { validators: vec![Mode::Real], validator_max_running: 1, ..Opts::default() }).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let root = w.group_declaring(&Name::parse("F01.uses_small")).unwrap();
    let closure = p1::closure(&w.groups, &root.gid).unwrap();
    assert!(closure.len() >= 2);
    for gid in &closure {
        let group = &w.groups[gid];
        c.store.s3.put_opaque(&group.group_object()).await.unwrap();
        c.store.s3.put_opaque(&group.capsule_object()).await.unwrap();
    }
    let ordered: Vec<SignedJob> = closure.iter().enumerate().map(|(i, gid)|
        job(&c, w.id(), &w.groups, &w.groups[gid], &format!("batch/order/{i}"), vec![])).collect();
    let mut reversed = ordered.clone();
    reversed.reverse();
    let wrong_order = batch(&c, &reversed).await;
    assert!(matches!(&wrong_order[0], ValidatorResponse::Refused { reason } if reason.contains("dependency")), "{wrong_order:?}");
    let results = batch(&c, &ordered).await;
    assert!(results.iter().all(accepted), "{results:?}");
    let checks = c.validators[0].checks_run.load(Ordering::SeqCst);
    assert_eq!(batch(&c, &ordered).await, results);
    assert_eq!(c.validators[0].checks_run.load(Ordering::SeqCst), checks);
    assert!(c.store.marker(&root.decl).await.unwrap().is_none(), "batch validation must not publish");

    let small = w.group_declaring(&Name::parse("F01.small")).unwrap();
    assert!(closure.iter().any(|gid| gid == &small.gid));
    let bad = job(&c, w.id(), &w.groups, small, "batch/bad-prerequisite", vec![TargetBinding {
        name: Name::parse("F01.small"), epoch: 0, statement: vec![0; 32],
    }]);
    let dependent = job(&c, w.id(), &w.groups, root, "batch/blocked-dependent", vec![]);
    let rejected = batch(&c, &[bad, dependent]).await;
    assert!(matches!(&rejected[0], ValidatorResponse::Receipt { receipt }
        if matches!(paralean_validator_api::decode_receipt(receipt).unwrap().body.verdict, Verdict::Rejected(_))), "{rejected:?}");
    assert!(matches!(&rejected[1], ValidatorResponse::Refused { reason } if reason.contains("dependency")), "{rejected:?}");

    // Byte-distinct capsules may describe the same group. An accepted alias must
    // not replace the receipt for the exact capsule named by the dependent job.
    let mut alias = small.clone();
    alias.meta_json = serde_json::to_vec_pretty(&alias.meta).unwrap();
    alias.meta_json.push(b'\n');
    assert_ne!(alias.capsule_id(), small.capsule_id());
    c.store.s3.put_opaque(&alias.capsule_object()).await.unwrap();
    let mut aliases = ordered[..ordered.len() - 1].to_vec();
    aliases.push(job(&c, w.id(), &w.groups, &alias, "batch/alias", vec![]));
    aliases.push(job(&c, w.id(), &w.groups, root, "batch/after-alias", vec![]));
    assert!(batch(&c, &aliases).await.iter().all(accepted));

    // Batch admission only supplies temporary proof to the validator. T1 must see
    // every prerequisite's published marker and certificate before the root commits.
    let package_at = |index: usize| {
        let ValidatorResponse::Receipt { receipt } = &results[index] else { unreachable!() };
        let receipt = paralean_validator_api::decode_receipt(receipt).unwrap();
        w.package(&w.groups[&closure[index]], receipt, ordered[index].clone(), vec![])
    };
    let root_package = package_at(closure.len() - 1);
    let missing = guard(w.writer.publish(&root_package).await);
    assert!(matches!(missing, GuardFailure::NotPublished(_) | GuardFailure::Uncertified(_)), "{missing:?}");
    let bypass = guard(w.writer.publish_skipping_staging_check(&root_package).await);
    assert!(matches!(bypass, GuardFailure::NotPublished(_) | GuardFailure::Uncertified(_)), "T1 bypass: {bypass:?}");
    assert!(c.store.marker(&root.decl).await.unwrap().is_none());
    for i in 0..closure.len() - 1 {
        assert!(w.writer.publish(&package_at(i)).await.unwrap().fresh);
    }
    assert!(w.writer.publish(&root_package).await.unwrap().fresh);
    c.audit_ok().await;
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn warm_process_rechecks_same_declaration_without_leaking_environment() {
    let Some(mut checker) = fork_checker() else {
        eprintln!("skipped: fork P1 checker not installed");
        return;
    };
    let warm_bin = repo().join("impl/p3/lean/.lake/build/bin/paralean-warm");
    let store = PathBuf::from(std::env::var("PARALEAN_P3_FORK_STORE")
        .unwrap_or_else(|_| repo().join(".runs/p1-fork-core/store").display().to_string()));
    if !warm_bin.is_file() || !store.join("meta").is_dir() {
        eprintln!("skipped: warm binary or fork fixture store unavailable");
        return;
    }
    checker.env.push(("PARALEAN_P3_WARM_BIN".into(), warm_bin.display().to_string()));
    let c = Cluster::start("warm-isolation", Opts { validators: vec![Mode::Real], checker: Some(checker),
        validator_max_running: 1, ..Opts::default() }).await;
    let w = c.worker(0, 8192, &store).await;
    let group = w.group_declaring(&Name::parse("F01.small")).unwrap();
    c.store.s3.put_opaque(&group.group_object()).await.unwrap();
    c.store.s3.put_opaque(&group.capsule_object()).await.unwrap();
    let wrong_statement = job(&c, w.id(), &w.groups, group, "warm/rejected", vec![TargetBinding {
        name: Name::parse("F01.small"), epoch: 0, statement: vec![0; 32],
    }]);
    let first = job(&c, w.id(), &w.groups, group, "warm/first", vec![]);
    let second = job(&c, w.id(), &w.groups, group, "warm/second", vec![]);
    let responses = batch(&c, &[wrong_statement, first, second]).await;
    assert!(matches!(&responses[0], ValidatorResponse::Receipt { receipt }
        if matches!(paralean_validator_api::decode_receipt(receipt).unwrap().body.verdict, Verdict::Rejected(_))), "{responses:?}");
    assert!(responses[1..].iter().all(accepted), "{responses:?}");
    assert_eq!(c.validators[0].checks_run.load(Ordering::SeqCst), 3);
    assert_eq!(c.validators[0].warm_pool.spawned.load(Ordering::SeqCst), 1, "one process should serve all three jobs");

    let dependent = w.group_declaring(&Name::parse("F01.uses_small")).unwrap();
    c.store.s3.put_opaque(&dependent.group_object()).await.unwrap();
    c.store.s3.put_opaque(&dependent.capsule_object()).await.unwrap();
    let request = ValidatorRequest::Validate { job: hex::encode(job(&c, w.id(), &w.groups, dependent,
        "warm/unpublished-dependency", vec![]).to_bytes()) };
    let response: ValidatorResponse = rpc::call_authenticated(&c.vaddrs[0], &request,
        &c.kf.authority_signer().unwrap(), &c.vsigners[0].public(), Duration::from_secs(30)).await.unwrap();
    assert!(matches!(&response, ValidatorResponse::Refused { reason } if reason.contains("dependency")), "{response:?}");
    assert_eq!(c.validators[0].warm_pool.spawned.load(Ordering::SeqCst), 1);

    // When the fork fixture store includes F11ScopedDecl, replay a group whose
    // capsule needs scoped notation, then return to F01 in the same process.
    if let Some(scoped) = w.group_declaring(&Name::parse("F11.star_def")) {
        let closure = p1::closure(&w.groups, &scoped.gid).unwrap();
        for gid in &closure {
            let g = &w.groups[gid];
            c.store.s3.put_opaque(&g.group_object()).await.unwrap();
            c.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
        }
        let jobs: Vec<SignedJob> = closure.iter().enumerate().map(|(i, gid)|
            job(&c, w.id(), &w.groups, &w.groups[gid], &format!("warm/scoped/{i}"), vec![])).collect();
        let scoped_results = batch(&c, &jobs).await;
        assert!(scoped_results.iter().all(accepted), "scoped notation batch: {scoped_results:?}");
        let after_scope = job(&c, w.id(), &w.groups, group, "warm/after-scope", vec![]);
        assert!(accepted(&batch(&c, &[after_scope]).await[0]));
        assert_eq!(c.validators[0].warm_pool.spawned.load(Ordering::SeqCst), 1,
            "scoped notation and F01 must share an isolated process");
    }

    let (_cancel, cancel_rx) = tokio::sync::watch::channel(false);
    let timed_out = c.validators[0].warm_pool.run(&c.checker, &store, &[group.gid.clone()], &group.decl.hex(),
        &[], Duration::from_millis(1), 4096, cancel_rx).await;
    assert!(matches!(timed_out, Err(paralean_control::checker::NoVerdict::Timeout)), "{timed_out:?}");
    let last = job(&c, w.id(), &w.groups, group, "warm/replaced-process", vec![]);
    assert!(accepted(&batch(&c, &[last]).await[0]));
    assert_eq!(c.validators[0].warm_pool.spawned.load(Ordering::SeqCst), 2, "timeout must replace the process");
}
