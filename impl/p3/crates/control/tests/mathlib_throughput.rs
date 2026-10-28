//! Full M01--M18 validator measurement. Input stores are P1 captures at the pinned
//! fork/Mathlib versions. Run with PARALEAN_P3_MATHLIB_STORES=/.../mathlib and
//! PARALEAN_P3_WARM_BIN=/.../paralean-warm, --ignored --nocapture --test-threads=1.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;

use std::collections::BTreeSet;
use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use common::*;
use paralean_control::{checker::base_id, p1, worker::WorkerNode};
use paralean_store::{receipt::{JobEnvelope, Policy, SignedJob}, *};
use paralean_validator_api::{rpc, ValidatorRequest, ValidatorResponse};

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn mathlib_throughput() {
    let stores = std::path::PathBuf::from(std::env::var("PARALEAN_P3_MATHLIB_STORES").expect("Mathlib stores"));
    let report = std::env::var("PARALEAN_P3_THROUGHPUT_REPORT").expect("report path");
    let mut rows = Vec::new();
    let only = std::env::var("PARALEAN_P3_MEASURE_MODULES").unwrap_or_default();
    for module in 1..=18 {
        let id = format!("M{module:02}");
        if !only.is_empty() && !only.split(',').any(|m| m == id) { continue; }
        let input = stores.join(&id).join("store");
        assert!(input.join("meta").is_dir(), "missing {}", input.display());
        let c = Cluster::start(&format!("mathlib-{id}"), Opts {
            validators: vec![Mode::Real], validator_max_running: 1,
            lease_ms: 600_000, memory_mb: 8192, deadline_ms: 120_000,
            ..Opts::default()
        }).await;
        let warm = c.checker.warm_bin().is_some();
        assert!(warm || std::env::var_os("PARALEAN_P3_MEASURE_COLD").is_some(),
            "configure a warm checker, or explicitly set PARALEAN_P3_MEASURE_COLD for a cold comparison");
        let w = WorkerNode::new(c.writer(0), &c.ctl_addr, 8192, &input).unwrap();
        let authority = c.kf.authority_signer().unwrap();
        let checker_id = c.validators[0].checker_id();
        let mut seen = BTreeSet::new();
        let mut order = Vec::new();
        for gid in w.groups.keys() {
            for dep in p1::closure(&w.groups, gid).unwrap() {
                if seen.insert(dep.clone()) { order.push(dep); }
            }
        }
        let begin = Instant::now();
        let mut payload_bytes = 0;
        for g in w.groups.values() {
            payload_bytes += g.grp.len() + g.meta_json.len();
            c.store.s3.put_opaque(&g.group_object()).await.unwrap();
            c.store.s3.put_opaque(&g.capsule_object()).await.unwrap();
        }
        let upload_s = begin.elapsed().as_secs_f64();
        let mut accepted = 0;
        let mut published = 0;
        let mut duplicate = 0;
        let mut failures = Vec::new();
        let mut validation_s = 0.0;
        let mut publish_s = 0.0;
        for chunk in order.chunks(32) {
            let mut jobs = Vec::new();
            for gid in chunk {
                let g = &w.groups[gid];
                let closure = p1::closure(&w.groups, gid).unwrap();
                let job = SignedJob::sign(JobEnvelope {
                    request: format!("{id}/{gid}").into_bytes(),
                    group: g.decl, capsule: g.capsule_id(),
                    deps: closure[..closure.len()-1].iter().map(|d| w.groups[d].capsule_id()).collect(),
                    base: base_id(&c.checker.lean_githash), policy: Policy::v1().id(),
                    checker: checker_id, worker: w.id(), targets: vec![],
                    deadline_ms: 120_000, memory_mb: 8192,
                }, &authority);
                c.store.meta.issue_job(&job).await.unwrap();
                jobs.push(job);
            }
            let start = Instant::now();
            let response: ValidatorResponse = rpc::call_authenticated(
                &c.vaddrs[0], &ValidatorRequest::ValidateBatch {
                    jobs: jobs.iter().map(|j| hex::encode(j.to_bytes())).collect(),
                }, &authority, &c.vsigners[0].public(), Duration::from_secs(4000),
            ).await.unwrap();
            validation_s += start.elapsed().as_secs_f64();
            let ValidatorResponse::Batch { responses } = response else { panic!("{response:?}") };
            assert_eq!(responses.len(), jobs.len());
            for ((gid, job), response) in chunk.iter().zip(jobs).zip(responses) {
                let ValidatorResponse::Receipt { receipt } = response else {
                    failures.push(serde_json::json!({"gid":gid,"reason":format!("{response:?}")}));
                    continue;
                };
                let receipt = paralean_validator_api::decode_receipt(&receipt).unwrap();
                if receipt.body.verdict != Verdict::Accepted {
                    failures.push(serde_json::json!({"gid":gid,"reason":format!("{:?}",receipt.body.verdict)}));
                    continue;
                }
                accepted += 1;
                let start = Instant::now();
                match w.writer.publish(&w.package(&w.groups[gid], receipt, job, vec![])).await {
                    Ok(_) => published += 1,
                    Err(StoreError::Guard(GuardFailure::AlreadyPublished { .. })) => duplicate += 1,
                    Err(e) => failures.push(serde_json::json!({"gid":gid,"reason":format!("T1: {e}")})),
                }
                publish_s += start.elapsed().as_secs_f64();
            }
            eprintln!("MEASURE {id}: {}/{} groups", accepted + failures.len(), order.len());
        }
        c.audit_ok().await;
        let row = serde_json::json!({
            "module":id, "groups":order.len(), "accepted":accepted, "published":published,
            "duplicate":duplicate, "failures":failures,
            "validation_s":validation_s, "validation_s_per_group":validation_s / order.len().max(1) as f64,
            "groups_per_s":order.len() as f64 / validation_s,
            "upload_s":upload_s, "publish_s":publish_s, "total_s":begin.elapsed().as_secs_f64(),
            "payload_bytes":payload_bytes, "batch_size":32,
            "pool_mode": if warm { "warm" } else { "cold" },
            "warm_processes":c.validators[0].warm_pool.spawned.load(Ordering::SeqCst),
            "peak_checker_rss_kb":c.validators[0].warm_pool.peak_rss_kb.load(Ordering::SeqCst),
            "checker":checker_id.hex(),
            "lean_githash":c.checker.lean_githash,
        });
        println!("MATHLIB {row}");
        rows.push(row);
        std::fs::write(&report, serde_json::to_vec_pretty(&rows).unwrap()).unwrap();
    }
    if only.is_empty() {
        assert_eq!(rows.len(), 18);
        assert_eq!(rows.iter().map(|r| r["groups"].as_u64().unwrap()).sum::<u64>(), 1105,
            "the full pinned Mathlib sample must contain 1,105 groups");
    }
    // A timing report is not certification. Keep the report even on failure,
    // but do not let a rejected or unpublished group produce a green test.
    for row in &rows {
        assert!(row["failures"].as_array().unwrap().is_empty(),
            "{} certification failures: {}", row["module"], row["failures"]);
        assert_eq!(row["accepted"], row["groups"], "{} acceptance", row["module"]);
        assert_eq!(row["published"].as_u64().unwrap() + row["duplicate"].as_u64().unwrap(),
            row["groups"].as_u64().unwrap(), "{} publication", row["module"]);
    }
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("mathlib_throughput", || { mathlib_throughput(); Ok(()) }).with_ignored_flag(true),
    ]);
}
