//! Costs (ignored by default; `scripts/test.sh --test measure -- --ignored --nocapture`):
//! validate and publish every group of the core fixture store F01–F13 in dependency order
//! through the controller and two validators, and report check latency and payload bytes.

mod common;

use std::time::Instant;

use common::*;
use paralean_control::p1;
use paralean_store::*;

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore]
async fn measure_validation_costs() {
    let c = Cluster::start("measure", Opts::default()).await;
    let w = c.worker(0, 8192, &core_store()).await;
    let mut order: Vec<String> = Vec::new();
    for gid in w.groups.keys() {
        for d in p1::closure(&w.groups, gid).unwrap() {
            if !order.contains(&d) {
                order.push(d);
            }
        }
    }
    let mut dedup = 0;
    let (mut ok, mut failed, mut bytes, mut closure_sizes) = (0, Vec::new(), 0usize, 0usize);
    let mut lat: Vec<f64> = Vec::new();
    let t_all = Instant::now();
    for gid in &order {
        let g = w.groups[gid].clone();
        if g.names().is_empty() {
            failed.push(format!("{} (no name to publish under)", g.file()));
            continue;
        }
        let t0 = Instant::now();
        let res = w.validate(&g, &format!("measure/{gid}"), &[], 0).await;
        let dt = t0.elapsed().as_secs_f64();
        match res {
            Ok((r, j)) => {
                lat.push(dt);
                bytes += g.grp.len() + g.meta_json.len();
                closure_sizes += j.body.deps.len() + 1;
                match w.writer.publish(&w.package(&g, r, j, vec![])).await {
                    Ok(_) => ok += 1,
                    // Byte-identical declarations of two P1 packages share a group ID (OPEN-23).
                    Err(StoreError::Guard(GuardFailure::AlreadyPublished { .. })) => dedup += 1,
                    Err(e) => panic!("{e}"),
                }
            }
            Err(e) => failed.push(format!("{} {:?}", g.file(), e).chars().take(200).collect()),
        }
    }
    lat.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let pct = |p: f64| lat[((lat.len() as f64 - 1.0) * p) as usize];
    println!(
        "MEASURE groups={} published={ok} same_group_id={dedup} failed={} total_s={:.1} check_p50_s={:.3} check_p95_s={:.3} check_max_s={:.3} payload_bytes={bytes} mean_closure={:.2}",
        order.len(),
        failed.len(),
        t_all.elapsed().as_secs_f64(),
        pct(0.5),
        pct(0.95),
        lat[lat.len() - 1],
        closure_sizes as f64 / (ok + dedup) as f64
    );
    for f in &failed {
        println!("  not published: {f}");
    }
    c.audit_ok().await;
}
