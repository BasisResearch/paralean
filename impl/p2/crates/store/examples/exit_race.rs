//! Exit-race reproducer for the W2 chaos investigation (docs/w2-chaos-notes.md).
//!
//! Boots FDB through `meta::boot`, as every P2 binary does, runs read-version requests from
//! `EXIT_RACE_THREADS` threads for `EXIT_RACE_MS` milliseconds, then leaves `main`:
//!
//! - `EXIT_RACE_MODE=idle` (default): join the workers, drop the database, return without
//!   stopping the network thread. This is the stock libtest harness after its last test.
//! - `EXIT_RACE_MODE=busy`: return while the workers still have requests in flight.
//! - `EXIT_RACE_MODE=keep`: as `idle`, but leak the database instead of dropping it.
//! - `EXIT_RACE_MODE=stop`: join, drop, then `meta::shutdown()` (the fixed lifecycle).
//!
//! `EXIT_RACE_GAP_MS` sleeps between dropping the database and leaving `main` (`idle` only).
//!
//! Run it with `PARALEAN_FDB_CLUSTER` set; scripts/exit-race-repro.sh loops it and keeps
//! backtraces of crashed runs.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use paralean_store::meta;

fn env_num(name: &str, default: u64) -> u64 {
    std::env::var(name).ok().and_then(|s| s.parse().ok()).unwrap_or(default)
}

fn main() {
    let mode = std::env::var("EXIT_RACE_MODE").unwrap_or_else(|_| "idle".into());
    let threads = env_num("EXIT_RACE_THREADS", 4);
    let ms = env_num("EXIT_RACE_MS", 50);
    meta::boot();
    let cluster = std::env::var("PARALEAN_FDB_CLUSTER").ok();
    let db = Arc::new(foundationdb::Database::new(cluster.as_deref()).expect("open database"));
    let done = Arc::new(AtomicBool::new(false));
    let workers: Vec<_> = (0..threads)
        .map(|_| {
            let (db, done) = (db.clone(), done.clone());
            std::thread::spawn(move || {
                while !done.load(Ordering::Relaxed) {
                    if let Ok(trx) = db.create_trx() {
                        let _ = futures::executor::block_on(trx.get_read_version());
                    }
                }
            })
        })
        .collect();
    std::thread::sleep(Duration::from_millis(ms));
    if mode == "busy" {
        return;
    }
    done.store(true, Ordering::Relaxed);
    for w in workers {
        w.join().unwrap();
    }
    if mode == "keep" {
        // As `idle`, but the database is never destroyed, so no destruction is queued
        // on the network thread as the process exits.
        std::mem::forget(db);
        return;
    }
    drop(db);
    std::thread::sleep(Duration::from_millis(env_num("EXIT_RACE_GAP_MS", 0)));
    if mode == "stop" {
        meta::shutdown();
    }
}
