//! Test harness: every test gets its own deployment (FDB key root and S3 key prefix) on
//! the real P2 cluster started by `scripts/up.sh`. Run through `scripts/test.sh`, which
//! sources `scripts/env.sh`.
#![allow(dead_code)]

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use paralean_store::*;

static COUNTER: AtomicU64 = AtomicU64::new(0);

pub fn deployment(name: &str) -> String {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    format!("t-{name}-{}-{}-{}", std::process::id(), nanos % 1_000_000_000, COUNTER.fetch_add(1, Ordering::Relaxed))
}

pub struct Env {
    pub store: Store,
    pub kf: KeyFile,
    pub ctl: Controller,
    pub w: Vec<Writer>,
    pub validator: Signer,
    pub cfg: StoreConfig,
}

impl Env {
    pub fn new(name: &str, nwriters: usize) -> Env {
        Env::with_faults(name, nwriters, Faults::none())
    }

    pub fn with_faults(name: &str, nwriters: usize, faults: Arc<Faults>) -> Env {
        let cfg = StoreConfig::from_env(&deployment(name))
            .expect("PARALEAN_* not set: run the tests through impl/p2/scripts/test.sh after scripts/up.sh");
        Env::open(cfg, nwriters, faults)
    }

    pub fn open(cfg: StoreConfig, nwriters: usize, faults: Arc<Faults>) -> Env {
        let kf = KeyFile::demo(nwriters.max(1));
        let store = Store::open(&cfg, kf.ring(), faults).expect("open store");
        let ctl = Controller::new(store.clone(), kf.authority_signer().unwrap());
        let w = (0..nwriters)
            .map(|i| {
                let (id, s) = kf.workspace(&format!("w{i}")).unwrap();
                Writer::new(store.clone(), id, s)
            })
            .collect();
        let validator = kf.validator_signer("v0").unwrap();
        Env { store, kf, ctl, w, validator, cfg }
    }

    /// A writer handle using another fault plan (same identity, same deployment).
    pub fn writer_with(&self, i: usize, faults: Arc<Faults>) -> Writer {
        self.w[i].with_store(self.store.with_faults(faults))
    }

    /// Prepare (single read of the target record) and build a package revising its head.
    pub async fn prepare(&self, wi: usize, name: &Name, tag: &str, lamport: u64) -> Result<Package> {
        let w = &self.w[wi];
        let pt = w.prepare_target(name).await?;
        let parents = pt.head.into_iter().collect();
        Ok(fixture::package(tag, w.id, &self.validator, name, parents, Some(pt), lamport))
    }

    /// Prepare and publish a proof of a target name.
    pub async fn publish_target(&self, wi: usize, name: &Name, tag: &str) -> Result<(Package, PublishOutcome)> {
        let p = self.prepare(wi, name, tag, 1).await?;
        let o = self.w[wi].publish(&p).await?;
        Ok((p, o))
    }

    /// A non-target group (free name) publication.
    pub fn plain_package(&self, wi: usize, name: &str, tag: &str) -> Package {
        fixture::package(tag, self.w[wi].id, &self.validator, &Name::parse(name), vec![], None, 1)
    }

    pub async fn audit_ok(&self) -> audit::AuditReport {
        let r = audit::audit(&self.store).await.expect("audit runs");
        r.assert_ok();
        r
    }
}

pub fn guard_of<T: std::fmt::Debug>(r: Result<T>) -> GuardFailure {
    match r {
        Err(StoreError::Guard(g)) => g,
        other => panic!("expected a guard failure, got {other:?}"),
    }
}

pub fn rev_id(p: &Package) -> Id {
    p.revisions[0].id()
}
