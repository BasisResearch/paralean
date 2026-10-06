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
        Env::open_keys(cfg, KeyFile::demo(nwriters.max(1)), nwriters, faults, None)
    }

    /// A deployment with its own key file; `peer` adds another deployment's writers and
    /// validators to the trusted ring (anti-entropy).
    pub fn open_keys(cfg: StoreConfig, kf: KeyFile, nwriters: usize, faults: Arc<Faults>, peer: Option<&KeyRing>) -> Env {
        let mut ring = kf.ring();
        if let Some(p) = peer {
            ring.trust(p);
        }
        let store = Store::open(&cfg, ring, faults).expect("open store");
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

/// Publish one plain group from writer `wi` and build a checkpoint over its revision.
pub async fn one_snapshot(e: &Env, wi: usize, tag: &str, token: TokenRef, pred: Option<Id>) -> Checkpoint {
    let p = e.plain_package(wi, &format!("N.{tag}"), tag);
    e.w[wi].publish(&p).await.unwrap();
    fixture::checkpoint(e.w[wi].id, vec![rev_id(&p)], pred, token, tag)
}

/// Put a checkpoint's manifests and snapshot and certify them (everything T5 needs except
/// the record), returning the snapshot ID.
pub async fn prepare_snapshot(e: &Env, wi: usize, cp: &Checkpoint) -> Id {
    let st = &e.store;
    for rid in &cp.snapshot.contents {
        let rev = st.revision(rid).await.unwrap().unwrap();
        e.w[wi].certify_existing(Kind::Group, &rev.group).await.unwrap();
        e.w[wi].certify_existing(Kind::Capsule, &rev.capsule).await.unwrap();
    }
    for m in [&cp.source_root, &cp.build_receipt] {
        let a = st.s3.put_object(Kind::Manifest, m).await.unwrap();
        e.w[wi].certify_object(a).await.unwrap();
    }
    let a = st.s3.put_object(Kind::Snapshot, &cp.snapshot).await.unwrap();
    e.w[wi].certify_object(a).await.unwrap();
    a.id()
}

/// A hook that rotates the fence to `holder`.
pub fn rotate_hook(ctl: &Controller, holder: WorkspaceId, request: &str) -> faults::Hook {
    let ctl = ctl.clone();
    let request = request.as_bytes().to_vec();
    std::sync::Arc::new(move || {
        let (ctl, request) = (ctl.clone(), request.clone());
        Box::pin(async move {
            ctl.rotate(holder, &request).await.unwrap();
        })
    })
}

/// A hook that reassigns a target name.
pub fn reassign_hook(ctl: &Controller, name: Name, owner: WorkspaceId, request: &str) -> faults::Hook {
    let ctl = ctl.clone();
    let request = request.as_bytes().to_vec();
    std::sync::Arc::new(move || {
        let (ctl, request, name) = (ctl.clone(), request.clone(), name.clone());
        Box::pin(async move {
            ctl.reassign(&name, owner, &request).await.unwrap();
        })
    })
}

/// The second deployment's configuration: its own FoundationDB cluster and S3 store when
/// `scripts/test.sh` runs with `PARALEAN_PEER_INSTANCE` (PARALEAN_PEER_*), otherwise another
/// key root on the same cluster.
pub fn peer_config(name: &str) -> StoreConfig {
    let dep = deployment(name);
    if std::env::var("PARALEAN_PEER_FDB_CLUSTER").is_ok() {
        StoreConfig::from_env_with("PARALEAN_PEER_", &dep).unwrap()
    } else {
        eprintln!("PARALEAN_PEER_INSTANCE not set: the peer deployment shares this cluster");
        StoreConfig::from_env(&dep).unwrap()
    }
}

/// Two independent deployments A and B (distinct identities, fences and replicas), each
/// trusting the other's writers. Writer `n-1` of each is its anti-entropy agent.
pub fn pair(name: &str, n: usize, fa: Arc<Faults>, fb: Arc<Faults>) -> (Env, Env) {
    let (ka, kb) = (KeyFile::demo_prefixed("a/", n), KeyFile::demo_prefixed("b/", n));
    let ca = StoreConfig::from_env(&deployment(&format!("{name}-a"))).unwrap();
    let cb = peer_config(&format!("{name}-b"));
    let a = Env::open_keys(ca, ka.clone(), n, fa, Some(&kb.ring()));
    let b = Env::open_keys(cb, kb, n, fb, Some(&ka.ring()));
    (a, b)
}
