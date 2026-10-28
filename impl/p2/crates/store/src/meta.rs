//! FoundationDB metadata store (API 730): key layout, the transaction retry loop and the
//! bodies of transactions T1–T7 of docs/store.md.
//!
//! Every transaction is idempotent: its body first reads whether its effect is already
//! present and, if so, returns without writing (`Step::Done`). That makes retrying the
//! resolution of an unknown outcome: after `commit_unknown_result` (real or injected) the
//! loop re-runs the body in a fresh transaction, which either finds the effect (the earlier
//! attempt committed) or re-checks every guard against current state and commits or
//! aborts. A writer never proceeds past an unresolved outcome: if the loop gives up it
//! returns `StoreError::Unresolved`, never a guard failure.
//!
//! Protocol key spaces are grow-only, which the paginated-scan argument of store.md
//! needs: nothing clears a marker, certificate, tombstone, grant, fence, catalogue or
//! registry key. The only clears are the anti-entropy work queues in `ae.rs` (pending
//! events and their parts, once archived as terminal records); they hold no lineage.
//! W4's controller GC clears only its own `controller/shard/*` chunks and retirements.

use std::sync::{Arc, Mutex, OnceLock};

use foundationdb::api::NetworkAutoStop;
use foundationdb::future::FdbValues;
use foundationdb::options::StreamingMode;
use foundationdb::tuple::{Bytes, Subspace};
use foundationdb::{Database, KeySelector, RangeOption, Transaction};
use futures::future::BoxFuture;

use crate::error::{GuardFailure, Result, StoreError};
use crate::ae::{append_event, AeKind};
use crate::ae::config_in_txn;
use crate::faults::{CommitFault, Faults, Txn};
use crate::id::{sha256, AgentId, Id, Kind, WorkspaceId};
use crate::objects::*;
use crate::pce::{Dec, Enc, Pce};

/// FDB values above this size are spilled to a content-addressed `blob` in S3 (store.md
/// "Layout"; FDB's own limit is 100 kB).
pub const INLINE_LIMIT: usize = 64 * 1024;

static NETWORK: OnceLock<Mutex<Option<NetworkAutoStop>>> = OnceLock::new();

/// Select API version 730 and start the FDB network thread once per process. The guard is
/// kept until `shutdown`.
pub fn boot() {
    NETWORK.get_or_init(|| {
        let builder = foundationdb::api::FdbApiBuilder::default()
            .set_runtime_version(730)
            .build()
            .expect("select FDB API version 730");
        Mutex::new(Some(unsafe { builder.boot() }.expect("start FDB network")))
    });
}

/// Stop the FDB network thread and join it (before process exit; the client library's
/// thread must not run while the process tears down). FDB cannot be used afterwards.
#[cfg(not(feature = "mutate-no-network-shutdown"))]
pub fn shutdown() {
    if let Some(m) = NETWORK.get() {
        drop(m.lock().unwrap_or_else(|p| p.into_inner()).take());
    }
}

/// Mutation support only (`mutate-no-network-shutdown`): leave the network thread running
/// into process exit, as the CLI did before it stopped the thread explicitly.
#[cfg(feature = "mutate-no-network-shutdown")]
pub fn shutdown() {}

/// Run a binary's async `main` on a multi-threaded Tokio runtime, drop the runtime (every
/// task, database and future it owns), then stop and join FDB's network thread, also when
/// `main` unwinds. Returning into `exit()` with that thread running can crash in
/// libfdb_c's exit-time destructors (docs/w2-chaos-notes.md).
pub fn run_main<T>(main: impl std::future::Future<Output = T>) -> T {
    struct Stop;
    impl Drop for Stop {
        fn drop(&mut self) { shutdown() }
    }
    let _stop = Stop;
    let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build().expect("start the Tokio runtime");
    let out = rt.block_on(main);
    drop(rt);
    out
}

#[cfg(test)]
mod lifecycle_tests {
    use super::{boot, shutdown, NETWORK};

    const CHILD: &str = "PARALEAN_NETWORK_EXIT_TEST_CHILD";

    #[test]
    fn network_stops_before_process_exit() {
        if std::env::var_os(CHILD).is_some() {
            boot();
            assert!(NETWORK.get().unwrap().lock().unwrap().is_some());
            shutdown();
            assert!(NETWORK.get().unwrap().lock().unwrap().is_none());
            return;
        }
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "meta::lifecycle_tests::network_stops_before_process_exit"])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(output.status.success(), "shutdown did not stop and join FDB: status {:?}, stderr {}",
            output.status, String::from_utf8_lossy(&output.stderr));
    }
}

// ---------------------------------------------------------------- keys

/// The key layout of store.md under one deployment root `("paralean", <deployment>)`.
#[derive(Clone)]
pub struct Keys {
    pub root: Subspace,
}

fn b(x: &[u8]) -> Bytes<'_> {
    Bytes::from(x)
}

impl Keys {
    pub fn new(deployment: &str) -> Keys {
        Keys { root: Subspace::from(("paralean", deployment)) }
    }
    pub fn sub(&self, kind: &str) -> Subspace {
        self.root.subspace(&(kind,))
    }
    pub fn marker(&self, g: &Id) -> Vec<u8> {
        self.root.pack(&("marker", b(&g.0)))
    }
    pub fn marker_variant(&self, g: &Id, marker: &Id) -> Vec<u8> { self.root.pack(&("mvariant", b(&g.0), b(&marker.0))) }
    pub fn marker_variants_of(&self, g: &Id) -> Subspace { self.root.subspace(&("mvariant", b(&g.0))) }
    pub fn variant_cert(&self, g: &Id, marker: &Id, writer: &WorkspaceId) -> Vec<u8> { self.root.pack(&("vcer", b(&g.0), b(&marker.0), b(&writer.0))) }
    pub fn variant_certs_of(&self, g: &Id) -> Subspace { self.root.subspace(&("vcer", b(&g.0))) }
    pub fn revision(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("revision", b(&id.0)))
    }
    pub fn receipt(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("receipt", b(&id.0)))
    }
    pub fn tombstone(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("tombstone", b(&id.0)))
    }
    pub fn agent_key(&self, agent: &AgentId, public: &[u8; 32]) -> Vec<u8> {
        self.root.pack(&("agent", b(&agent.0), b(public)))
    }
    pub fn agent_revoke(&self, public: &[u8; 32]) -> Vec<u8> {
        self.root.pack(&("arevoke", b(public)))
    }
    pub fn delete_grant(&self, tombstone: &Id) -> Vec<u8> {
        self.root.pack(&("deletegrant", b(&tombstone.0)))
    }
    pub fn group_chunks(&self, id: &Id) -> Vec<u8> { self.root.pack(&("gchunks", b(&id.0))) }
    pub fn cert(&self, g: &Id, w: &WorkspaceId) -> Vec<u8> {
        self.root.pack(&("cert", b(&g.0), b(&w.0)))
    }
    pub fn certs_of(&self, g: &Id) -> Subspace {
        self.root.subspace(&("cert", b(&g.0)))
    }
    pub fn tcert(&self, t: &Id, w: &WorkspaceId) -> Vec<u8> {
        self.root.pack(&("tcert", b(&t.0), b(&w.0)))
    }
    pub fn tcerts_of(&self, t: &Id) -> Subspace {
        self.root.subspace(&("tcert", b(&t.0)))
    }
    /// Evidence kept by an anti-entropy receiver: another deployment's verified certificate
    /// (`kind` is `cert` or `tcert`), never read as a certificate of this deployment.
    pub fn xcert(&self, kind: &str, object: &Id, replica: &[u8], w: &WorkspaceId) -> Vec<u8> {
        self.root.pack(&("xcert", kind, b(&object.0), b(replica), b(&w.0)))
    }
    pub fn target(&self, name: &Name) -> Vec<u8> {
        self.root.pack(&("target", b(&name.to_pce())))
    }
    pub fn assign(&self, name: &Name, epoch: u64) -> Vec<u8> {
        self.root.pack(&("assign", b(&name.to_pce()), epoch))
    }
    pub fn catalog(&self, c: &Id) -> Vec<u8> {
        self.root.pack(&("catalog", b(&c.0)))
    }
    pub fn rcert(&self, c: &Id) -> Vec<u8> {
        self.root.pack(&("rcert", b(&c.0)))
    }
    pub fn ocert(&self, kind: Kind, id: &Id) -> Vec<u8> {
        self.root.pack(&("ocert", kind.name(), b(&id.0)))
    }
    pub fn fence(&self) -> Vec<u8> {
        self.root.pack(&("fence",))
    }
    pub fn token(&self, rank: u64) -> Vec<u8> {
        self.root.pack(&("token", rank))
    }
    pub fn token_request(&self, request: &[u8]) -> Vec<u8> {
        self.root.pack(&("treq", b(request)))
    }
    pub fn assign_request(&self, name: &Name, request: &[u8]) -> Vec<u8> {
        self.root.pack(&("areq", b(&name.to_pce()), b(request)))
    }
}

// ---------------------------------------------------------------- value envelope

/// Value of an object key: `0x00 ‖ stored bytes`, or, for values over `INLINE_LIMIT`,
/// `0x01 ‖ object ID ‖ blob ID` where the blob (domain `v0/blob`, in S3) holds the stored
/// bytes. The object's ID never depends on where its bytes live.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Envelope {
    Inline(Vec<u8>),
    Blob { object: Id, blob: Id },
}

impl Envelope {
    pub fn encode(&self) -> Vec<u8> {
        match self {
            Envelope::Inline(v) => {
                let mut o = Vec::with_capacity(v.len() + 1);
                o.push(0);
                o.extend_from_slice(v);
                o
            }
            Envelope::Blob { object, blob } => {
                let mut o = vec![1];
                o.extend_from_slice(&object.0);
                o.extend_from_slice(&blob.0);
                o
            }
        }
    }
    pub fn decode(v: &[u8]) -> Result<Envelope> {
        match v.first() {
            Some(0) => Ok(Envelope::Inline(v[1..].to_vec())),
            Some(1) if v.len() == 65 => Ok(Envelope::Blob {
                object: Id(v[1..33].try_into().unwrap()),
                blob: Id(v[33..65].try_into().unwrap()),
            }),
            _ => Err(StoreError::Invalid("bad value envelope".into())),
        }
    }
}

/// The stored bytes of an unsigned object, wrapped for a blob if needed. Returns the
/// envelope and the blob preimage that must be acknowledged by S3 first.
pub fn envelope_for(object: Id, stored: Vec<u8>) -> (Envelope, Option<Vec<u8>>) {
    if stored.len() <= INLINE_LIMIT {
        (Envelope::Inline(stored), None)
    } else {
        let blob = Opaque::new(Kind::Blob, stored);
        (Envelope::Blob { object, blob: blob.id() }, Some(blob.preimage()))
    }
}

/// ID of the unsigned object held in an envelope.
pub fn envelope_object_id(v: &[u8]) -> Result<Id> {
    Ok(match Envelope::decode(v)? {
        Envelope::Inline(s) => Id(sha256(&s)),
        Envelope::Blob { object, .. } => object,
    })
}


/// How an object key's value is laid out. Unsigned objects (markers, revisions,
/// tombstones) use the envelope; signed objects (receipts, catalogue records, certificates)
/// are small and stored as their `Signed` bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
    Envelope,
    SignedRecord,
}

impl ValueKind {
    pub fn object_id(self, v: &[u8]) -> Result<Id> {
        match self {
            ValueKind::Envelope => envelope_object_id(v),
            ValueKind::SignedRecord => Ok(SignedRecord::from_bytes(v)?.id()),
        }
    }
}

fn enc_u64(n: u64) -> Vec<u8> {
    let mut e = Enc::new();
    e.uvarint(n);
    e.out
}
fn dec_u64(v: &[u8]) -> Result<u64> {
    let mut d = Dec::new(v);
    let n = d.uvarint()?;
    d.end()?;
    Ok(n)
}

// ---------------------------------------------------------------- transaction loop

pub(crate) enum Step<T> {
    /// The effect is already present (or the transaction is read-only): nothing to commit.
    Done(T),
    /// Commit the writes made in the body; `T` is returned once the commit is known.
    Commit(T),
}

type Body<T> = Box<dyn for<'t> Fn(&'t Transaction) -> BoxFuture<'t, Result<Step<T>>> + Send + Sync>;

#[derive(Clone)]
pub struct Meta {
    pub db: Arc<Database>,
    pub keys: Keys,
    pub faults: Arc<Faults>,
    pub max_attempts: usize,
}

pub(crate) async fn get(trx: &Transaction, key: &[u8]) -> Result<Option<Vec<u8>>> {
    Ok(trx.get(key, false).await?.map(|v| v.to_vec()))
}

/// Admission is checked in the mutation transaction. A controller-signed grant in the
/// configured key file may bootstrap its FDB slot, but the claimed author alone never does.
pub(crate) async fn active_agent_key(
    trx: &Transaction, k: &Keys, ring: &crate::sign::KeyRing,
    agent: AgentId, workspace: WorkspaceId, public: [u8; 32],
) -> Result<()> {
    active_agent_key_from(trx, k, ring, agent, workspace, public, ring.authority).await
}

async fn active_agent_key_from(
    trx: &Transaction, k: &Keys, ring: &crate::sign::KeyRing,
    agent: AgentId, workspace: WorkspaceId, public: [u8; 32], expected_issuer: [u8; 32],
) -> Result<()> {
    let configured = ring.agent_keys.iter().find(|grant| {
        grant.parts().is_some_and(|(a, w, p, issuer)|
            a == agent && w == workspace && p == public &&
            (issuer == expected_issuer || cfg!(feature = "mutate-agent-foreign-rotation")) && grant.verify())
    });
    let key = k.agent_key(&agent, &public);
    let stored = get(trx, &key).await?;
    match (stored, configured) {
        (Some(bytes), _) => {
            let persisted: crate::authority::AgentKeyGrant = serde_json::from_slice(&bytes)
                .map_err(|_| GuardFailure::AgentKeyNotRegistered(agent.hex()))?;
            if !persisted.parts().is_some_and(|(a, w, p, issuer)| a == agent && w == workspace && p == public &&
                (issuer == expected_issuer || cfg!(feature = "mutate-agent-foreign-rotation")) && persisted.verify()) {
                return Err(GuardFailure::AgentKeyNotRegistered(agent.hex()).into());
            }
        }
        (None, Some(grant)) => trx.set(&key, &grant.encoded()),
        (None, None) => return Err(GuardFailure::AgentKeyNotRegistered(agent.hex()).into()),
    }
    if !cfg!(feature = "mutate-agent-no-revocation") && get(trx, &k.agent_revoke(&public)).await?.is_some() {
        return Err(GuardFailure::AgentKeyRevoked(public).into());
    }
    Ok(())
}

pub(crate) async fn range(trx: &Transaction, begin: Vec<u8>, end: Vec<u8>, limit: usize) -> Result<FdbValues> {
    let opt = RangeOption {
        limit: Some(limit),
        mode: StreamingMode::WantAll,
        ..RangeOption::from((KeySelector::first_greater_or_equal(begin), KeySelector::first_greater_or_equal(end)))
    };
    Ok(trx.get_range(&opt, 1, false).await?)
}

impl Meta {
    pub fn open(cluster_file: Option<&str>, deployment: &str, faults: Arc<Faults>) -> Result<Meta> {
        boot();
        let db = Database::new(cluster_file)?;
        Ok(Meta { db: Arc::new(db), keys: Keys::new(deployment), faults, max_attempts: 60 })
    }

    pub fn with_faults(&self, faults: Arc<Faults>) -> Meta {
        Meta { faults, ..self.clone() }
    }

    /// Run an idempotent transaction body to a known outcome.
    pub(crate) async fn run<T: Send>(&self, txn: Txn, body: Body<T>) -> Result<T> {
        let mut last = String::new();
        let mut trx = self.db.create_trx()?;
        for _attempt in 0..self.max_attempts {
            let step = body(&trx).await;
            let out = match step {
                Ok(Step::Done(v)) => return Ok(v),
                Ok(Step::Commit(v)) => v,
                Err(StoreError::Fdb(e)) => {
                    last = e.to_string();
                    self.faults.count("fdb-retry");
                    trx = trx.on_error(e).await?;
                    continue;
                }
                Err(e) => return Err(e), // guard failure or decode error: nothing written
            };
            match self.faults.commit_fault(txn) {
                CommitFault::None => {}
                CommitFault::UnknownNotCommitted => {
                    self.faults.count("unknown-result-resolved");
                    last = "injected commit_unknown_result (not committed)".into();
                    drop(trx.cancel());
                    trx = self.db.create_trx()?;
                    continue;
                }
                CommitFault::UnknownCommitted => {
                    match trx.commit().await {
                        Ok(_) => {}
                        Err(e) => {
                            // The injected rule was consumed, but a real FDB error won
                            // before its simulated committed outcome could be resolved.
                            self.faults.count("injected-commit-real-error");
                            if e.is_maybe_committed() {
                                self.faults.count("real-commit-unknown-result");
                            } else {
                                self.faults.count("fdb-retry");
                            }
                            last = e.to_string();
                            trx = e.on_error().await?;
                            continue;
                        }
                    }
                    self.faults.count("unknown-result-resolved");
                    last = "injected commit_unknown_result (committed)".into();
                    trx = self.db.create_trx()?;
                    continue;
                }
                CommitFault::Interleave(hook) => hook().await,
                CommitFault::UnknownThen { committed, hook } => {
                    if committed {
                        match trx.commit().await {
                            Ok(_) => {}
                            Err(e) => {
                                self.faults.count("injected-commit-real-error");
                                if e.is_maybe_committed() {
                                    self.faults.count("real-commit-unknown-result");
                                } else {
                                    self.faults.count("fdb-retry");
                                }
                                last = e.to_string();
                                trx = e.on_error().await?;
                                continue;
                            }
                        }
                    } else {
                        drop(trx.cancel());
                    }
                    hook().await;
                    self.faults.count("unknown-result-resolved");
                    last = format!("injected commit_unknown_result (committed: {committed})");
                    trx = self.db.create_trx()?;
                    continue;
                }
                CommitFault::CrashBeforeCommit => {
                    drop(trx.cancel());
                    return Err(self.faults.crash(&format!("{txn:?}:before-commit")));
                }
                CommitFault::CrashAfterCommit => {
                    let _ = trx.commit().await;
                    return Err(self.faults.crash(&format!("{txn:?}:after-commit")));
                }
            }
            match trx.commit().await {
                Ok(_) => return Ok(out),
                Err(e) => {
                    if e.is_maybe_committed() {
                        self.faults.count("real-commit-unknown-result");
                    } else {
                        self.faults.count("fdb-retry");
                    }
                    last = e.to_string();
                    // Retryable (not_committed, commit_unknown_result, ...): the body re-reads
                    // its effect and guards. Otherwise on_error returns the error.
                    trx = e.on_error().await?;
                }
            }
        }
        Err(StoreError::Unresolved { attempts: self.max_attempts, last })
    }

    /// A read-only transaction (linearizable reads at a fresh read version).
    pub async fn read<T: Send + 'static>(
        &self,
        f: impl for<'t> Fn(&'t Transaction) -> BoxFuture<'t, Result<T>> + Send + Sync + 'static,
    ) -> Result<T> {
        let mut trx = self.db.create_trx()?;
        loop {
            match f(&trx).await {
                Ok(v) => return Ok(v),
                Err(StoreError::Fdb(e)) => trx = trx.on_error(e).await?,
                Err(e) => return Err(e),
            }
        }
    }

    pub async fn get(&self, key: Vec<u8>) -> Result<Option<Vec<u8>>> {
        self.read(move |trx| {
            let key = key.clone();
            Box::pin(async move { get(trx, &key).await })
        })
        .await
    }

    /// Paginated scan of a subspace: one transaction per page, each at its own read
    /// version. Correct as a model scan because the scanned key spaces only grow (store.md
    /// "Physical scan and enumeration"). `between` runs after each page (tests interleave
    /// concurrent writes there).
    pub async fn scan(
        &self,
        sub: &Subspace,
        page: usize,
        mut between: impl FnMut(usize) -> Option<BoxFuture<'static, ()>>,
    ) -> Result<Vec<(Vec<u8>, Vec<u8>)>> {
        let (mut begin, end) = sub.range();
        let mut out = Vec::new();
        let mut n = 0;
        loop {
            let (b0, e0) = (begin.clone(), end.clone());
            // One batch per transaction. FDB may return fewer than `page` pairs (byte
            // limits) while more remain: continue on `more()`, never on the batch size.
            let (kvs, more): (Vec<(Vec<u8>, Vec<u8>)>, bool) = self
                .read(move |trx| {
                    let (b0, e0) = (b0.clone(), e0.clone());
                    Box::pin(async move {
                        let r = range(trx, b0, e0, page).await?;
                        Ok((r.iter().map(|kv| (kv.key().to_vec(), kv.value().to_vec())).collect(), r.more()))
                    })
                })
                .await?;
            if let Some(last) = kvs.last() {
                begin = last.0.clone();
                begin.push(0);
            }
            let empty = kvs.is_empty();
            out.extend(kvs);
            n += 1;
            if !more || empty {
                return Ok(out);
            }
            if let Some(f) = between(n) {
                f.await;
            }
        }
    }

    pub async fn fence(&self) -> Result<u64> {
        Ok(match self.get(self.keys.fence()).await? {
            None => 0,
            Some(v) => dec_u64(&v)?,
        })
    }

    /// Controller registration/rotation. The key slot is immutable; old keys remain
    /// historical evidence until separately revoked for new author writes.
    pub async fn register_agent_key(&self, grant: crate::authority::AgentKeyGrant, authority: [u8; 32]) -> Result<bool> {
        let (_, _, public, issuer) = grant.parts().ok_or_else(|| StoreError::Invalid("bad agent key registration".into()))?;
        if issuer != authority || !grant.verify() { return Err(StoreError::Invalid("agent key registration lacks controller signature".into())); }
        let agent = crate::id::AgentId::from_hex(&grant.agent).expect("validated above");
        let key = self.keys.agent_key(&agent, &public);
        let bytes = Arc::new(grant.encoded());
        self.run(Txn::AgentAuthority, Box::new(move |trx| {
            let (key, bytes) = (key.clone(), bytes.clone());
            Box::pin(async move {
                match get(trx, &key).await? {
                    Some(old) if old == *bytes => Ok(Step::Done(false)),
                    Some(_) => Err(StoreError::Invalid("agent key slot holds another grant".into())),
                    None => { trx.set(&key, &bytes); Ok(Step::Commit(true)) }
                }
            })
        })).await
    }

    /// Read-only view of `active_agent_key`'s admission rule for schedulers and
    /// editors: whether a controller grant binds `agent` to `public` for
    /// `workspace` (persisted, or configured and still bootstrappable), and
    /// whether that key is revoked. Admission itself is still decided in T1/T8.
    pub async fn agent_key_state(
        &self, ring: &crate::sign::KeyRing, agent: AgentId, workspace: WorkspaceId, public: [u8; 32],
    ) -> Result<(bool, bool)> {
        let (slot, revoke) = (self.keys.agent_key(&agent, &public), self.keys.agent_revoke(&public));
        let ring = ring.clone();
        self.read(move |trx| {
            let (slot, revoke, ring) = (slot.clone(), revoke.clone(), ring.clone());
            Box::pin(async move {
                let matches = |grant: &crate::authority::AgentKeyGrant| grant.parts().is_some_and(|(a, w, p, issuer)|
                    a == agent && w == workspace && p == public && issuer == ring.authority) && grant.verify();
                let registered = match get(trx, &slot).await? {
                    Some(bytes) => serde_json::from_slice::<crate::authority::AgentKeyGrant>(&bytes)
                        .is_ok_and(|grant| matches(&grant)),
                    None => ring.agent_keys.iter().any(matches),
                };
                Ok((registered, get(trx, &revoke).await?.is_some()))
            })
        })
        .await
    }

    /// Revocation is grow-only and conflicts with T1/T8/T10 reads of this key.
    pub async fn revoke_agent_key(&self, revocation: crate::authority::AgentKeyRevocation, authority: [u8; 32]) -> Result<bool> {
        if !revocation.verify(&authority) { return Err(StoreError::Invalid("agent key revocation lacks controller signature".into())); }
        let public = revocation.public().expect("validated above");
        let key = self.keys.agent_revoke(&public);
        let bytes = Arc::new(revocation.encoded());
        self.run(Txn::AgentAuthority, Box::new(move |trx| {
            let (key, bytes) = (key.clone(), bytes.clone());
            Box::pin(async move {
                match get(trx, &key).await? {
                    Some(old) if old == *bytes => Ok(Step::Done(false)),
                    Some(_) => Err(StoreError::Invalid("agent key already revoked with another record".into())),
                    None => { trx.set(&key, &bytes); Ok(Step::Commit(true)) }
                }
            })
        })).await
    }

    pub async fn target(&self, name: &Name) -> Result<Option<TargetRecord>> {
        Ok(match self.get(self.keys.target(name)).await? {
            None => None,
            Some(v) => Some(TargetRecord::from_pce(&v)?),
        })
    }

    // ============================================================ T1 publish

    pub(crate) async fn t1_publish(&self, a: Arc<PublishArgs>) -> Result<PublishOutcome> {
        let k = self.keys.clone();
        self.run(
            Txn::T1Publish,
            Box::new(move |trx| {
                let (k, a) = (k.clone(), a.clone());
                Box::pin(async move { t1_body(trx, &k, &a).await })
            }),
        )
        .await
    }

    // ============================================================ T2 certify

    pub(crate) async fn t2_certify(&self, group: Id, writer: WorkspaceId, marker: Id, cert: Vec<u8>) -> Result<bool> {
        let k = self.keys.clone();
        let cert = Arc::new(cert);
        self.run(
            Txn::T2Certify,
            Box::new(move |trx| {
                let (k, cert) = (k.clone(), cert.clone());
                Box::pin(async move {
                    let ck = k.cert(&group, &writer);
                    if get(trx, &ck).await?.is_some() {
                        return Ok(Step::Done(false));
                    }
                    let Some(mv) = get(trx, &k.marker(&group)).await? else {
                        return Err(GuardFailure::NotPublished(group).into());
                    };
                    if envelope_object_id(&mv)? != marker {
                        return Err(GuardFailure::BadPackage("certificate names another marker".into()).into());
                    }
                    // Knowing the group as published means a live certificate exists (§8.3);
                    // a raw marker key is not evidence.
                    let (b0, e0) = k.certs_of(&group).range();
                    if range(trx, b0, e0, 1).await?.is_empty() {
                        return Err(GuardFailure::Uncertified(group).into());
                    }
                    trx.set(&ck, &cert);
                    let cert_id = Cert::from_bytes(&cert)?.id();
                    append_event(trx, &k, &AeKind::Evidence { kind: "cert".into(), object: group, cert: cert_id }, 0);
                    Ok(Step::Commit(true))
                })
            }),
        )
        .await
    }

    /// Mutation support only (`mutate-cert-outside-publish`): write a certificate with no
    /// guard, as the lagging design's separate certificate transaction.
    #[cfg(feature = "mutate-cert-outside-publish")]
    pub(crate) async fn t2_raw_cert(&self, group: Id, writer: WorkspaceId, cert: Vec<u8>) -> Result<bool> {
        let key = self.keys.cert(&group, &writer);
        let cert = Arc::new(cert);
        self.run(
            Txn::T2Certify,
            Box::new(move |trx| {
                let (key, cert) = (key.clone(), cert.clone());
                Box::pin(async move {
                    trx.set(&key, &cert);
                    Ok(Step::Commit(true))
                })
            }),
        )
        .await
    }
    #[cfg(not(feature = "mutate-cert-outside-publish"))]
    pub(crate) async fn t2_raw_cert(&self, _: Id, _: WorkspaceId, _: Vec<u8>) -> Result<bool> {
        unreachable!()
    }

    // ============================================================ T3 rotate

    /// Read-modify-write of `fence` (never an atomic add), writing `token/<k+1>` and the
    /// request index `treq/<request>`. The index makes the effect recognisable by request
    /// ID for any retry, including a late duplicate after other rotations.
    pub(crate) async fn t3_rotate(&self, request: Vec<u8>, holder: WorkspaceId, signer: crate::sign::Signer) -> Result<TokenRef> {
        let k = self.keys.clone();
        let request = Arc::new(request);
        self.run(
            Txn::T3Rotate,
            Box::new(move |trx| {
                let (k, request, signer) = (k.clone(), request.clone(), signer.clone());
                Box::pin(async move {
                    if let Some(v) = get(trx, &k.token_request(&request)).await? {
                        let rank = dec_u64(&v)?;
                        let e = TokenEntry::from_pce(&get(trx, &k.token(rank)).await?.ok_or_else(|| {
                            StoreError::Invalid(format!("request index names missing token {rank}"))
                        })?)?;
                        return Ok(Step::Done(e.token.body.token));
                    }
                    let fence = match get(trx, &k.fence()).await? {
                        None => 0,
                        Some(v) => dec_u64(&v)?,
                    };
                    let token = TokenRef { rank: fence + 1, holder };
                    let entry = TokenEntry { token: Token::sign(TokenBody { token }, &signer), request: (*request).clone() };
                    trx.set(&k.fence(), &enc_u64(fence + 1));
                    trx.set(&k.token(fence + 1), &entry.to_pce());
                    trx.set(&k.token_request(&request), &enc_u64(fence + 1));
                    Ok(Step::Commit(token))
                })
            }),
        )
        .await
    }

    // ============================================================ T4 reassign

    /// Assign (create) or reassign a target name: `owner := new`, `epoch := epoch + 1`,
    /// `head` unchanged. The record stores the last request ID (store.md); the grow-only
    /// `assign/<name>/<epoch>` log and the index `areq/<name>/<request>` make the effect
    /// recognisable for any retry, so a late duplicate never reverts a newer reassignment.
    pub(crate) async fn t4_reassign(&self, name: Name, owner: WorkspaceId, request: Vec<u8>) -> Result<u64> {
        let k = self.keys.clone();
        let (name, request) = (Arc::new(name), Arc::new(request));
        self.run(
            Txn::T4Reassign,
            Box::new(move |trx| {
                let (k, name, request) = (k.clone(), name.clone(), request.clone());
                Box::pin(async move {
                    if let Some(cfg) = config_in_txn(trx, &k).await? {
                        if cfg.target_homes.get(name.as_ref()).map(String::as_str) != Some(cfg.deployment.as_str()) {
                            return Err(GuardFailure::ForeignTarget((*name).clone()).into());
                        }
                    }
                    if let Some(v) = get(trx, &k.assign_request(&name, &request)).await? {
                        return Ok(Step::Done(dec_u64(&v)?));
                    }
                    let tk = k.target(&name);
                    let cur = get(trx, &tk).await?.map(|v| TargetRecord::from_pce(&v)).transpose()?;
                    let next = cur.as_ref().map(|r| r.epoch + 1).unwrap_or(0);
                    let rec = TargetRecord {
                        name: (*name).clone(),
                        owner,
                        epoch: next,
                        head: cur.and_then(|r| r.head),
                        last_request: (*request).clone(),
                    };
                    trx.set(&tk, &rec.to_pce());
                    trx.set(&k.assign(&name, next), &AssignEntry { owner, request: (*request).clone() }.to_pce());
                    trx.set(&k.assign_request(&name, &request), &enc_u64(next));
                    Ok(Step::Commit(next))
                })
            }),
        )
        .await
    }

    // ============================================================ T5 catalogue

    /// Fenced write of a catalogue record and its commit certificate in one transaction.
    pub(crate) async fn t5_commit(&self, a: Arc<CommitArgs>) -> Result<bool> {
        let k = self.keys.clone();
        self.run(
            Txn::T5Commit,
            Box::new(move |trx| {
                let (k, a) = (k.clone(), a.clone());
                Box::pin(async move { t5_body(trx, &k, &a, true).await })
            }),
        )
        .await
    }

    /// Fenced first write of a catalogue record without its commit certificate (staging).
    /// If the record's bytes are already present the call succeeds without writing: an
    /// acknowledgement of existing bytes is unconditional (CatalogFencing).
    pub(crate) async fn t5_stage(&self, a: Arc<CommitArgs>) -> Result<bool> {
        let k = self.keys.clone();
        self.run(
            Txn::T5Stage,
            Box::new(move |trx| {
                let (k, a) = (k.clone(), a.clone());
                Box::pin(async move { t5_body(trx, &k, &a, false).await })
            }),
        )
        .await
    }

    // ============================================================ T6 object certificate

    pub(crate) async fn t6_object(&self, kind: Kind, id: Id, value: Vec<u8>) -> Result<bool> {
        let key = self.keys.ocert(kind, &id);
        let keys = self.keys.clone();
        let value = Arc::new(value);
        self.run(
            Txn::T6ObjectCert,
            Box::new(move |trx| {
                let (key, value, keys) = (key.clone(), value.clone(), keys.clone());
                Box::pin(async move {
                    // Snapshot read: any writer's certificate suffices, and concurrent
                    // certifiers need not conflict.
                    if trx.get(&key, true).await?.is_some() {
                        return Ok(Step::Done(false));
                    }
                    trx.set(&key, &value);
                    let cert_id = ObjectCert::from_bytes(&value)?.id();
                    append_event(trx, &keys, &AeKind::Evidence { kind: format!("ocert/{}", kind.name()), object: id, cert: cert_id }, 0);
                    Ok(Step::Commit(true))
                })
            }),
        )
        .await
    }

    // ============================================================ T7 repair

    /// Unconditional, unfenced copy of an existing certificate. `requires` is the key whose
    /// presence shows the certified object's bytes already exist here (marker or record);
    /// object certificates are checked against S3 by the caller.
    pub(crate) async fn t7_repair(&self, key: Vec<u8>, value: Vec<u8>, requires: Option<(Vec<u8>, Id, ValueKind)>) -> Result<bool> {
        let (key, value, requires) = (Arc::new(key), Arc::new(value), Arc::new(requires));
        self.run(
            Txn::T7Repair,
            Box::new(move |trx| {
                let (key, value, requires) = (key.clone(), value.clone(), requires.clone());
                Box::pin(async move {
                    if get(trx, &key).await?.is_some() {
                        return Ok(Step::Done(false));
                    }
                    if let Some((rk, rid, vk)) = requires.as_ref() {
                        match get(trx, rk).await? {
                            Some(v) if vk.object_id(&v)? == *rid => {}
                            _ => return Err(GuardFailure::RepairNoExistingBytes.into()),
                        }
                    }
                    trx.set(&key, &value);
                    Ok(Step::Commit(true))
                })
            }),
        )
        .await
    }

    // ============================================================ T11 move position

    /// Certify a new placement of an existing group after the old placement was
    /// tombstoned. The registry marker and revisions stay unchanged.
    pub(crate) async fn t11_move_position(&self, marker: Marker, old_marker: Marker, anchor_marker: Option<Marker>, old: Tombstone,
        value: Vec<u8>, cert: Vec<u8>, writer: WorkspaceId, ring: Arc<crate::sign::KeyRing>) -> Result<bool> {
        let k = self.keys.clone();
        let marker = Arc::new(marker);
        let old_marker = Arc::new(old_marker);
        let anchor_marker = Arc::new(anchor_marker);
        let old = Arc::new(old);
        let value = Arc::new(value);
        let cert = Arc::new(cert);
        self.run(Txn::T11MovePosition, Box::new(move |trx| {
            let (k, marker, old_marker, anchor_marker, old, value, cert, ring) =
                (k.clone(), marker.clone(), old_marker.clone(), anchor_marker.clone(), old.clone(), value.clone(), cert.clone(), ring.clone());
            Box::pin(async move {
                let g = marker.group;
                let mid = marker.id();
                let vk = k.marker_variant(&g, &mid);
                let ck = k.variant_cert(&g, &mid, &writer);
                if let Some(v) = get(trx, &vk).await? {
                    if envelope_object_id(&v)? == mid {
                        if let Some(bytes) = get(trx, &ck).await? {
                            let prior = Cert::from_bytes(&bytes)?;
                            if prior.body.group == g && prior.body.marker == mid && prior.body.writer == writer
                                && ring.verify_writer(&writer, &prior.id(), &prior.sig) {
                                return Ok(Step::Done(false));
                            }
                        }
                    }
                    return Err(GuardFailure::BadPackage("move position already occupied".into()).into());
                }
                let certificate = Cert::from_bytes(&cert)?;
                let public = *ring.writer(&writer).ok_or_else(|| GuardFailure::AgentKeyNotRegistered(marker.author.hex()))?;
                if certificate.body.group != g || certificate.body.marker != mid || certificate.body.writer != writer
                    || !certificate.verify(&public) {
                    return Err(GuardFailure::BadPackage("move certificate does not bind writer".into()).into());
                }
                if !cfg!(feature = "mutate-no-agent-registry") {
                    active_agent_key(trx, &k, &ring, marker.author, writer, public).await?;
                }
                let base = get(trx, &k.marker(&g)).await?.ok_or(GuardFailure::NotPublished(g))?;
                let base_id = envelope_object_id(&base)?;
                let (b0, e0) = k.certs_of(&g).range();
                if range(trx, b0, e0, 1).await?.is_empty() { return Err(GuardFailure::Uncertified(g).into()); }
                // A move needs certified deletion of an exact position. The old
                // tombstone must have committed before this transaction.
                let old_pos = old.position.ok_or_else(|| GuardFailure::BadPackage("move requires position tombstone".into()))?;
                if old_marker.id() != old_pos || old_marker.group != g ||
                    (!cfg!(feature = "mutate-position-lineage") &&
                        (marker.revisions != old_marker.revisions || marker.receipt != old_marker.receipt ||
                            marker.lineage_keys != old_marker.lineage_keys)) || marker.author != old_marker.author {
                    return Err(GuardFailure::BadPackage("move changed lineage".into()).into());
                }
                if old.target != g || (!cfg!(feature = "mutate-position-cross-file") && old.file_path != marker.file_path) || old_pos == mid
                    || marker.lamport <= old.lamport || (!cfg!(feature = "mutate-position-author") && old.author != marker.author) {
                    return Err(GuardFailure::BadPackage("move lineage or Lamport order differs".into()).into());
                }
                let old_key = if old_pos == base_id { k.marker(&g) } else { k.marker_variant(&g, &old_pos) };
                let old_value = get(trx, &old_key).await?.ok_or(GuardFailure::NotPublished(g))?;
                if envelope_object_id(&old_value)? != old_pos { return Err(GuardFailure::BadPackage("old position differs".into()).into()); }
                let old_stored = get(trx, &k.tombstone(&old.id())).await?.ok_or_else(|| GuardFailure::BadPackage("move tombstone absent".into()))?;
                if !cfg!(feature = "mutate-position-no-tombstone-guard") &&
                    (envelope_object_id(&old_stored)? != old.id() || get(trx, &k.tcert(&old.id(), &writer)).await?.is_none()) {
                    return Err(GuardFailure::BadPackage("move tombstone uncertified".into()).into());
                }
                // The supplied old marker is bound to its immutable store ID above.
                if !cfg!(feature = "mutate-position-bad-root") &&
                    (marker.root_path.last() != Some(&(g, marker.lamport, marker.author))
                        || (matches!(marker.anchor, Anchor::FileStart) && marker.root_path.len() != 1)) {
                    return Err(GuardFailure::BadPackage("move root path does not end at new position".into()).into());
                }
                if !cfg!(feature = "mutate-position-no-anchor") { match (&marker.anchor, anchor_marker.as_ref()) {
                    (Anchor::FileStart, None) => {}
                    (Anchor::After(anchor_group), Some(anchor)) if anchor.group == *anchor_group
                        && anchor.file_path == marker.file_path && anchor.group != g
                        && marker.root_path.len() == anchor.root_path.len() + 1
                        && marker.root_path[..anchor.root_path.len()] == anchor.root_path => {
                        let anchor_base = get(trx, &k.marker(anchor_group)).await?.map(|v| envelope_object_id(&v)).transpose()?;
                        let key = if anchor_base == Some(anchor.id()) { k.marker(anchor_group) }
                            else { k.marker_variant(anchor_group, &anchor.id()) };
                        let stored = get(trx, &key).await?.ok_or(GuardFailure::NotPublished(*anchor_group))?;
                        if envelope_object_id(&stored)? != anchor.id() {
                            return Err(GuardFailure::BadPackage("move anchor marker changed".into()).into());
                        }
                        let (b, e) = if anchor_base == Some(anchor.id()) { k.certs_of(anchor_group).range() }
                            else { k.root.subspace(&("vcer", b(&anchor_group.0), b(&anchor.id().0))).range() };
                        if range(trx, b, e, 1).await?.is_empty() { return Err(GuardFailure::Uncertified(*anchor_group).into()); }
                    }
                    _ => return Err(GuardFailure::BadPackage("move anchor path differs".into()).into()),
                }}
                trx.set(&vk, &value);
                trx.set(&ck, &cert);
                append_event(trx, &k, &AeKind::GroupVariant { group: g, marker: mid, cert: certificate.id() }, 0);
                Ok(Step::Commit(true))
            })
        })).await
    }

    // ============================================================ T8 tombstone

    /// Publish a tombstone (§11.4): the tombstone key and the publisher's tombstone
    /// certificate in one transaction, as T1 does for markers, conditional on the target
    /// being published and certified here and on the tombstone being a valid deletion of it.
    pub(crate) async fn t8_tombstone(&self, a: Arc<TombstoneArgs>) -> Result<bool> {
        let k = self.keys.clone();
        self.run(
            Txn::T8Tombstone,
            Box::new(move |trx| {
                let (k, a) = (k.clone(), a.clone());
                Box::pin(async move { t8_body(trx, &k, &a).await })
            }),
        )
        .await
    }

    /// Mutation support only (`mutate-tombstone-cert-outside`): the tombstone certificate in
    /// a later transaction of its own.
    #[cfg(feature = "mutate-tombstone-cert-outside")]
    pub(crate) async fn t8_raw_cert(&self, key: Vec<u8>, cert: Vec<u8>) -> Result<bool> {
        let (key, cert) = (Arc::new(key), Arc::new(cert));
        self.run(
            Txn::T8Tombstone,
            Box::new(move |trx| {
                let (key, cert) = (key.clone(), cert.clone());
                Box::pin(async move {
                    trx.set(&key, &cert);
                    Ok(Step::Commit(true))
                })
            }),
        )
        .await
    }

    // ============================================================ T9/T10 receive

    /// Anti-entropy receive of a group published at another deployment. Writes the marker,
    /// revisions and receipt if absent, this deployment's receiver certificate and the
    /// sender's verified certificates as evidence (`xcert/`), in one transaction.
    pub(crate) async fn t9_receive_group(&self, a: Arc<ReceiveGroupArgs>) -> Result<bool> {
        let k = self.keys.clone();
        self.run(
            Txn::T9ReceiveGroup,
            Box::new(move |trx| {
                let (k, a) = (k.clone(), a.clone());
                Box::pin(async move { t9_body(trx, &k, &a).await })
            }),
        )
        .await
    }

    /// Anti-entropy receive of a tombstone: T8's guards against this deployment's copy of
    /// the target, then the tombstone, this deployment's receiver certificate and evidence.
    pub(crate) async fn t10_receive_tombstone(&self, a: Arc<ReceiveTombstoneArgs>) -> Result<bool> {
        let k = self.keys.clone();
        self.run(
            Txn::T10ReceiveTombstone,
            Box::new(move |trx| {
                let (k, a) = (k.clone(), a.clone());
                Box::pin(async move { t10_body(trx, &k, &a).await })
            }),
        )
        .await
    }

    /// Test-only: write a raw key in the store's namespace (fixtures that construct states
    /// no transaction produces, e.g. a marker key without certificates).
    pub async fn raw_set(&self, key: Vec<u8>, value: Vec<u8>) -> Result<()> {
        let mut trx = self.db.create_trx()?;
        loop {
            trx.set(&key, &value);
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await?,
            }
        }
    }
}

// ---------------------------------------------------------------- T1 body

#[derive(Clone, Debug)]
pub struct PreparedTarget {
    pub name: Name,
    /// The epoch read from the target record when the proof was prepared.
    pub epoch: u64,
    /// The head read from the same record; the new revision must list it as a parent.
    pub head: Option<Id>,
}

pub(crate) struct PublishArgs {
    pub writer: WorkspaceId,
    pub group: Id,
    pub marker_id: Id,
    pub author: AgentId,
    pub marker_value: Vec<u8>,
    pub revisions: Vec<(Id, Revision, Vec<u8>)>,
    pub receipt_id: Id,
    pub receipt_value: Vec<u8>,
    pub receipt: Receipt,
    pub job: crate::receipt::SignedJob,
    pub ring: Arc<crate::sign::KeyRing>,
    pub dep_groups: Vec<Id>,
    pub replica: crate::id::ReplicaId,
    pub targets: Vec<PreparedTarget>,
    pub cert_value: Vec<u8>,
    pub chunk_index: Option<Vec<(Id, u64)>>,
}

/// Every dependency group has its marker here and a valid publication certificate on this
/// deployment's replica (T1, and T9 for a received group). Read in the caller's transaction.
async fn dependencies_published(
    trx: &Transaction, k: &Keys, deps: &[Id], ring: &crate::sign::KeyRing, replica: crate::id::ReplicaId,
) -> Result<()> {
    for dep in deps {
        let Some(mv) = get(trx, &k.marker(dep)).await? else {
            return Err(GuardFailure::NotPublished(*dep).into());
        };
        let marker = envelope_object_id(&mv)?;
        let mut certified = false;
        for writer in ring.writers.keys() {
            let Some(bytes) = get(trx, &k.cert(dep, writer)).await? else { continue };
            let Ok(cert) = Cert::from_bytes(&bytes) else { continue };
            if cert.body.group == *dep && cert.body.marker == marker &&
                cert.body.writer == *writer && cert.body.replica == replica &&
                ring.verify_writer(writer, &cert.id(), &cert.sig) {
                certified = true;
                break;
            }
        }
        if !certified { return Err(GuardFailure::Uncertified(*dep).into()) }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublishOutcome {
    pub marker: Id,
    /// False when the effect was already present (a retry after an unknown outcome).
    pub fresh: bool,
}

async fn t1_body(trx: &Transaction, k: &Keys, a: &PublishArgs) -> Result<Step<PublishOutcome>> {
    if let Some(cfg) = config_in_txn(trx, k).await? {
        let own = &cfg.members[&cfg.deployment];
        if !a.job.verify(&own.authority) && !own.job_issuers.iter().any(|key| a.job.verify(key)) {
            return Err(StoreError::Invalid("federated publication job issuer is not bound to this deployment".into()));
        }
        for (_, rev, _) in &a.revisions {
            if let Some(home) = cfg.target_homes.get(&rev.name) {
                if home != &cfg.deployment { return Err(GuardFailure::ForeignTarget(rev.name.clone()).into()); }
                if !a.targets.iter().any(|t| t.name == rev.name) { return Err(GuardFailure::UndeclaredTarget(rev.name.clone()).into()); }
            }
        }
        for target in &a.targets {
            if cfg.target_homes.get(&target.name) != Some(&cfg.deployment) {
                return Err(GuardFailure::ForeignTarget(target.name.clone()).into());
            }
        }
    }
    let mk = k.marker(&a.group);
    let ck = k.cert(&a.group, &a.writer);
    if let Some(v) = get(trx, &mk).await? {
        let existing = envelope_object_id(&v)?;
        if existing == a.marker_id && (cfg!(feature = "mutate-cert-outside-publish") || get(trx, &ck).await?.is_some()) {
            return Ok(Step::Done(PublishOutcome { marker: a.marker_id, fresh: false }));
        }
        return Err(GuardFailure::AlreadyPublished { group: a.group, existing }.into());
    }
    let cert = Cert::from_bytes(&a.cert_value)?;
    let public = *a.ring.writer(&a.writer).ok_or_else(|| GuardFailure::AgentKeyNotRegistered(a.author.hex()))?;
    if cert.body.group != a.group || cert.body.marker != a.marker_id || cert.body.writer != a.writer ||
        !cert.verify(&public) {
        return Err(GuardFailure::BadPackage("publisher certificate does not bind the claimed writer".into()).into());
    }
    if !cfg!(feature = "mutate-no-agent-registry") {
        active_agent_key(trx, k, &a.ring, a.author, a.writer, public).await?;
    }
    // P3 staging rule (receipt.rs, OPEN-7): the receipt verifies under a configured validator
    // key, is accepted, names this group, and is bound to a controller-issued envelope with
    // pinned policy and checker and exactly the prepared target names and epochs.
    if !cfg!(feature = "mutate-no-receipt-check") {
        crate::receipt::check(&a.receipt, &a.job, &a.group, &a.targets, &a.ring)?;
    }
    // A batch may validate a dependent group using an earlier accepted batch
    // receipt, before that dependency is published. T1 admits the dependent only
    // after every dependency's marker and a valid publication certificate exist.
    // This read is in the same FDB transaction as the new marker/certificate.
    dependencies_published(trx, k, &a.dep_groups, &a.ring, a.replica).await?;
    // Revocation and cancellation are read in this transaction, so a revocation or a
    // cancellation that commits first stops every later publication.
    let vkey = a.receipt.body.validator_key;
    if !cfg!(feature = "mutate-no-revocation-check") && get(trx, &k.revocation(&vkey)).await?.is_some() {
        return Err(GuardFailure::ValidatorRevoked(vkey).into());
    }
    let request = &a.job.body.request;
    if !cfg!(feature = "mutate-no-cancel-check") && get(trx, &k.job_cancel(&a.job.body.worker, request)).await?.is_some() {
        return Err(GuardFailure::JobCancelled(request.clone()).into());
    }
    // A revision of a name that has a target record must be a prepared target (TargetNames:
    // every group declaring a target name is guarded, whatever the publisher lists).
    for (_, rev, _) in &a.revisions {
        if a.targets.iter().any(|t| t.name == rev.name) || cfg!(feature = "mutate-no-undeclared-target") {
            continue;
        }
        if get(trx, &k.target(&rev.name)).await?.is_some() {
            return Err(GuardFailure::UndeclaredTarget(rev.name.clone()).into());
        }
    }
    // TargetNames PublishOk (epoch fence) and the head compare-and-swap.
    for t in &a.targets {
        let Some(v) = get(trx, &k.target(&t.name)).await? else {
            return Err(GuardFailure::NoTargetRecord(t.name.clone()).into());
        };
        let rec = TargetRecord::from_pce(&v)?;
        if rec.owner != a.writer && !cfg!(feature = "mutate-no-owner-check") {
            return Err(GuardFailure::NotOwner { name: t.name.clone() }.into());
        }
        if rec.epoch != t.epoch && !cfg!(feature = "mutate-no-epoch-fence") {
            return Err(GuardFailure::StaleEpoch { name: t.name.clone(), prepared: t.epoch, current: rec.epoch }.into());
        }
        if rec.head != t.head && !cfg!(feature = "mutate-no-head-cas") {
            return Err(GuardFailure::HeadMoved { name: t.name.clone(), prepared: t.head, current: rec.head }.into());
        }
        // W2 A-4: a pinned statement fixes what the head may prove. The job's binding (stamped
        // by the controller, and what the validator checked the group against) must carry it.
        if let Some(pin) = get(trx, &k.target_statement(&t.name)).await? {
            let bound = a.job.body.targets.iter().find(|b| b.name == t.name).map(|b| &b.statement);
            if bound != Some(&pin) && !cfg!(feature = "mutate-no-statement-pin-check") {
                return Err(GuardFailure::TargetStatement(t.name.clone()).into());
            }
        }
        let Some((_, rev, _)) = a.revisions.iter().find(|(_, r, _)| r.name == t.name) else {
            return Err(GuardFailure::MissingTargetRevision(t.name.clone()).into());
        };
        if let Some(h) = rec.head {
            if !rev.parents.contains(&h) {
                return Err(GuardFailure::NotRevisingHead(t.name.clone()).into());
            }
        }
    }
    // Admitted ancestor closure: every parent revision is already in the store.
    for (_, rev, _) in &a.revisions {
        for p in &rev.parents {
            if get(trx, &k.revision(p)).await?.is_none() {
                return Err(GuardFailure::UnknownParentRevision(*p).into());
            }
        }
    }
    // Writes: marker, revisions and receipt if absent, heads, the publisher's certificate.
    trx.set(&mk, &a.marker_value);
    for (id, _, v) in &a.revisions {
        let rk = k.revision(id);
        if trx.get(&rk, true).await?.is_none() {
            trx.set(&rk, v);
        }
    }
    let rk = k.receipt(&a.receipt_id);
    if trx.get(&rk, true).await?.is_none() {
        trx.set(&rk, &a.receipt_value);
    }
    // The envelope the receipt is bound to, so the binding can be re-checked later.
    let jk = k.job(&a.job.id());
    if trx.get(&jk, true).await?.is_none() {
        trx.set(&jk, &a.job.to_bytes());
    }
    let publisher_cert = Cert::from_bytes(&a.cert_value)?.id();
    trx.set(&k.jobproof(&a.group, &a.marker_id, &publisher_cert), &a.job.to_bytes());
    for t in &a.targets {
        let tk = k.target(&t.name);
        let mut rec = TargetRecord::from_pce(&get(trx, &tk).await?.expect("read above"))?;
        let (rid, _, _) = a.revisions.iter().find(|(_, r, _)| r.name == t.name).expect("checked above");
        rec.head = Some(*rid);
        trx.set(&tk, &rec.to_pce());
    }
    if !cfg!(feature = "mutate-cert-outside-publish") {
        trx.set(&ck, &a.cert_value);
    }
    if let Some(chunks) = &a.chunk_index {
        let mut e = Enc::new();
        e.list(chunks, |e, (id, length)| { id.encode(e); e.uvarint(*length); });
        trx.set(&k.group_chunks(&a.group), &e.finish());
    }
    append_event(trx, k, &AeKind::GroupVariant { group: a.group, marker: a.marker_id, cert: publisher_cert }, 0);
    Ok(Step::Commit(PublishOutcome { marker: a.marker_id, fresh: true }))
}

// ---------------------------------------------------------------- T8 body

pub(crate) struct TombstoneArgs {
    pub writer: WorkspaceId,
    pub tombstone: Tombstone,
    pub tombstone_id: Id,
    pub value: Vec<u8>,
    pub cert_value: Vec<u8>,
    /// The target's marker, read and verified by the writer (markers are immutable; the
    /// transaction checks that `marker/<target>` still holds this ID).
    pub target_marker: Marker,
    /// The names and workspaces of the target's revisions (read and verified by the writer).
    pub target_names: Vec<Name>,
    pub target_workspaces: Vec<WorkspaceId>,
    pub ring: Arc<crate::sign::KeyRing>,
    pub controller_grant: Option<crate::authority::ControllerDeleteGrant>,
}

/// The tombstone rules shared by T8 and the anti-entropy receive (T10). Workspaces models a
/// tombstone as a revision of its target: the target is published (its revision ancestors
/// are admitted), in the same file, and older (`ts e < ts d` for everything the author
/// knows). The deleting writer must have an active controller-signed AgentID registration,
/// or present an exact controller deletion grant at the current local fence. Received
/// historical deletions verify their grant against the certified source controller.
/// TargetNames has no deletion, so a group declaring a target name cannot be tombstoned.
pub(crate) async fn tombstone_guards(
    trx: &Transaction,
    k: &Keys,
    t: &Tombstone,
    m: &Marker,
    names: &[Name],
    workspaces: &[WorkspaceId],
    deleter: &WorkspaceId,
    deleter_public: [u8; 32],
    ring: &crate::sign::KeyRing,
    grant: Option<&crate::authority::ControllerDeleteGrant>,
    foreign_controller: bool,
    agent_issuer: [u8; 32],
) -> Result<()> {
    let g = t.target;
    if !cfg!(feature = "mutate-tombstone-no-target-check") {
        let base_key = k.marker(&g);
        let base_id = get(trx, &base_key).await?.map(|v| envelope_object_id(&v)).transpose()?;
        let marker_key = if t.position.is_some() && base_id != Some(m.id()) {
            k.marker_variant(&g, &m.id())
        } else { base_key.clone() };
        let Some(mv) = get(trx, &marker_key).await? else {
            return Err(GuardFailure::NotPublished(g).into());
        };
        if envelope_object_id(&mv)? != m.id() || m.group != g
            || t.position.is_some_and(|position| position != m.id()) {
            return Err(GuardFailure::BadPackage("tombstone target's marker differs".into()).into());
        }
        let (b0, e0) = if marker_key == base_key { k.certs_of(&g).range() }
            else { k.root.subspace(&("vcer", b(&g.0), b(&m.id().0))).range() };
        if range(trx, b0, e0, 1).await?.is_empty() {
            return Err(GuardFailure::Uncertified(g).into());
        }
    }
    if t.file_path != m.file_path {
        return Err(GuardFailure::TombstoneFileMismatch { tombstone: t.file_path.clone(), target: m.file_path.clone() }.into());
    }
    if t.lamport <= m.lamport {
        return Err(GuardFailure::TombstoneNotNewer { lamport: t.lamport, target: m.lamport }.into());
    }
    let controller = if let Some(grant) = grant {
        let issuer: [u8; 32] = hex::decode(&grant.issuer).ok().and_then(|v| v.try_into().ok())
            .ok_or(GuardFailure::ControllerDeleteDenied)?;
        if (!foreign_controller && issuer != ring.authority) ||
            (foreign_controller && issuer != ring.authority && !ring.agent_authorities.contains(&issuer)) {
            return Err(GuardFailure::ControllerDeleteDenied.into());
        }
        if !grant.verify(&t.id(), &issuer) { return Err(GuardFailure::ControllerDeleteDenied.into()); }
        if t.author != crate::authority::controller_agent_id(&issuer) {
            return Err(GuardFailure::ControllerDeleteDenied.into());
        }
        if !foreign_controller {
            let current = get(trx, &k.fence()).await?.map(|v| dec_u64(&v)).transpose()?.unwrap_or(0);
            if grant.fence != current && !cfg!(feature = "mutate-no-controller-fence") {
                return Err(GuardFailure::ControllerDeleteDenied.into());
            }
        }
        true
    } else { false };
    if !controller && (t.author != m.author || !workspaces.contains(deleter)) && !cfg!(feature = "mutate-tombstone-no-author-check") {
        return Err(GuardFailure::TombstoneNotAuthor.into());
    }
    if !cfg!(feature = "mutate-no-agent-registry") {
        let agent = if controller {
            ring.agent_keys.iter().find_map(|entry| entry.parts().and_then(|(agent, writer, public, _)|
                (writer == *deleter && public == deleter_public && entry.verify()).then_some(agent)))
                .ok_or_else(|| GuardFailure::AgentKeyNotRegistered(t.author.hex()))?
        } else { t.author };
        active_agent_key_from(trx, k, ring, agent, *deleter, deleter_public, agent_issuer).await?;
    }
    for n in names {
        if config_in_txn(trx, k).await?.as_ref().is_some_and(|cfg| cfg.target_homes.contains_key(n)) {
            return Err(GuardFailure::TombstoneOfTarget(n.clone()).into());
        }
        if get(trx, &k.target(n)).await?.is_some() {
            return Err(GuardFailure::TombstoneOfTarget(n.clone()).into());
        }
    }
    if let Some(r) = t.receipt {
        let Some(v) = get(trx, &k.receipt(&r)).await? else {
            return Err(GuardFailure::TombstoneReceiptAbsent(r).into());
        };
        // P3: a named receipt by a revoked validator admits nothing, as in T1. The read is in
        // this transaction, so a revocation that commits first stops the tombstone.
        let vkey = Receipt::from_bytes(&v)?.body.validator_key;
        if !cfg!(feature = "mutate-no-revocation-check") && get(trx, &k.revocation(&vkey)).await?.is_some() {
            return Err(GuardFailure::ValidatorRevoked(vkey).into());
        }
    }
    Ok(())
}

async fn t8_body(trx: &Transaction, k: &Keys, a: &TombstoneArgs) -> Result<Step<bool>> {
    let tk = k.tombstone(&a.tombstone_id);
    let ck = k.tcert(&a.tombstone_id, &a.writer);
    if let Some(v) = get(trx, &tk).await? {
        if envelope_object_id(&v)? == a.tombstone_id
            && (cfg!(feature = "mutate-tombstone-cert-outside") || get(trx, &ck).await?.is_some())
        {
            return Ok(Step::Done(false));
        }
        return Err(GuardFailure::TombstoneExists { tombstone: a.tombstone_id }.into());
    }
    let cert = TombstoneCert::from_bytes(&a.cert_value)?;
    let public = a.ring.writer(&a.writer)
        .ok_or_else(|| GuardFailure::AgentKeyNotRegistered(a.tombstone.author.hex()))?;
    let cert_valid = if cfg!(feature = "mutate-agent-historical-t8") {
        a.ring.verify_writer(&a.writer, &cert.id(), &cert.sig)
    } else { cert.verify(public) };
    if cert.body.tombstone != a.tombstone_id || cert.body.target != a.tombstone.target || cert.body.writer != a.writer ||
        !cert_valid {
        return Err(GuardFailure::BadPackage("tombstone certificate does not bind the writer".into()).into());
    }
    tombstone_guards(trx, k, &a.tombstone, &a.target_marker, &a.target_names, &a.target_workspaces, &a.writer, *public, &a.ring, a.controller_grant.as_ref(), false, a.ring.authority).await?;
    trx.set(&tk, &a.value);
    if let Some(grant) = &a.controller_grant { trx.set(&k.delete_grant(&a.tombstone_id), &grant.encoded()); }
    if !cfg!(feature = "mutate-tombstone-cert-outside") {
        trx.set(&ck, &a.cert_value);
    }
    append_event(trx, k, &AeKind::Tombstone { id: a.tombstone_id, cert: TombstoneCert::from_bytes(&a.cert_value)?.id() }, 0);
    Ok(Step::Commit(true))
}

// ---------------------------------------------------------------- T9/T10 bodies

pub(crate) struct ReceiveGroupArgs {
    pub group: Id,
    pub marker_id: Id,
    pub author: AgentId,
    pub author_writer: WorkspaceId,
    pub author_public: [u8; 32],
    pub author_replica: crate::id::ReplicaId,
    pub ring: Arc<crate::sign::KeyRing>,
    pub marker_value: Vec<u8>,
    pub revisions: Vec<(Id, Revision, Vec<u8>)>,
    pub receipt_id: Id,
    pub receipt_value: Vec<u8>,
    /// The receipt's validator key (its revocation is read in the transaction).
    pub validator_key: [u8; 32],
    /// The job envelope the receipt answers, already checked against this deployment's
    /// key ring with the staging rule (written as `job/<id>`, as T1 does).
    pub job_id: Id,
    pub job_value: Vec<u8>,
    /// The decoded envelope: its request is this deployment's to cancel if one of
    /// `local_issuers` (or, when federated, the pinned local member's keys) signed it.
    pub job: crate::receipt::SignedJob,
    /// Without a pinned federation: every key that may sign envelopes T1 here accepts
    /// (authority and job issuers), so T9 reads cancellation exactly when T1 would.
    pub local_issuers: Vec<[u8; 32]>,
    /// The groups the job's dependency capsules name (T1's dependency guard).
    pub dep_groups: Vec<Id>,
    pub replica: crate::id::ReplicaId,
    /// This deployment's receiver certificate (key, value).
    pub cert: (Vec<u8>, Vec<u8>),
    /// The sender's verified certificates, kept as evidence (key, value).
    pub evidence: Vec<(Vec<u8>, Vec<u8>)>,
    pub chunk_index: Option<Vec<(Id, u64)>>,
    pub variant: bool,
    pub target_home: Option<String>,
}

/// A receiver certifies only a group it knows as published: the sender's certificate is
/// the evidence (§8.3 "receiving an already-published group requires a live replica
/// certificate"; AckCertificates `put` needs `known n d`). It certifies on its own
/// deployment's replica only; the sender's certificates are stored apart and never counted.
async fn t9_body(trx: &Transaction, k: &Keys, a: &ReceiveGroupArgs) -> Result<Step<bool>> {
    let federation = config_in_txn(trx, k).await?;
    if let Some(cfg) = &federation {
        let mut found_home: Option<&String> = None;
        for (_, rev, _) in &a.revisions {
            if let Some(home) = cfg.target_homes.get(&rev.name) {
                if found_home.is_some_and(|h| h != home) { return Err(StoreError::Invalid("target names have different homes".into())); }
                found_home = Some(home);
            }
        }
        if found_home.map(String::as_str) != a.target_home.as_deref() {
            return Err(StoreError::Invalid("target home changed before receive commit".into()));
        }
        if let Some(home) = found_home {
            if home == &cfg.deployment && get(trx, &k.marker(&a.group)).await?.is_none() {
                return Err(StoreError::Invalid("target home cannot receive an unknown foreign publication".into()));
            }
            let member = &cfg.members[home];
            if !a.evidence.iter().any(|(_, value)| Cert::from_bytes(value).ok().is_some_and(|c|
                c.body.group == a.group && c.body.marker == a.marker_id && c.body.replica == member.replica &&
                member.verify_writer(&a.ring, &c.body.writer, &c.id(), &c.sig))) {
                return Err(StoreError::Invalid("target publication lacks home certificate".into()));
            }
        }
    } else if a.target_home.is_some() {
        return Err(StoreError::Invalid("target home supplied without pinned federation".into()));
    }
    if !cfg!(feature = "mutate-no-agent-registry") {
        if a.ring.ambiguous_writer_origins.contains(&a.author_writer) {
            return Err(GuardFailure::AgentKeyNotRegistered(a.author.hex()).into());
        }
        let issuer = if let Some(cfg) = &federation {
            cfg.members.values().find(|member| member.replica == a.author_replica &&
                a.evidence.iter().any(|(_, bytes)| Cert::from_bytes(bytes).ok().is_some_and(|cert|
                    cert.body.group == a.group && cert.body.marker == a.marker_id &&
                    cert.body.writer == a.author_writer && cert.body.replica == a.author_replica &&
                    a.ring.signing_writer_key(&a.author_writer, &cert.id(), &cert.sig) == Some(a.author_public) &&
                    member.verify_writer(&a.ring, &a.author_writer, &cert.id(), &cert.sig))))
                .map(|member| member.authority)
        } else { a.ring.writer_origins.get(&a.author_writer).copied() };
        let issuer = issuer.ok_or_else(|| GuardFailure::AgentKeyNotRegistered(a.author.hex()))?;
        active_agent_key_from(trx, k, &a.ring, a.author, a.author_writer, a.author_public, issuer).await?;
    }
    let mk = k.marker(&a.group);
    let mut publication_new = false;
    if let Some(v) = get(trx, &mk).await? {
        let local = envelope_object_id(&v)?;
        if local != a.marker_id && cfg!(feature = "mutate-receive-overwrite-marker") {
            trx.set(&mk, &a.marker_value);
        } else if local != a.marker_id && !a.variant {
            // One marker per group in the store (and per group in the Workspaces model's
            // Layout); a second publication of the group elsewhere is a conflict, reported.
            return Err(GuardFailure::MarkerConflict { group: a.group, local, remote: a.marker_id }.into());
        }
        if local != a.marker_id {
            let vk = k.marker_variant(&a.group, &a.marker_id);
            if get(trx, &vk).await?.is_none() {
                trx.set(&vk, &a.marker_value);
                publication_new = true;
            }
        }
    } else {
        for (_, rev, _) in &a.revisions {
            // TargetNames keeps one record per name, in one store: a name homed here is
            // published only by its owner through T1, never received.
            if federation.as_ref().is_none_or(|cfg| !cfg.target_homes.contains_key(&rev.name))
                && get(trx, &k.target(&rev.name)).await?.is_some() {
                return Err(GuardFailure::ForeignTarget(rev.name.clone()).into());
            }
            // Admitted ancestor closure, as in T1.
            for p in &rev.parents {
                if get(trx, &k.revision(p)).await?.is_none() {
                    return Err(GuardFailure::UnknownParentRevision(*p).into());
                }
            }
        }
        trx.set(&mk, &a.marker_value);
        publication_new = true;
    }
    // A new marker or marker variant is a publication here, so T1's cancellation and
    // dependency reads apply in this transaction (W2 A-2): a request this deployment's
    // controller or issuers signed and then cancelled is never published here, whoever
    // relays its receipt, and every job dependency must already be published and
    // certified on this replica. Evidence for a group already published here is not a
    // new publication; a cancellation does not unpublish.
    if publication_new {
        let local = match &federation {
            Some(cfg) => {
                let own = &cfg.members[&cfg.deployment];
                std::iter::once(&own.authority).chain(&own.job_issuers).any(|key| a.job.verify(key))
            }
            None => a.local_issuers.iter().any(|key| a.job.verify(key)),
        };
        let request = &a.job.body.request;
        if local && !cfg!(feature = "mutate-receive-no-cancel-check") && get(trx, &k.job_cancel(&a.job.body.worker, request)).await?.is_some() {
            return Err(GuardFailure::JobCancelled(request.clone()).into());
        }
        if !cfg!(feature = "mutate-receive-no-dep-check") {
            dependencies_published(trx, k, &a.dep_groups, &a.ring, a.replica).await?;
        }
    }
    // P3: a receive is a publication here, so the receiver's revocation of the receipt's
    // validator stops it, as it stops T1 (the staging rule itself was checked against this
    // deployment's key ring before the transaction).
    if !cfg!(feature = "mutate-no-revocation-check") && get(trx, &k.revocation(&a.validator_key)).await?.is_some() {
        return Err(GuardFailure::ValidatorRevoked(a.validator_key).into());
    }
    for (id, _, v) in &a.revisions {
        let rk = k.revision(id);
        if trx.get(&rk, true).await?.is_none() {
            trx.set(&rk, v);
        }
    }
    let rk = k.receipt(&a.receipt_id);
    if trx.get(&rk, true).await?.is_none() {
        trx.set(&rk, &a.receipt_value);
    }
    let jk = k.job(&a.job_id);
    if trx.get(&jk, true).await?.is_none() {
        trx.set(&jk, &a.job_value);
    }
    let origin_cert = a.evidence.first().map(|(_, value)| Cert::from_bytes(value).map(|cert| cert.id())).transpose()?
        .unwrap_or(Cert::from_bytes(&a.cert.1)?.id());
    let proof_key = k.jobproof(&a.group, &a.marker_id, &origin_cert);
    let mut proof_new = false;
    match get(trx, &proof_key).await? {
        None => { trx.set(&proof_key, &a.job_value); proof_new = true; }
        Some(old) if old == a.job_value => {}
        Some(_) => return Err(StoreError::Invalid("source job proof collision for publication certificate".into())),
    }
    let mut changed = publication_new || proof_new;
    let mut local_cert_new = false;
    match get(trx, &a.cert.0).await? {
        None => { trx.set(&a.cert.0, &a.cert.1); changed = true; local_cert_new = true; }
        Some(old) if old == a.cert.1 => {}
        Some(_) => return Err(StoreError::Invalid("local certificate key holds different bytes".into())),
    }
    let mut new_evidence = Vec::new();
    for (ek, ev) in &a.evidence {
        match get(trx, ek).await? {
            None => { trx.set(ek, ev); changed = true; new_evidence.push(Cert::from_bytes(ev)?.id()); }
            Some(old) if old == *ev => {}
            Some(_) => return Err(StoreError::Invalid("foreign certificate key holds different bytes".into())),
        }
    }
    if let Some(chunks) = &a.chunk_index {
        let mut e = Enc::new();
        e.list(chunks, |e, (id, length)| { id.encode(e); e.uvarint(*length); });
        trx.set(&k.group_chunks(&a.group), &e.finish());
    }
    if proof_new { append_event(trx, k, &AeKind::GroupVariant { group: a.group, marker: a.marker_id, cert: origin_cert }, 0); }
    if new_evidence.len() > u16::MAX as usize - 2 { return Err(StoreError::Invalid("too many certificates in one receive".into())); }
    for (i, cert) in new_evidence.into_iter().enumerate() {
        append_event(trx, k, &AeKind::Evidence { kind: "cert".into(), object: a.group, cert }, (i + 1) as u16);
    }
    if local_cert_new {
        let cert = Cert::from_bytes(&a.cert.1)?.id();
        append_event(trx, k, &AeKind::Evidence { kind: "cert".into(), object: a.group, cert }, (a.evidence.len() + 1) as u16);
    }
    if !changed { return Ok(Step::Done(false)); }
    Ok(Step::Commit(true))
}

pub(crate) struct ReceiveTombstoneArgs {
    pub tombstone: Tombstone,
    pub tombstone_id: Id,
    pub value: Vec<u8>,
    pub target_marker: Marker,
    pub target_names: Vec<Name>,
    pub target_workspaces: Vec<WorkspaceId>,
    /// The writer of a verified sender certificate who is the target's author workspace,
    /// i.e. the deleter (OPEN-19 default), if any.
    pub deleter: WorkspaceId,
    pub deleter_public: [u8; 32],
    pub deleter_replica: crate::id::ReplicaId,
    pub ring: Arc<crate::sign::KeyRing>,
    pub controller_grant: Option<crate::authority::ControllerDeleteGrant>,
    pub cert: (Vec<u8>, Vec<u8>),
    pub evidence: Vec<(Vec<u8>, Vec<u8>)>,
}

async fn t10_body(trx: &Transaction, k: &Keys, a: &ReceiveTombstoneArgs) -> Result<Step<bool>> {
    let federation = config_in_txn(trx, k).await?;
    let tk = k.tombstone(&a.tombstone_id);
    let mut publication_new = false;
    if let Some(v) = get(trx, &tk).await? {
        if envelope_object_id(&v)? != a.tombstone_id {
            return Err(StoreError::Invalid("tombstone key holds another object".into()));
        }
    } else {
        if a.ring.ambiguous_writer_origins.contains(&a.deleter) {
            return Err(GuardFailure::AgentKeyNotRegistered(a.tombstone.author.hex()).into());
        }
        let source_issuer = if let Some(cfg) = &federation {
            cfg.members.values().find(|member| member.replica == a.deleter_replica &&
                a.evidence.iter().any(|(_, bytes)| TombstoneCert::from_bytes(bytes).ok().is_some_and(|cert|
                    cert.body.tombstone == a.tombstone_id && cert.body.writer == a.deleter &&
                    cert.body.replica == a.deleter_replica &&
                    a.ring.signing_writer_key(&a.deleter, &cert.id(), &cert.sig) == Some(a.deleter_public) &&
                    member.verify_writer(&a.ring, &a.deleter, &cert.id(), &cert.sig))))
                .map(|member| member.authority)
        } else { a.ring.writer_origins.get(&a.deleter).copied() };
        let source_issuer = source_issuer.ok_or_else(|| GuardFailure::AgentKeyNotRegistered(a.tombstone.author.hex()))?;
        if let Some(grant) = &a.controller_grant {
            let grant_issuer: Option<[u8; 32]> = hex::decode(&grant.issuer).ok().and_then(|v| v.try_into().ok());
            let source_bound = a.evidence.iter().filter_map(|(_, bytes)| TombstoneCert::from_bytes(bytes).ok()).any(|cert| {
                if cert.body.tombstone != a.tombstone_id || cert.body.target != a.tombstone.target { return false; }
                let Some(public) = a.ring.signing_writer_key(&cert.body.writer, &cert.id(), &cert.sig) else { return false };
                let origin_matches = grant_issuer.is_some_and(|issuer| !a.ring.ambiguous_writer_origins.contains(&cert.body.writer) &&
                    federation.as_ref().map_or_else(
                        || a.ring.writer_origins.get(&cert.body.writer).copied() == Some(issuer),
                        |cfg| cfg.members.values().any(|member| member.replica == cert.body.replica &&
                            member.authority == issuer && member.verify_writer(&a.ring, &cert.body.writer, &cert.id(), &cert.sig))));
                let registered_source = a.ring.agent_keys.iter().any(|entry| entry.parts().is_some_and(|(_, workspace, key, issuer)|
                    workspace == cert.body.writer && key == public && grant.issuer == hex::encode(issuer) && entry.verify()));
                registered_source && (origin_matches || cfg!(feature = "mutate-controller-no-origin"))
            });
            if !source_bound && !cfg!(feature = "mutate-controller-no-source") {
                return Err(GuardFailure::ControllerDeleteDenied.into());
            }
        }
        tombstone_guards(trx, k, &a.tombstone, &a.target_marker, &a.target_names, &a.target_workspaces, &a.deleter, a.deleter_public, &a.ring, a.controller_grant.as_ref(), true, source_issuer).await?;
        trx.set(&tk, &a.value);
        if let Some(grant) = &a.controller_grant { trx.set(&k.delete_grant(&a.tombstone_id), &grant.encoded()); }
        publication_new = true;
    }
    let mut changed = publication_new;
    let mut local_cert_new = false;
    match get(trx, &a.cert.0).await? {
        None => { trx.set(&a.cert.0, &a.cert.1); changed = true; local_cert_new = true; }
        Some(old) if old == a.cert.1 => {}
        Some(_) => return Err(StoreError::Invalid("local tombstone certificate key holds different bytes".into())),
    }
    let mut new_evidence = Vec::new();
    for (ek, ev) in &a.evidence {
        match get(trx, ek).await? {
            None => { trx.set(ek, ev); changed = true; new_evidence.push(TombstoneCert::from_bytes(ev)?.id()); }
            Some(old) if old == *ev => {}
            Some(_) => return Err(StoreError::Invalid("foreign tombstone certificate key holds different bytes".into())),
        }
    }
    if publication_new {
        let cert = a.evidence.iter().filter_map(|(_, ev)| TombstoneCert::from_bytes(ev).ok())
            .find(|c| c.body.writer == a.deleter).map(|c| c.id())
            .unwrap_or(TombstoneCert::from_bytes(&a.cert.1)?.id());
        append_event(trx, k, &AeKind::Tombstone { id: a.tombstone_id, cert }, 0);
    }
    if new_evidence.len() > u16::MAX as usize - 2 { return Err(StoreError::Invalid("too many tombstone certificates in one receive".into())); }
    for (i, cert) in new_evidence.into_iter().enumerate() {
        append_event(trx, k, &AeKind::Evidence { kind: "tcert".into(), object: a.tombstone_id, cert }, (i + 1) as u16);
    }
    if local_cert_new {
        let cert = TombstoneCert::from_bytes(&a.cert.1)?.id();
        append_event(trx, k, &AeKind::Evidence { kind: "tcert".into(), object: a.tombstone_id, cert }, (a.evidence.len() + 1) as u16);
    }
    if !changed { return Ok(Step::Done(false)); }
    Ok(Step::Commit(true))
}

// ---------------------------------------------------------------- T5 body

pub(crate) struct CommitArgs {
    pub record: SignedRecord,
    pub record_value: Vec<u8>,
    pub rcert_value: Vec<u8>,
    pub snapshot: Option<Snapshot>,
    pub ring: Arc<crate::sign::KeyRing>,
    pub replica: crate::id::ReplicaId,
}

async fn t5_body(trx: &Transaction, k: &Keys, a: &CommitArgs, commit: bool) -> Result<Step<bool>> {
    let c = a.record.id();
    let rec = &a.record.body;
    let ck = k.catalog(&c);
    let rk = k.rcert(&c);
    let existing = get(trx, &ck).await?;
    if commit {
        if get(trx, &rk).await?.is_some() {
            return Ok(Step::Done(false));
        }
    } else if existing.is_some() {
        return Ok(Step::Done(false));
    }
    // CatalogFencing / CatalogCertificates: token.rank = fence, read in this transaction.
    let fence = match get(trx, &k.fence()).await? {
        None => 0,
        Some(v) => dec_u64(&v)?,
    };
    if rec.token.rank != fence && !(commit && cfg!(feature = "mutate-unfenced-commit")) {
        return Err(GuardFailure::StaleToken { rank: rec.token.rank, fence }.into());
    }
    match get(trx, &k.token(rec.token.rank)).await? {
        Some(v) if TokenEntry::from_pce(&v)?.token.body.token == rec.token => {}
        _ => return Err(GuardFailure::TokenNotIssued(rec.token.rank).into()),
    }
    if commit {
        // The record's manifest (snapshot) certificate.
        if get(trx, &k.ocert(Kind::Snapshot, &rec.snapshot)).await?.is_none() {
            return Err(GuardFailure::ManifestUncertified(rec.snapshot).into());
        }
        let snapshot = a.snapshot.as_ref().ok_or(GuardFailure::CheckpointSnapshotMissing(rec.snapshot))?;
        if snapshot.id() != rec.snapshot || snapshot.workspace != rec.workspace {
            return Err(GuardFailure::CheckpointSnapshotMissing(rec.snapshot).into());
        }
        crate::checkpoint_guard::check(trx, k, snapshot, &a.ring, a.replica).await?;
        // Every parent is committed: its commit and manifest certificates exist.
        if let Some(p) = rec.predecessor.filter(|_| !cfg!(feature = "mutate-no-parent-check")) {
            if get(trx, &k.rcert(&p)).await?.is_none() {
                return Err(GuardFailure::ParentUncommitted(p).into());
            }
            let Some(pv) = get(trx, &k.catalog(&p)).await? else {
                return Err(GuardFailure::ParentUncommitted(p).into());
            };
            let parent = SignedRecord::from_bytes(&pv)?;
            if get(trx, &k.ocert(Kind::Snapshot, &parent.body.snapshot)).await?.is_none() {
                return Err(GuardFailure::ParentUncommitted(p).into());
            }
        }
    }
    match existing {
        Some(v) if v != a.record_value => return Err(GuardFailure::RecordMismatch.into()),
        Some(_) => {}
        None => trx.set(&ck, &a.record_value),
    }
    if commit {
        trx.set(&rk, &a.rcert_value);
        append_event(trx, k, &AeKind::Catalogue { source: String::new(), id: c, cert: CommitCert::from_bytes(&a.rcert_value)?.id() }, 0);
    }
    Ok(Step::Commit(true))
}
