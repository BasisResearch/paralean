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
//! No code path in this crate clears a key (`clear`/`clear_range` are never called): the
//! key spaces are grow-only, which the paginated-scan argument of store.md needs.

use std::sync::{Arc, Mutex, OnceLock};

use foundationdb::api::NetworkAutoStop;
use foundationdb::future::FdbValues;
use foundationdb::options::StreamingMode;
use foundationdb::tuple::{Bytes, Subspace};
use foundationdb::{Database, KeySelector, RangeOption, Transaction};
use futures::future::BoxFuture;

use crate::error::{GuardFailure, Result, StoreError};
use crate::faults::{CommitFault, Faults, Txn};
use crate::id::{sha256, Id, Kind, WorkspaceId};
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
pub fn shutdown() {
    if let Some(m) = NETWORK.get() {
        drop(m.lock().unwrap().take());
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
    pub fn revision(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("revision", b(&id.0)))
    }
    pub fn receipt(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("receipt", b(&id.0)))
    }
    pub fn tombstone(&self, id: &Id) -> Vec<u8> {
        self.root.pack(&("tombstone", b(&id.0)))
    }
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

async fn get(trx: &Transaction, key: &[u8]) -> Result<Option<Vec<u8>>> {
    Ok(trx.get(key, false).await?.map(|v| v.to_vec()))
}

async fn range(trx: &Transaction, begin: Vec<u8>, end: Vec<u8>, limit: usize) -> Result<FdbValues> {
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
        let value = Arc::new(value);
        self.run(
            Txn::T6ObjectCert,
            Box::new(move |trx| {
                let (key, value) = (key.clone(), value.clone());
                Box::pin(async move {
                    // Snapshot read: any writer's certificate suffices, and concurrent
                    // certifiers need not conflict.
                    if trx.get(&key, true).await?.is_some() {
                        return Ok(Step::Done(false));
                    }
                    trx.set(&key, &value);
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
    pub marker_value: Vec<u8>,
    pub revisions: Vec<(Id, Revision, Vec<u8>)>,
    pub receipt_id: Id,
    pub receipt_value: Vec<u8>,
    pub targets: Vec<PreparedTarget>,
    pub cert_value: Vec<u8>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublishOutcome {
    pub marker: Id,
    /// False when the effect was already present (a retry after an unknown outcome).
    pub fresh: bool,
}

async fn t1_body(trx: &Transaction, k: &Keys, a: &PublishArgs) -> Result<Step<PublishOutcome>> {
    let mk = k.marker(&a.group);
    let ck = k.cert(&a.group, &a.writer);
    if let Some(v) = get(trx, &mk).await? {
        let existing = envelope_object_id(&v)?;
        if existing == a.marker_id && (cfg!(feature = "mutate-cert-outside-publish") || get(trx, &ck).await?.is_some()) {
            return Ok(Step::Done(PublishOutcome { marker: a.marker_id, fresh: false }));
        }
        return Err(GuardFailure::AlreadyPublished { group: a.group, existing }.into());
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
}

/// The tombstone rules shared by T8 and the anti-entropy receive (T10). Workspaces models a
/// tombstone as a revision of its target: the target is published (its revision ancestors
/// are admitted), in the same file, and older (`ts e < ts d` for everything the author
/// knows). OPEN-19's v0 default restricts deletion to the element's author (the controller
/// path is not implemented): the tombstone's `author` is the target marker's, and the
/// deleting writer (`deleter`, who signs the tombstone certificate) is the workspace of the
/// target's revisions, since P2 has no registry binding agent IDs to workspaces. TargetNames
/// has no deletion, so a group declaring a target name cannot be tombstoned (P2's choice;
/// see docs/p2-log.md).
pub(crate) async fn tombstone_guards(
    trx: &Transaction,
    k: &Keys,
    t: &Tombstone,
    m: &Marker,
    names: &[Name],
    workspaces: &[WorkspaceId],
    deleter: &WorkspaceId,
) -> Result<()> {
    let g = t.target;
    if !cfg!(feature = "mutate-tombstone-no-target-check") {
        let Some(mv) = get(trx, &k.marker(&g)).await? else {
            return Err(GuardFailure::NotPublished(g).into());
        };
        if envelope_object_id(&mv)? != m.id() || m.group != g {
            return Err(GuardFailure::BadPackage("tombstone target's marker differs".into()).into());
        }
        let (b0, e0) = k.certs_of(&g).range();
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
    if (t.author != m.author || !workspaces.contains(deleter)) && !cfg!(feature = "mutate-tombstone-no-author-check") {
        return Err(GuardFailure::TombstoneNotAuthor.into());
    }
    for n in names {
        if get(trx, &k.target(n)).await?.is_some() {
            return Err(GuardFailure::TombstoneOfTarget(n.clone()).into());
        }
    }
    if let Some(r) = t.receipt {
        if get(trx, &k.receipt(&r)).await?.is_none() {
            return Err(GuardFailure::TombstoneReceiptAbsent(r).into());
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
    tombstone_guards(trx, k, &a.tombstone, &a.target_marker, &a.target_names, &a.target_workspaces, &a.writer).await?;
    trx.set(&tk, &a.value);
    if !cfg!(feature = "mutate-tombstone-cert-outside") {
        trx.set(&ck, &a.cert_value);
    }
    Ok(Step::Commit(true))
}

// ---------------------------------------------------------------- T9/T10 bodies

pub(crate) struct ReceiveGroupArgs {
    pub group: Id,
    pub marker_id: Id,
    pub marker_value: Vec<u8>,
    pub revisions: Vec<(Id, Revision, Vec<u8>)>,
    pub receipt_id: Id,
    pub receipt_value: Vec<u8>,
    /// This deployment's receiver certificate (key, value).
    pub cert: (Vec<u8>, Vec<u8>),
    /// The sender's verified certificates, kept as evidence (key, value).
    pub evidence: Vec<(Vec<u8>, Vec<u8>)>,
}

/// A receiver certifies only a group it knows as published: the sender's certificate is
/// the evidence (§8.3 "receiving an already-published group requires a live replica
/// certificate"; AckCertificates `put` needs `known n d`). It certifies on its own
/// deployment's replica only; the sender's certificates are stored apart and never counted.
async fn t9_body(trx: &Transaction, k: &Keys, a: &ReceiveGroupArgs) -> Result<Step<bool>> {
    let mk = k.marker(&a.group);
    if let Some(v) = get(trx, &mk).await? {
        let local = envelope_object_id(&v)?;
        if local != a.marker_id && cfg!(feature = "mutate-receive-overwrite-marker") {
            trx.set(&mk, &a.marker_value);
        } else if local != a.marker_id {
            // One marker per group in the store (and per group in the Workspaces model's
            // Layout); a second publication of the group elsewhere is a conflict, reported.
            return Err(GuardFailure::MarkerConflict { group: a.group, local, remote: a.marker_id }.into());
        }
        let (b0, e0) = k.certs_of(&a.group).range();
        if !range(trx, b0, e0, 1).await?.is_empty() {
            return Ok(Step::Done(false));
        }
    } else {
        for (_, rev, _) in &a.revisions {
            // TargetNames keeps one record per name, in one store: a name homed here is
            // published only by its owner through T1, never received.
            if get(trx, &k.target(&rev.name)).await?.is_some() {
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
    trx.set(&a.cert.0, &a.cert.1);
    for (ek, ev) in &a.evidence {
        trx.set(ek, ev);
    }
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
    pub cert: (Vec<u8>, Vec<u8>),
    pub evidence: Vec<(Vec<u8>, Vec<u8>)>,
}

async fn t10_body(trx: &Transaction, k: &Keys, a: &ReceiveTombstoneArgs) -> Result<Step<bool>> {
    let tk = k.tombstone(&a.tombstone_id);
    if let Some(v) = get(trx, &tk).await? {
        if envelope_object_id(&v)? != a.tombstone_id {
            return Err(StoreError::Invalid("tombstone key holds another object".into()));
        }
        let (b0, e0) = k.tcerts_of(&a.tombstone_id).range();
        if !range(trx, b0, e0, 1).await?.is_empty() {
            return Ok(Step::Done(false));
        }
    } else {
        tombstone_guards(trx, k, &a.tombstone, &a.target_marker, &a.target_names, &a.target_workspaces, &a.deleter).await?;
        trx.set(&tk, &a.value);
    }
    trx.set(&a.cert.0, &a.cert.1);
    for (ek, ev) in &a.evidence {
        trx.set(ek, ev);
    }
    Ok(Step::Commit(true))
}

// ---------------------------------------------------------------- T5 body

pub(crate) struct CommitArgs {
    pub record: SignedRecord,
    pub record_value: Vec<u8>,
    pub rcert_value: Vec<u8>,
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
    }
    Ok(Step::Commit(true))
}

