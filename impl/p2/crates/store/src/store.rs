//! The store handle: FoundationDB metadata plus the S3 payload store, the trusted key ring
//! and the abstract replica identity σ.

use std::sync::Arc;

use crate::error::{Result, StoreError};
use crate::faults::Faults;
use crate::id::{Id, Kind, ReplicaId, WorkspaceId};
use crate::meta::{self, Envelope, Meta};
use crate::objects::*;
use crate::pce::Pce;
use crate::s3::{Payloads, S3Config};
use crate::sign::KeyRing;

#[derive(Clone, Debug)]
pub struct StoreConfig {
    /// FDB cluster file (`None`: the client default).
    pub cluster_file: Option<String>,
    /// Deployment name: FDB keys live under `("paralean", deployment)`.
    pub deployment: String,
    pub s3: S3Config,
    /// σ, the single abstract replica (store.md "Abstraction").
    pub replica: ReplicaId,
    /// Page size of enumeration scans.
    pub page: usize,
}

impl StoreConfig {
    /// From `PARALEAN_FDB_CLUSTER`, `PARALEAN_S3_*` and the given deployment; the S3 prefix
    /// defaults to `<deployment>/`.
    pub fn from_env(deployment: &str) -> Result<StoreConfig> {
        StoreConfig::from_env_with("PARALEAN_", deployment)
    }

    /// As `from_env`, reading `<p>FDB_CLUSTER` and `<p>S3_*` (`PARALEAN_PEER_`: a peer
    /// deployment's own cluster and store, for anti-entropy).
    pub fn from_env_with(p: &str, deployment: &str) -> Result<StoreConfig> {
        let mut s3 = S3Config::from_env_with(p)?;
        if std::env::var(format!("{p}S3_PREFIX")).is_err() {
            s3.prefix = format!("{deployment}/");
        }
        Ok(StoreConfig {
            cluster_file: std::env::var(format!("{p}FDB_CLUSTER")).ok(),
            deployment: deployment.to_string(),
            s3,
            replica: ReplicaId::derive(&format!("sigma/{deployment}")),
            page: std::env::var("PARALEAN_SCAN_PAGE").ok().and_then(|s| s.parse().ok()).unwrap_or(500),
        })
    }
}

#[derive(Clone)]
pub struct Store {
    pub meta: Meta,
    pub s3: Payloads,
    pub ring: Arc<KeyRing>,
    pub replica: ReplicaId,
    pub faults: Arc<Faults>,
    pub page: usize,
}

impl Store {
    pub fn open(cfg: &StoreConfig, ring: KeyRing, faults: Arc<Faults>) -> Result<Store> {
        let meta = Meta::open(cfg.cluster_file.as_deref(), &cfg.deployment, faults.clone())?;
        let s3 = Payloads::new(&cfg.s3, faults.clone());
        Ok(Store { meta, s3, ring: Arc::new(ring), replica: cfg.replica, faults, page: cfg.page })
    }

    /// The same deployment with another fault plan (e.g. one per simulated process).
    pub fn with_faults(&self, faults: Arc<Faults>) -> Store {
        Store {
            meta: self.meta.with_faults(faults.clone()),
            s3: self.s3.with_faults(faults.clone()),
            faults,
            ..self.clone()
        }
    }

    /// Wrap an unsigned object's stored bytes for an FDB value, uploading the blob first
    /// when the value is too large (payload before metadata).
    pub async fn stage_value(&self, object: Id, stored: Vec<u8>) -> Result<Vec<u8>> {
        let (env, blob) = meta::envelope_for(object, stored);
        if let Some(b) = blob {
            self.s3.put(Kind::Blob, &b).await?;
        }
        Ok(env.encode())
    }

    /// Unwrap an envelope; a blob is fetched and verified (missing or corrupt → `None`).
    pub async fn open_value(&self, v: &[u8]) -> Result<Option<Vec<u8>>> {
        match Envelope::decode(v)? {
            Envelope::Inline(s) => Ok(Some(s)),
            Envelope::Blob { object, blob } => {
                let Some(pre) = self.s3.get(Kind::Blob, &blob).await? else { return Ok(None) };
                let stored = Kind::Blob.domain().strip(&pre)?.to_vec();
                if crate::id::Id(crate::id::sha256(&stored)) != object {
                    return Ok(None);
                }
                Ok(Some(stored))
            }
        }
    }

    async fn unsigned<T: Object>(&self, key: Vec<u8>, id: &Id) -> Result<Option<T>> {
        let Some(v) = self.meta.get(key).await? else { return Ok(None) };
        let Some(stored) = self.open_value(&v).await? else { return Ok(None) };
        let o = T::from_preimage(&stored)?;
        if o.id() != *id {
            return Err(StoreError::Invalid(format!("object under key {} has another ID", id)));
        }
        Ok(Some(o))
    }

    /// The marker of a group, if its key exists (no certificate check: callers decide).
    pub async fn marker(&self, group: &Id) -> Result<Option<(Id, Marker)>> {
        let Some(v) = self.meta.get(self.meta.keys.marker(group)).await? else { return Ok(None) };
        let Some(stored) = self.open_value(&v).await? else { return Ok(None) };
        let m = Marker::from_preimage(&stored)?;
        Ok(Some((m.id(), m)))
    }

    pub async fn tombstone(&self, id: &Id) -> Result<Option<Tombstone>> {
        self.unsigned(self.meta.keys.tombstone(id), id).await
    }

    /// The valid tombstone certificates of a tombstone.
    pub async fn tcerts(&self, t: &Id) -> Result<Vec<TombstoneCert>> {
        let kvs = self.meta.scan(&self.meta.keys.tcerts_of(t), self.page, |_| None).await?;
        let mut out = Vec::new();
        for (k, v) in kvs {
            let (_, _, w): (String, foundationdb::tuple::Bytes, foundationdb::tuple::Bytes) =
                self.meta.keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
            let Ok(c) = TombstoneCert::from_bytes(&v) else { continue };
            if c.body.tombstone == *t && c.body.writer.0[..] == w[..] && self.ring.verify_writer(&c.body.writer, &c.id(), &c.sig) {
                out.push(c);
            }
        }
        Ok(out)
    }

    pub async fn revision(&self, id: &Id) -> Result<Option<Revision>> {
        self.unsigned(self.meta.keys.revision(id), id).await
    }

    pub async fn receipt(&self, id: &Id) -> Result<Option<Receipt>> {
        match self.meta.get(self.meta.keys.receipt(id)).await? {
            None => Ok(None),
            Some(v) => Ok(Some(Receipt::from_bytes(&v)?)),
        }
    }

    pub async fn record(&self, c: &Id) -> Result<Option<SignedRecord>> {
        match self.meta.get(self.meta.keys.catalog(c)).await? {
            None => Ok(None),
            Some(v) => Ok(Some(SignedRecord::from_bytes(&v)?)),
        }
    }

    pub async fn token(&self, rank: u64) -> Result<Option<TokenEntry>> {
        match self.meta.get(self.meta.keys.token(rank)).await? {
            None => Ok(None),
            Some(v) => Ok(Some(TokenEntry::from_pce(&v)?)),
        }
    }

    /// A commit certificate that verifies under its holder's key and matches the record.
    pub async fn valid_rcert(&self, c: &Id, rec: &CatalogRecord) -> Result<Option<CommitCert>> {
        let Some(v) = self.meta.get(self.meta.keys.rcert(c)).await? else { return Ok(None) };
        let rc = CommitCert::from_bytes(&v)?;
        let ok = rc.body.catalog == *c
            && rc.body.token == rec.token
            && self.ring.verify_writer(&rec.token.holder, &rc.id(), &rc.sig);
        Ok(ok.then_some(rc))
    }

    /// An object certificate that verifies under its writer's key and names this object.
    pub async fn valid_ocert(&self, kind: Kind, id: &Id) -> Result<Option<ObjectCert>> {
        let Some(v) = self.meta.get(self.meta.keys.ocert(kind, id)).await? else { return Ok(None) };
        let oc = ObjectCert::from_bytes(&v)?;
        let ok = oc.body.kind == kind && oc.body.id == *id && self.ring.verify_writer(&oc.body.writer, &oc.id(), &oc.sig);
        Ok(ok.then_some(oc))
    }

    /// The valid publication certificates of a group.
    pub async fn certs(&self, group: &Id) -> Result<Vec<Cert>> {
        let kvs = self.meta.scan(&self.meta.keys.certs_of(group), self.page, |_| None).await?;
        let mut out = Vec::new();
        for (k, v) in kvs {
            let (_, _, w): (String, foundationdb::tuple::Bytes, foundationdb::tuple::Bytes) =
                self.meta.keys.root.unpack(&k).map_err(|e| StoreError::Invalid(e.to_string()))?;
            let Ok(c) = Cert::from_bytes(&v) else { continue };
            if c.body.group == *group
                && c.body.writer.0[..] == w[..]
                && self.ring.verify_writer(&c.body.writer, &c.id(), &c.sig)
            {
                out.push(c);
            }
        }
        Ok(out)
    }

    pub async fn has_cert(&self, group: &Id, w: &WorkspaceId) -> Result<bool> {
        Ok(self.meta.get(self.meta.keys.cert(group, w)).await?.is_some())
    }

    pub async fn fence(&self) -> Result<u64> {
        self.meta.fence().await
    }
    pub async fn target(&self, name: &Name) -> Result<Option<TargetRecord>> {
        self.meta.target(name).await
    }
}
