//! Payload store client: plain S3 API against a configurable endpoint (Garage behind the
//! s3-guard gateway in the P2 cluster; any S3-compatible store works by changing the
//! endpoint).
//!
//! store.md "Content-addressed writes":
//! 1. the stored bytes are the object's hash preimage, so `SHA-256(bytes) = ID`;
//! 2. `PUT obj/<kind>/<hex id>` with `x-amz-checksum-sha256` set to the ID, so the store
//!    rejects a body whose digest differs;
//! 3. `200 OK` with the echoed checksum equal to the ID is the acknowledgement; a timeout or
//!    error is not, and the PUT is retried (harmless: the key determines the bytes);
//! 4. readers always re-hash; a mismatch counts as missing.
//!
//! The client also re-hashes before every PUT, so a store that ignored the checksum header
//! would still never be sent mislabelled bytes.

use std::sync::Arc;
use std::time::Duration;

use aws_sdk_s3::config::{BehaviorVersion, Region, RequestChecksumCalculation, ResponseChecksumValidation};
use aws_sdk_s3::primitives::ByteStream;
use aws_sdk_s3::Client;
use base64::Engine;

use crate::error::{Result, StoreError};
use crate::faults::{Faults, GetFault, PutFault};
use crate::id::{sha256, Id, Kind};
use crate::objects::{Object, Opaque};

#[derive(Clone, Debug)]
pub struct S3Config {
    pub endpoint: String,
    pub bucket: String,
    pub region: String,
    pub access_key: String,
    pub secret_key: String,
    /// Key prefix (one per deployment in tests; empty in production).
    pub prefix: String,
}

impl S3Config {
    pub fn from_env() -> Result<S3Config> {
        let v = |k: &str| std::env::var(k).map_err(|_| StoreError::Invalid(format!("{k} is not set")));
        Ok(S3Config {
            endpoint: v("PARALEAN_S3_ENDPOINT")?,
            bucket: std::env::var("PARALEAN_S3_BUCKET").unwrap_or_else(|_| "paralean".into()),
            region: std::env::var("PARALEAN_S3_REGION").unwrap_or_else(|_| "garage".into()),
            access_key: v("PARALEAN_S3_ACCESS_KEY")?,
            secret_key: v("PARALEAN_S3_SECRET_KEY")?,
            prefix: std::env::var("PARALEAN_S3_PREFIX").unwrap_or_default(),
        })
    }
}

/// Proof that the payload store acknowledged `(kind, id)` to this process: a verified
/// `200 OK` of our own PUT with the echoed checksum, or a GET whose bytes re-hashed to the
/// ID. Only this module constructs it, so metadata can name an object only after its
/// writer saw it acknowledged.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Acked {
    kind: Kind,
    id: Id,
}

impl Acked {
    pub fn kind(&self) -> Kind {
        self.kind
    }
    pub fn id(&self) -> Id {
        self.id
    }
}

#[derive(Clone)]
pub struct Payloads {
    client: Client,
    bucket: String,
    prefix: String,
    faults: Arc<Faults>,
    pub max_attempts: usize,
}

fn b64(id: &Id) -> String {
    base64::engine::general_purpose::STANDARD.encode(id.0)
}

impl Payloads {
    pub fn new(cfg: &S3Config, faults: Arc<Faults>) -> Payloads {
        let creds = aws_credential_types::Credentials::from_keys(&cfg.access_key, &cfg.secret_key, None);
        let timeouts = aws_sdk_s3::config::timeout::TimeoutConfig::builder()
            .operation_attempt_timeout(Duration::from_secs(20))
            .connect_timeout(Duration::from_secs(5))
            .build();
        let conf = aws_sdk_s3::config::Builder::new()
            .behavior_version(BehaviorVersion::latest())
            .endpoint_url(&cfg.endpoint)
            .region(Region::new(cfg.region.clone()))
            .credentials_provider(creds)
            .force_path_style(true)
            .request_checksum_calculation(RequestChecksumCalculation::WhenRequired)
            .response_checksum_validation(ResponseChecksumValidation::WhenRequired)
            .timeout_config(timeouts)
            .build();
        Payloads {
            client: Client::from_conf(conf),
            bucket: cfg.bucket.clone(),
            prefix: cfg.prefix.clone(),
            faults,
            max_attempts: 8,
        }
    }

    pub fn with_faults(&self, faults: Arc<Faults>) -> Payloads {
        Payloads { faults, ..self.clone() }
    }

    pub fn key(&self, kind: Kind, id: &Id) -> String {
        format!("{}obj/{}/{}", self.prefix, kind.name(), id.hex())
    }

    /// PUT a preimage under its kind; returns the acknowledgement. Retries timeouts and
    /// errors; the bytes are re-hashed first so a mislabelled body is never sent.
    pub async fn put(&self, kind: Kind, preimage: &[u8]) -> Result<Acked> {
        kind.domain().strip(preimage)?; // the bytes must be a preimage of this kind's domain
        let id = Id(sha256(preimage));
        let key = self.key(kind, &id);
        let mut last = String::new();
        for attempt in 0..self.max_attempts {
            if attempt > 0 {
                tokio::time::sleep(Duration::from_millis(20 * attempt as u64)).await;
            }
            match self.faults.put_fault(kind) {
                PutFault::None => {}
                PutFault::TimeoutNotLanded => {
                    last = "injected timeout (not landed)".into();
                    continue;
                }
                PutFault::TimeoutLanded => {
                    let _ = self.raw_put(&key, preimage, &id).await;
                    last = "injected timeout (landed)".into();
                    continue;
                }
                PutFault::CrashAfterLanded => {
                    let _ = self.raw_put(&key, preimage, &id).await;
                    return Err(self.faults.crash("s3-put-landed"));
                }
            }
            match self.raw_put(&key, preimage, &id).await {
                Ok(()) => return Ok(Acked { kind, id }),
                Err(e) => last = e,
            }
        }
        Err(StoreError::S3(format!("PUT {key} not acknowledged after {} attempts: {last}", self.max_attempts)))
    }

    async fn raw_put(&self, key: &str, body: &[u8], id: &Id) -> std::result::Result<(), String> {
        let want = b64(id);
        let resp = self
            .client
            .put_object()
            .bucket(&self.bucket)
            .key(key)
            .body(ByteStream::from(body.to_vec()))
            .checksum_sha256(&want)
            .send()
            .await
            .map_err(|e| format!("{}", aws_sdk_s3::error::DisplayErrorContext(e)))?;
        match resp.checksum_sha256() {
            Some(echo) if echo == want => Ok(()),
            other => Err(format!("checksum echo {other:?} differs from the ID")),
        }
    }

    pub async fn put_opaque(&self, o: &Opaque) -> Result<Acked> {
        self.put(o.kind, &o.preimage()).await
    }
    pub async fn put_object<T: Object>(&self, kind: Kind, o: &T) -> Result<Acked> {
        debug_assert_eq!(kind.domain(), T::DOMAIN);
        self.put(kind, &o.preimage()).await
    }

    /// GET and verify. `None` if absent or if the bytes do not hash to the ID (corrupt bytes
    /// count as nothing). Transport errors are retried, then reported.
    pub async fn get(&self, kind: Kind, id: &Id) -> Result<Option<Vec<u8>>> {
        let key = self.key(kind, id);
        let mut last = String::new();
        for attempt in 0..self.max_attempts {
            if attempt > 0 {
                tokio::time::sleep(Duration::from_millis(20 * attempt as u64)).await;
            }
            let r = self.client.get_object().bucket(&self.bucket).key(&key).send().await;
            match r {
                Ok(o) => {
                    let mut bytes = match o.body.collect().await {
                        Ok(b) => b.into_bytes().to_vec(),
                        Err(e) => {
                            last = e.to_string();
                            continue;
                        }
                    };
                    if self.faults.get_fault(kind) == GetFault::Corrupt && !bytes.is_empty() {
                        let i = bytes.len() / 2;
                        bytes[i] ^= 0x5a;
                    }
                    if Id(sha256(&bytes)) != *id {
                        self.faults.count("hash-mismatch-on-read");
                        return Ok(None);
                    }
                    return Ok(Some(bytes));
                }
                Err(e) => {
                    if let Some(se) = e.as_service_error() {
                        if se.is_no_such_key() {
                            return Ok(None);
                        }
                    }
                    if e.raw_response().map(|r| r.status().as_u16()) == Some(404) {
                        return Ok(None);
                    }
                    last = format!("{}", aws_sdk_s3::error::DisplayErrorContext(e));
                }
            }
        }
        Err(StoreError::S3(format!("GET {key} failed: {last}")))
    }

    /// A verified read that also yields the acknowledgement proof.
    pub async fn get_acked(&self, kind: Kind, id: &Id) -> Result<Option<(Acked, Vec<u8>)>> {
        Ok(self.get(kind, id).await?.map(|b| (Acked { kind, id: *id }, b)))
    }

    pub async fn get_object<T: Object>(&self, kind: Kind, id: &Id) -> Result<Option<T>> {
        match self.get(kind, id).await? {
            None => Ok(None),
            Some(b) => Ok(Some(T::from_preimage(&b)?)),
        }
    }

    /// List every ID of a kind (paginated).
    pub async fn list(&self, kind: Kind) -> Result<Vec<Id>> {
        let prefix = format!("{}obj/{}/", self.prefix, kind.name());
        let mut out = Vec::new();
        let mut token: Option<String> = None;
        loop {
            let mut req = self.client.list_objects_v2().bucket(&self.bucket).prefix(&prefix).max_keys(1000);
            if let Some(t) = &token {
                req = req.continuation_token(t);
            }
            let resp = req.send().await.map_err(|e| StoreError::S3(format!("{}", aws_sdk_s3::error::DisplayErrorContext(e))))?;
            for o in resp.contents() {
                if let Some(id) = o.key().and_then(|k| k.strip_prefix(&prefix)).and_then(Id::from_hex) {
                    out.push(id);
                }
            }
            match resp.next_continuation_token() {
                Some(t) if resp.is_truncated() == Some(true) => token = Some(t.to_string()),
                _ => break,
            }
        }
        Ok(out)
    }

    // ----------------------------------------------------------- test and fault helpers

    /// Overwrite an object's key with arbitrary bytes and no checksum header: simulates
    /// corruption at rest (or a buggy writer). Readers must treat it as missing.
    pub async fn corrupt_at_rest(&self, kind: Kind, id: &Id, bytes: &[u8]) -> Result<()> {
        self.client
            .put_object()
            .bucket(&self.bucket)
            .key(self.key(kind, id))
            .body(ByteStream::from(bytes.to_vec()))
            .send()
            .await
            .map_err(|e| StoreError::S3(format!("{}", aws_sdk_s3::error::DisplayErrorContext(e))))?;
        Ok(())
    }

    /// A PUT whose checksum header names `claimed` while the body is `body`: the store
    /// must reject it.
    pub async fn put_with_wrong_checksum(&self, kind: Kind, claimed: &Id, body: &[u8]) -> std::result::Result<(), String> {
        self.raw_put(&self.key(kind, claimed), body, claimed).await
    }

    /// Attempt a delete. The P2 bucket denies deletes, so this must fail.
    pub async fn try_delete(&self, kind: Kind, id: &Id) -> std::result::Result<(), String> {
        self.client
            .delete_object()
            .bucket(&self.bucket)
            .key(self.key(kind, id))
            .send()
            .await
            .map(|_| ())
            .map_err(|e| format!("{}", aws_sdk_s3::error::DisplayErrorContext(e)))
    }
}
