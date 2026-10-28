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

#[derive(Clone)]
pub struct S3Config {
    pub endpoint: String,
    pub bucket: String,
    pub region: String,
    pub access_key: String,
    pub secret_key: String,
    /// Key prefix (one per deployment in tests; empty in production).
    pub prefix: String,
    /// Garage's private S3 socket, for test corruption at rest only (`<p>GARAGE_S3_SOCKET`).
    pub garage_socket: Option<String>,
}

impl std::fmt::Debug for S3Config {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("S3Config").field("endpoint", &self.endpoint)
            .field("bucket", &self.bucket).field("region", &self.region)
            .field("access_key", &self.access_key)
            .field("secret_key", &"[REDACTED]").field("prefix", &self.prefix)
            .field("garage_socket", &self.garage_socket).finish()
    }
}

/// Matches the gateway's object bound, including content-address domain overhead.
pub const MAX_OBJECT_BYTES: usize = 65 * 1024 * 1024;

async fn read_bounded(mut body: ByteStream, cap: usize) -> std::result::Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    while let Some(chunk) = body.next().await {
        let chunk = chunk.map_err(|e| e.to_string())?;
        if !cfg!(feature = "mutate-unbounded-s3-read") && chunk.len() > cap.saturating_sub(bytes.len()) {
            return Err("S3 object exceeds byte limit".into());
        }
        bytes.extend_from_slice(&chunk);
    }
    Ok(bytes)
}

impl S3Config {
    pub fn from_env() -> Result<S3Config> {
        S3Config::from_env_with("PARALEAN_")
    }

    /// From `<p>S3_ENDPOINT`, `<p>S3_ACCESS_KEY`, ... (`PARALEAN_PEER_` names a peer deployment).
    pub fn from_env_with(p: &str) -> Result<S3Config> {
        let v = |k: &str| std::env::var(format!("{p}{k}")).map_err(|_| StoreError::Invalid(format!("{p}{k} is not set")));
        Ok(S3Config {
            endpoint: v("S3_ENDPOINT")?,
            bucket: v("S3_BUCKET").unwrap_or_else(|_| "paralean".into()),
            region: v("S3_REGION").unwrap_or_else(|_| "garage".into()),
            access_key: v("S3_ACCESS_KEY")?,
            secret_key: v("S3_SECRET_KEY")?,
            prefix: v("S3_PREFIX").unwrap_or_default(),
            garage_socket: v("GARAGE_S3_SOCKET").ok(),
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
    /// Store GC revival (gc.rs) only: the caller just saw `(kind, id)` acknowledged by its
    /// own verified PUT or GET.
    pub(crate) fn seen(kind: Kind, id: Id) -> Acked {
        Acked { kind, id }
    }
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
    /// The same bucket over Garage's private socket, bypassing the gateway (tests only).
    direct: Option<Client>,
    bucket: String,
    prefix: String,
    faults: Arc<Faults>,
    pub max_attempts: usize,
    /// `max-keys` of one listing page (tests lower it to exercise pagination).
    pub list_page: i32,
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
        let direct = cfg.garage_socket.as_ref().map(|socket| {
            Client::from_conf(conf.to_builder().http_client(garage_direct::UnixClient(socket.into())).build())
        });
        Payloads {
            client: Client::from_conf(conf),
            direct,
            bucket: cfg.bucket.clone(),
            prefix: cfg.prefix.clone(),
            faults,
            max_attempts: 8,
            list_page: 1000,
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
                // A gateway refusal is deterministic (e.g. the store GC is deleting this
                // key); retrying it only delays the caller's revival path.
                Err(e) if e.contains("AccessDenied") => {
                    last = e;
                    break;
                }
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
                    let mut bytes = match tokio::time::timeout(Duration::from_secs(60), read_bounded(o.body, MAX_OBJECT_BYTES)).await {
                        Ok(Ok(b)) => b,
                        Ok(Err(e)) => {
                            last = e.to_string();
                            continue;
                        }
                        Err(_) => { last = "S3 object body timed out".into(); continue; }
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
        Ok(self.list_sized(kind).await?.0.into_iter().map(|(id, _)| id).collect())
    }

    /// Every `(ID, stored size)` of a kind, and the number of listing pages. Follows the
    /// continuation token while the store reports truncation, never on a short page.
    pub async fn list_sized(&self, kind: Kind) -> Result<(Vec<(Id, u64)>, u64)> {
        let prefix = format!("{}obj/{}/", self.prefix, kind.name());
        let mut out = Vec::new();
        let mut pages = 0u64;
        let mut token: Option<String> = None;
        loop {
            let mut req = self.client.list_objects_v2().bucket(&self.bucket).prefix(&prefix).max_keys(self.list_page);
            if let Some(t) = &token {
                req = req.continuation_token(t);
            }
            let resp = req.send().await.map_err(|e| StoreError::S3(format!("{}", aws_sdk_s3::error::DisplayErrorContext(e))))?;
            pages += 1;
            for o in resp.contents() {
                if let Some(id) = o.key().and_then(|k| k.strip_prefix(&prefix)).and_then(Id::from_hex) {
                    out.push((id, o.size().unwrap_or(0).max(0) as u64));
                }
            }
            match resp.next_continuation_token() {
                Some(t) if resp.is_truncated() == Some(true) => token = Some(t.to_string()),
                _ if resp.is_truncated() == Some(true) => {
                    return Err(StoreError::S3(format!("listing {prefix} truncated without a continuation token")));
                }
                _ => break,
            }
        }
        Ok((out, pages))
    }

    // ----------------------------------------------------------- test and fault helpers

    /// Overwrite an object's key with arbitrary bytes and no checksum header: simulates
    /// corruption at rest (or a buggy writer). Readers must treat it as missing. The
    /// gateway refuses such a write, so it goes to Garage's private socket directly.
    pub async fn corrupt_at_rest(&self, kind: Kind, id: &Id, bytes: &[u8]) -> Result<()> {
        let direct = self.direct.as_ref()
            .ok_or_else(|| StoreError::S3("corruption at rest needs GARAGE_S3_SOCKET (Garage's private socket)".into()))?;
        direct
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

    /// Attempt to replace a stored object through the gateway: with other bytes, or by a
    /// server-side copy of another object. Either destroys the object as a delete would,
    /// so the gateway must refuse both.
    pub async fn try_overwrite(&self, kind: Kind, id: &Id, bytes: &[u8], copy_from: &Id) -> (std::result::Result<(), String>, std::result::Result<(), String>) {
        let err = |e| format!("{}", aws_sdk_s3::error::DisplayErrorContext(e));
        let put = self.client.put_object().bucket(&self.bucket).key(self.key(kind, id))
            .body(ByteStream::from(bytes.to_vec())).send().await.map(|_| ()).map_err(err);
        let copy = self.client.copy_object().bucket(&self.bucket).key(self.key(kind, id))
            .copy_source(format!("{}/{}", self.bucket, self.key(kind, copy_from))).send().await
            .map(|_| ()).map_err(|e| format!("{}", aws_sdk_s3::error::DisplayErrorContext(e)));
        (put, copy)
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

/// An S3 HTTP client over a Unix socket, so the SDK signs as usual but the request reaches
/// Garage's private S3 socket instead of the gateway. Used only to simulate corruption.
mod garage_direct {
    use std::path::PathBuf;

    use aws_smithy_runtime_api::client::http::{
        HttpClient, HttpConnector, HttpConnectorFuture, HttpConnectorSettings, SharedHttpConnector,
    };
    use aws_smithy_runtime_api::client::orchestrator::{HttpRequest, HttpResponse};
    use aws_smithy_runtime_api::client::result::ConnectorError;
    use aws_smithy_runtime_api::client::runtime_components::RuntimeComponents;
    use aws_smithy_types::body::SdkBody;
    use http_body_util::{BodyExt, Full};

    #[derive(Clone, Debug)]
    pub struct UnixClient(pub PathBuf);

    impl HttpClient for UnixClient {
        fn http_connector(&self, _: &HttpConnectorSettings, _: &RuntimeComponents) -> SharedHttpConnector {
            SharedHttpConnector::new(self.clone())
        }
    }

    impl HttpConnector for UnixClient {
        fn call(&self, request: HttpRequest) -> HttpConnectorFuture {
            let socket = self.0.clone();
            HttpConnectorFuture::new(async move {
                let io = |e: Box<dyn std::error::Error + Send + Sync>| ConnectorError::io(e);
                let request = request.try_into_http1x().map_err(|e| ConnectorError::other(e.into(), None))?;
                let (mut parts, body) = request.into_parts();
                let body = body.bytes().map(|b| b.to_vec())
                    .ok_or_else(|| ConnectorError::other("streaming bodies are not supported".into(), None))?;
                // Origin-form request target. The SDK signs Host from the endpoint URI and
                // leaves the header to the HTTP client, as hyper's pooled client would.
                if let Some(authority) = parts.uri.authority().cloned() {
                    let host = http::HeaderValue::from_str(authority.as_str())
                        .map_err(|e| ConnectorError::other(e.into(), None))?;
                    parts.headers.entry(http::header::HOST).or_insert(host);
                }
                parts.uri = parts.uri.path_and_query().map(|p| p.as_str()).unwrap_or("/").parse()
                    .map_err(|e: http::uri::InvalidUri| ConnectorError::other(e.into(), None))?;
                let stream = tokio::net::UnixStream::connect(&socket).await.map_err(|e| io(e.into()))?;
                let (mut sender, connection) = hyper::client::conn::http1::handshake(hyper_util::rt::TokioIo::new(stream))
                    .await.map_err(|e| io(e.into()))?;
                tokio::spawn(async move { let _ = connection.await; });
                let response = sender.send_request(http::Request::from_parts(parts, Full::new(bytes::Bytes::from(body))))
                    .await.map_err(|e| io(e.into()))?;
                let (parts, body) = response.into_parts();
                let body = body.collect().await.map_err(|e| io(e.into()))?.to_bytes();
                HttpResponse::try_from(http::Response::from_parts(parts, SdkBody::from(body)))
                    .map_err(|e| ConnectorError::other(e.into(), None))
            })
        }
    }
}

#[cfg(test)]
mod security_tests {
    use super::*;
    #[tokio::test]
    async fn oversized_s3_body_is_rejected_before_hashing() {
        assert!(read_bounded(ByteStream::from(vec![0; 4097]), 4096).await.is_err());
        assert_eq!(read_bounded(ByteStream::from(vec![7; 4096]), 4096).await.unwrap().len(), 4096);
    }
    #[test]
    fn config_debug_redacts_credentials() {
        let config = S3Config { endpoint: "http://local".into(), bucket: "b".into(), region: "r".into(),
            access_key: "public".into(), secret_key: "do-not-log-secret".into(), prefix: "".into(), garage_socket: None };
        assert!(!format!("{config:?}").contains(&config.secret_key));
    }
}
