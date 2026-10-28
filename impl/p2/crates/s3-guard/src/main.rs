//! s3-guard: a byte-for-byte S3 passthrough that refuses every request that could delete
//! or expire stored objects, or change the bucket's configuration.
//!
//! store.md requires that "the bucket denies `DeleteObject` (or uses Object Lock)". Garage
//! has neither bucket policies nor Object Lock, and a Garage key with write permission may
//! delete. The P2 cluster therefore exposes Garage only through this gateway. Requests are
//! forwarded unchanged (method, path, query, headers including `Host`, body), so SigV4
//! signatures computed against the gateway's address verify at Garage, and clients use the
//! plain S3 API: replacing Garage by another S3 store changes only the upstream address.
//!
//! Allowed: GET and HEAD; and PUT of one whole object under a content-addressed key
//! `.../obj/<kind>/<sha256 hex>` whose body hashes to that key (a retry rewrites the same
//! bytes). Refused (403 `AccessDenied`): every POST (DeleteObjects, multipart uploads);
//! PUT with any sub-resource query, server-side copy or aws-chunked framing; PUT of any
//! other key, including bucket creation; PUT of a body that does not hash to its key,
//! which would destroy the stored object as surely as a delete; and every DELETE except
//! the GC principal's below.
//!
//! GC deletes (off unless both `--gc-access-key` and `--gc-delete-prefix` are given): only
//! an object `DELETE` without a query, bearing that SigV4 access key (an identity selector:
//! Garage verifies the signature and authorizes the key, so keep Garage inaccessible to
//! clients), naming path-style a key under one of the configured
//! `--gc-delete-prefix BUCKET/KEYPREFIX` entries. No decoded key containing `obj/` is ever
//! deletable: every P2 content kind (groups, capsules, chunks, snapshots, manifests,
//! blobs, markers and tombstones) lives under `<deployment>obj/<kind>/`, and those objects
//! are reachable from live heads, checkpoints and tombstone lineage. Retiring them needs a
//! distributed retirement protocol that does not exist yet. Bucket and configuration
//! deletes are refused even for GC.
//!
//! Store-GC content deletes (off unless `--gc-fdb-cluster FILE` and at least one
//! `--gc-deployment NAME[=BUCKET/KEYPREFIX]` are given, with `--gc-access-key`;
//! docs/w4-rest-log.md Design 1): a GC-principal `DELETE` of exactly
//! `<BUCKET/KEYPREFIX>obj/<kind>/<64 hex>` for a configured deployment is admitted only after
//! an FDB transaction moves `gcobj/<kind>/<id>` under `("paralean", NAME)` from `Doomed` (or an
//! interrupted `Deleting`) to `Deleting{nonce}`; it is then forwarded, and on Garage's success
//! `Deleting{nonce}` becomes `Gone{gc/clock}`. Any other principal, an unmarked key or a key
//! in another state, a query, a virtual-hosted request and every bucket, configuration or
//! bulk delete stay refused. A content PUT under a configured deployment whose key is
//! `Doomed` or `Deleting` is refused, so a revival cannot land under an in-flight delete.
//! The non-content `--gc-delete-prefix` rule above is unchanged.
//!
//! `--upstream` takes a comma-separated list (the S3 ports of a multi-node Garage cluster).
//! A request goes to the first upstream that accepts the connection, so the gateway rides
//! through the loss of a node; the request body is buffered for that.

use std::collections::HashMap;
use std::convert::Infallible;
use std::net::{IpAddr, SocketAddr};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use bytes::Bytes;
use http_body_util::{combinators::BoxBody, BodyExt, Full, Limited};
use hyper::body::Incoming;
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::header::AUTHORIZATION;
use hyper::{HeaderMap, Method, Request, Response, StatusCode, Uri};
use sha2::{Digest, Sha256};
use hyper_util::client::legacy::{connect::HttpConnector, Client};
use hyper_util::rt::{TokioExecutor, TokioIo};
use tokio::net::{TcpListener, UnixStream};

type Body = BoxBody<Bytes, hyper::Error>;

const MAX_BODY: usize = 65 * 1024 * 1024; // 64 MiB chunk plus domain/encoding
const MAX_CONNECTIONS: usize = 16;
/// One source address may hold only part of the pool, so it cannot lock out the others.
const MAX_CONNECTIONS_PER_SOURCE: usize = 4;

/// Connection admission: at most `total` connections, `per_source` of them from one address.
/// A connection over either bound is refused at once; a slot is released when dropped.
struct Admission {
    total: usize,
    per_source: usize,
    held: Mutex<(usize, HashMap<IpAddr, usize>)>,
}

struct Slot {
    owner: Arc<Admission>,
    source: IpAddr,
}

impl Admission {
    fn new(total: usize, per_source: usize) -> Arc<Self> {
        Arc::new(Admission { total, per_source, held: Mutex::new((0, HashMap::new())) })
    }
    /// The gateway's limits: `MAX_CONNECTIONS` in all, `MAX_CONNECTIONS_PER_SOURCE` per address.
    fn gateway() -> Arc<Self> {
        let per_source = if cfg!(feature = "mutate-no-per-source-admission") { usize::MAX } else { MAX_CONNECTIONS_PER_SOURCE };
        Admission::new(MAX_CONNECTIONS, per_source)
    }
    fn try_admit(self: &Arc<Self>, source: IpAddr) -> Option<Slot> {
        let source = source.to_canonical();
        let mut held = self.held.lock().unwrap();
        let (total, sources) = &mut *held;
        let n = sources.entry(source).or_insert(0);
        if *total >= self.total || *n >= self.per_source {
            if *n == 0 {
                sources.remove(&source);
            }
            return None;
        }
        *n += 1;
        *total += 1;
        Some(Slot { owner: self.clone(), source })
    }
}

impl Drop for Slot {
    fn drop(&mut self) {
        let mut held = self.owner.held.lock().unwrap();
        let (total, sources) = &mut *held;
        *total -= 1;
        if let Some(n) = sources.get_mut(&self.source) {
            *n -= 1;
            if *n == 0 {
                sources.remove(&self.source);
            }
        }
    }
}

/// Decode a query key before matching S3 subresources. A malformed escape or
/// non-UTF-8 key fails closed, and a remaining '%' cannot hide a second decode.
fn query_key(raw: &str) -> Option<String> {
    if cfg!(feature = "mutate-no-query-key-decode") {
        return Some(raw.to_string());
    }
    let bytes = raw.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            let hex = |b: u8| match b {
                b'0'..=b'9' => Some(b - b'0'),
                b'a'..=b'f' => Some(b - b'a' + 10),
                b'A'..=b'F' => Some(b - b'A' + 10),
                _ => None,
            };
            let hi = hex(*bytes.get(i + 1)?)?;
            let lo = hex(*bytes.get(i + 2)?)?;
            decoded.push((hi << 4) | lo);
            i += 3;
        } else {
            decoded.push(bytes[i]);
            i += 1;
        }
    }
    let key = String::from_utf8(decoded).ok()?;
    // Different S3 backends may split before or after decoding. Never forward a
    // key whose decoded form can introduce a second separator.
    (!key.chars().any(|c| matches!(c, '%' | '&' | '='))).then_some(key)
}

// ---------------------------------------------------------------- store-GC content deletes

/// `gcobj/<kind>/<id>` (paralean-store `gc::GcState`; the byte layout is shared and covered by
/// `gc_state_layout_matches_the_store`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GcState {
    Sighted,
    Doomed { size: u64 },
    Deleting { nonce: [u8; 16], size: u64 },
    Gone,
}

impl GcState {
    fn decode(v: &[u8]) -> Option<GcState> {
        let u = |b: &[u8]| u64::from_be_bytes(b.try_into().unwrap());
        match (v.first(), v.len()) {
            (Some(1), 9) => Some(GcState::Sighted),
            (Some(2), 17) => Some(GcState::Doomed { size: u(&v[9..17]) }),
            (Some(3), 25) => Some(GcState::Deleting { nonce: v[1..17].try_into().unwrap(), size: u(&v[17..25]) }),
            (Some(4), 25) => Some(GcState::Gone),
            _ => None,
        }
    }
}

fn deleting(nonce: [u8; 16], size: u64) -> Vec<u8> {
    let mut v = vec![3];
    v.extend_from_slice(&nonce);
    v.extend_from_slice(&size.to_be_bytes());
    v
}

fn gone(clock: u64, nonce: [u8; 16]) -> Vec<u8> {
    let mut v = vec![4];
    v.extend_from_slice(&clock.to_be_bytes());
    v.extend_from_slice(&nonce);
    v
}

/// A content delete may proceed only for an object the store GC doomed (or whose earlier
/// delete was interrupted after admission). An unmarked, sighted or gone key is refused.
fn gc_delete_admits(state: Option<GcState>) -> bool {
    if cfg!(feature = "mutate-storegc-guard-no-mark-check") {
        return true;
    }
    matches!(state, Some(GcState::Doomed { .. } | GcState::Deleting { .. }))
}

/// A content PUT is refused while the object is doomed or being deleted.
fn gc_put_admits(state: Option<GcState>) -> bool {
    !matches!(state, Some(GcState::Doomed { .. } | GcState::Deleting { .. }))
}

const CONTENT_KINDS: [&str; 8] = ["group", "chunk", "capsule", "snapshot", "manifest", "blob", "marker", "tombstone"];

/// One deployment whose content keys the GC principal may delete under the FDB protocol.
#[derive(Clone, Debug)]
struct GcDeployment {
    /// `BUCKET/KEYPREFIX` of the deployment's objects (`KEYPREFIX` may be empty).
    prefix: String,
    root: foundationdb::tuple::Subspace,
}

/// The configured deployment, kind and ID a request path names exactly as
/// `<prefix>obj/<kind>/<64 lowercase hex>`, after strict path decoding.
fn content_target<'a>(raw_path: &str, deployments: &'a [GcDeployment]) -> Option<(&'a GcDeployment, &'static str, [u8; 32])> {
    let path = object_path(raw_path)?;
    for d in deployments {
        let Some(rest) = path.strip_prefix(d.prefix.as_str()) else { continue };
        let mut parts = rest.split('/');
        let (Some("obj"), Some(kind), Some(hex), None) = (parts.next(), parts.next(), parts.next(), parts.next()) else { continue };
        let Some(kind) = CONTENT_KINDS.iter().copied().find(|k| *k == kind) else { continue };
        if hex.len() != 64 || !hex.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
            continue;
        }
        let mut id = [0; 32];
        for (i, byte) in id.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).ok()?;
        }
        return Some((d, kind, id));
    }
    None
}

fn gcobj_key(d: &GcDeployment, kind: &str, id: &[u8; 32]) -> Vec<u8> {
    d.root.pack(&("gcobj", kind, foundationdb::tuple::Bytes::from(&id[..])))
}

/// Why a content delete for a configured deployment is refused before its FDB mark, if it is.
fn content_delete_refusal(uri: &Uri, headers: &HeaderMap, gc: &GcPolicy) -> Option<&'static str> {
    // The only query admitted is the SDK's operation marker, spelled exactly; a version,
    // sub-resource or any other (or re-encoded) query is refused.
    if uri.query().is_some_and(|q| q != "x-id=DeleteObject") {
        return Some("content deletes take no query but x-id=DeleteObject");
    }
    if !cfg!(feature = "mutate-storegc-guard-any-principal") && !gc_principal(headers, gc.key.as_deref()) {
        return Some("content deletes require the configured GC principal");
    }
    if !path_style(headers) {
        return Some("content deletes must be path-style");
    }
    None
}

fn valid_gc_deployment_prefix(prefix: &str) -> bool {
    prefix.split_once('/').is_some_and(|(bucket, _)| !bucket.is_empty())
        && prefix.ends_with('/')
        && !prefix.contains(PROTECTED_SEGMENT)
        && object_path(&format!("/{prefix}x")).as_deref() == Some(&format!("{prefix}x"))
}

fn nonce() -> [u8; 16] {
    use std::io::Read;
    let mut n = [0; 16];
    std::fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut n)).expect("read /dev/urandom");
    n
}

/// `Doomed` (or `Deleting`) → `Deleting{nonce}`; `None` if the key is not admissible.
async fn gc_mark_deleting(db: &foundationdb::Database, key: &[u8]) -> Result<Option<[u8; 16]>, String> {
    let mut trx = db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        let state = match trx.get(key, false).await {
            Ok(v) => v.and_then(|v| GcState::decode(&v)),
            Err(e) => { trx = trx.on_error(e).await.map_err(|e| e.to_string())?; continue; }
        };
        if !gc_delete_admits(state) {
            return Ok(None);
        }
        let size = match state { Some(GcState::Doomed { size } | GcState::Deleting { size, .. }) => size, _ => 0 };
        let n = nonce();
        trx.set(key, &deleting(n, size));
        match trx.commit().await {
            Ok(_) => return Ok(Some(n)),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("store-GC mark outcome unresolved".into())
}

/// `Deleting{nonce}` → `Gone{gc/clock}` after Garage acknowledged the delete.
async fn gc_mark_gone(db: &foundationdb::Database, key: &[u8], clock_key: &[u8], n: [u8; 16]) -> Result<bool, String> {
    let mut trx = db.create_trx().map_err(|e| e.to_string())?;
    for _ in 0..60 {
        let read = async {
            let state = trx.get(key, false).await?.and_then(|v| GcState::decode(&v));
            let clock = trx.get(clock_key, false).await?.and_then(|v| <[u8; 8]>::try_from(&v[..]).ok()).map(u64::from_be_bytes).unwrap_or(0);
            Ok::<_, foundationdb::FdbError>((state, clock))
        };
        let (state, clock) = match read.await {
            Ok(x) => x,
            Err(e) => { trx = trx.on_error(e).await.map_err(|e| e.to_string())?; continue; }
        };
        if !matches!(state, Some(GcState::Deleting { nonce, .. }) if nonce == n) {
            return Ok(false);
        }
        trx.set(key, &gone(clock, n));
        match trx.commit().await {
            Ok(_) => return Ok(true),
            Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
        }
    }
    Err("store-GC completion outcome unresolved".into())
}

async fn gc_put_check(db: &foundationdb::Database, key: &[u8]) -> Result<bool, String> {
    let mut trx = db.create_trx().map_err(|e| e.to_string())?;
    loop {
        match trx.get(key, false).await {
            Ok(v) => return Ok(gc_put_admits(v.and_then(|v| GcState::decode(&v)))),
            Err(e) => trx = trx.on_error(e).await.map_err(|e| e.to_string())?,
        }
    }
}

/// The P2 content-kind segment. A key containing it is never a GC candidate.
const PROTECTED_SEGMENT: &str = "obj/";

/// The GC principal's delete boundary: allowlisted `bucket/key` prefixes.
#[derive(Clone, Default)]
struct GcPolicy {
    key: Option<String>,
    prefixes: Vec<String>,
    /// Store-GC content deletes: the FDB database and the configured deployments.
    store: Option<(Arc<foundationdb::Database>, Vec<GcDeployment>)>,
}

/// Decode an object path for allowlist matching. Fails closed on malformed or
/// double escapes, dot segments, empty segments, backslashes and control bytes,
/// so an encoded `obj/` or traversal cannot pass a plain prefix test.
fn object_path(raw: &str) -> Option<String> {
    let bytes = raw.as_bytes();
    let mut decoded = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            let hex = |b: u8| (b as char).to_digit(16).map(|d| d as u8);
            let hi = hex(*bytes.get(i + 1)?)?;
            let lo = hex(*bytes.get(i + 2)?)?;
            decoded.push((hi << 4) | lo);
            i += 3;
        } else {
            decoded.push(bytes[i]);
            i += 1;
        }
    }
    let path = String::from_utf8(decoded).ok()?;
    let rest = path.strip_prefix('/')?;
    let bad = rest.chars().any(|c| c == '%' || c == '\\' || c.is_control())
        || rest.split('/').any(|seg| seg.is_empty() || seg == "." || seg == "..");
    (!bad).then(|| rest.to_string())
}

/// Path-style addressing only: a virtual-hosted request names its bucket in
/// `Host`, which would make the path's first segment part of the key.
fn path_style(headers: &HeaderMap) -> bool {
    let Some(host) = headers.get(hyper::header::HOST).and_then(|v| v.to_str().ok()) else {
        return false;
    };
    let name = if let Some(v6) = host.strip_prefix('[') {
        v6.split(']').next().unwrap_or("")
    } else {
        host.rsplit_once(':').map(|(n, _)| n).unwrap_or(host)
    };
    name == "localhost" || name.parse::<std::net::IpAddr>().is_ok()
}

fn gc_delete_allowed(uri: &Uri, headers: &HeaderMap, policy: &GcPolicy) -> bool {
    if cfg!(feature = "mutate-no-gc-prefix-check") {
        return true;
    }
    let Some(path) = object_path(uri.path()) else {
        return false;
    };
    let Some((_bucket, key)) = path.split_once('/') else {
        return false;
    };
    path_style(headers)
        && !key.contains(PROTECTED_SEGMENT)
        && policy
            .prefixes
            .iter()
            .any(|prefix| path.starts_with(prefix.as_str()) && path.len() > prefix.len())
}

/// Reject an allowlist entry that could cover protected content.
fn valid_gc_prefix(prefix: &str) -> bool {
    prefix
        .split_once('/')
        .is_some_and(|(bucket, key)| !bucket.is_empty() && !key.is_empty())
        && !prefix.contains(PROTECTED_SEGMENT)
        && object_path(&format!("/{prefix}x")).as_deref() == Some(&format!("{prefix}x"))
}

/// The configured access key is an identity selector, not an authentication secret.
/// Garage verifies the SigV4 signature before performing any forwarded delete.
fn gc_principal(headers: &HeaderMap, configured_key: Option<&str>) -> bool {
    let Some(key) = configured_key.filter(|key| !key.is_empty()) else {
        return false;
    };
    let mut auth = headers.get_all(AUTHORIZATION).iter();
    let Some(value) = auth.next() else {
        return false;
    };
    if auth.next().is_some() {
        return false;
    }
    let Ok(value) = value.to_str() else {
        return false;
    };
    let Some(fields) = value.strip_prefix("AWS4-HMAC-SHA256 ") else {
        return false;
    };
    let mut credential = None;
    let mut signature = None;
    let mut signed_headers = None;
    for part in fields.split(',').map(str::trim) {
        let Some((name, value)) = part.split_once('=') else {
            return false;
        };
        match name {
            "Credential" if credential.replace(value).is_none() => {}
            "Signature" if signature.replace(value).is_none() => {}
            "SignedHeaders" if signed_headers.replace(value).is_none() => {}
            _ => return false,
        }
    }
    credential.is_some_and(|value| {
        value
            .split_once('/')
            .is_some_and(|(access_key, scope)| access_key == key && !scope.is_empty())
    }) && signature.is_some_and(|value| !value.is_empty())
        && signed_headers.is_some_and(|value| !value.is_empty())
}

/// The content address a PUT path names: `<bucket>/<prefix>obj/<kind>/<64 hex>`. The
/// last three segments must be literal (no percent-encoding), so the key Garage stores is
/// exactly the one checked here.
fn content_address(path: &str) -> Option<[u8; 32]> {
    let segments: Vec<&str> = path.trim_start_matches('/').split('/').collect();
    let [.., bucket_or_prefix, obj, kind, hex] = segments.as_slice() else { return None };
    let _ = bucket_or_prefix;
    let lower_hex = |s: &str| s.len() == 64 && s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b));
    if *obj != "obj" || kind.is_empty() || !kind.bytes().all(|b| b.is_ascii_lowercase()) || !lower_hex(hex) {
        return None;
    }
    let mut id = [0; 32];
    for (i, byte) in id.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hex[2 * i..2 * i + 2], 16).ok()?;
    }
    Some(id)
}

/// Why a request is refused, or `None` if it may pass. A writer may only add objects:
/// every accepted PUT is a whole content-addressed object (checked against its body in
/// `handle`), so an existing key can only be rewritten with its own bytes. Overwriting
/// an object with other bytes would destroy it as surely as deleting it.
fn refusal(method: &Method, uri: &Uri, headers: &HeaderMap, gc: &GcPolicy) -> Option<&'static str> {
    let query = uri.query().unwrap_or("");
    let keys: Option<Vec<String>> = query
        .split('&')
        .filter(|s| !s.is_empty())
        .map(|kv| query_key(kv.split('=').next().unwrap_or("")))
        .collect();
    let Some(keys) = keys else { return Some("invalid query encoding"); };
    if cfg!(feature = "mutate-allow-delete") { return None; }
    if method == Method::GET || method == Method::HEAD {
        return None;
    }
    if method == Method::DELETE {
        // A GC principal may delete only an object. Bucket and bucket-configuration
        // deletion remains impossible through this gateway, even for GC.
        let path = uri.path().trim_start_matches('/');
        let is_bucket_level = !path.contains('/') || path.ends_with('/') && path.matches('/').count() == 1;
        if (!cfg!(feature = "mutate-no-bucket-delete-check") && is_bucket_level) || !keys.is_empty() {
            return Some("bucket and configuration deletes are denied");
        }
        if !cfg!(feature = "mutate-no-gc-principal-check") && !gc_principal(headers, gc.key.as_deref()) {
            return Some("object deletes require the configured GC principal");
        }
        if !gc_delete_allowed(uri, headers, gc) {
            return Some("GC deletes are limited to allowlisted non-content prefixes");
        }
        return None;
    }
    if method != Method::PUT {
        // POST carries DeleteObjects and multipart uploads, which assemble an object
        // the gateway never sees whole. The store uses neither.
        return Some("only whole-object PUT, GET and HEAD are allowed");
    }
    if keys.iter().any(|k| k != "x-id") {
        return Some("bucket and object configuration changes and multipart uploads are denied");
    }
    if cfg!(feature = "mutate-allow-overwrite") { return None; }
    if headers.keys().any(|h| h.as_str().starts_with("x-amz-copy-source")) {
        return Some("server-side copy is denied: the gateway must see the object's bytes");
    }
    let header = |name: &str| headers.get_all(name).iter().any(|v| v.to_str().map_or(true, |s| s.to_ascii_lowercase().contains("aws-chunked") || s.starts_with("STREAMING-")));
    if header("content-encoding") || header("x-amz-content-sha256") {
        return Some("aws-chunked uploads are denied: send the object as one body");
    }
    if content_address(uri.path()).is_none() {
        return Some("PUT must name a content-addressed key obj/<kind>/<sha256 hex>");
    }
    None
}

/// Whether a PUT body may be stored under its key: its SHA-256 must be the key's ID.
fn content_matches(method: &Method, uri: &Uri, body: &[u8]) -> bool {
    if method != Method::PUT || cfg!(feature = "mutate-allow-overwrite") || cfg!(feature = "mutate-allow-delete") {
        return true;
    }
    content_address(uri.path()).is_some_and(|id| <[u8; 32]>::from(Sha256::digest(body)) == id)
}

fn denied(msg: &str) -> Response<Body> {
    let xml = format!(
        "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<Error><Code>AccessDenied</Code><Message>{msg}</Message></Error>"
    );
    Response::builder()
        .status(StatusCode::FORBIDDEN)
        .header("content-type", "application/xml")
        .body(Full::new(Bytes::from(xml)).map_err(|n: Infallible| match n {}).boxed())
        .unwrap()
}

async fn handle(
    client: Client<HttpConnector, Full<Bytes>>,
    upstreams: Arc<Vec<String>>,
    gc: Arc<GcPolicy>,
    req: Request<Incoming>,
) -> Result<Response<Body>, Infallible> {
    // Store-GC content keys of configured deployments: deletes follow the FDB protocol,
    // PUTs are refused while the key is doomed or being deleted.
    if let Some((db, deployments)) = &gc.store {
        let target = content_target(req.uri().path(), deployments).map(|(d, kind, id)| (gcobj_key(d, kind, &id), d.root.pack(&("gc", "clock"))));
        if req.method() == Method::DELETE {
            if let Some((key, clock_key)) = target {
                if let Some(msg) = content_delete_refusal(req.uri(), req.headers(), &gc) {
                    eprintln!("s3-guard: refused DELETE");
                    return Ok(denied(msg));
                }
                let n = match gc_mark_deleting(db, &key).await {
                    Ok(Some(n)) => n,
                    Ok(None) => return Ok(denied("the object is not doomed by the store GC")),
                    Err(e) => return Ok(error(StatusCode::SERVICE_UNAVAILABLE, &format!("store-GC state: {e}"))),
                };
                let (parts, _) = req.into_parts();
                let resp = forward(&client, &upstreams, parts, Bytes::new()).await;
                if resp.status().is_success() {
                    // On failure the state stays Deleting (refused to writers); a retried
                    // DELETE is admitted again and completes the transition.
                    if let Err(e) = gc_mark_gone(db, &key, &clock_key, n).await {
                        return Ok(error(StatusCode::SERVICE_UNAVAILABLE, &format!("store-GC completion: {e}")));
                    }
                }
                return Ok(resp);
            }
        } else if req.method() == Method::PUT {
            if object_path(req.uri().path()).is_none() {
                return Ok(denied("malformed object path"));
            }
            if let Some((key, _)) = target {
                match gc_put_check(db, &key).await {
                    Ok(true) => {}
                    Ok(false) => return Ok(denied("the store GC is deleting this object; retry after it is gone")),
                    Err(e) => return Ok(error(StatusCode::SERVICE_UNAVAILABLE, &format!("store-GC state: {e}"))),
                }
            }
        }
    }
    if let Some(msg) = refusal(req.method(), req.uri(), req.headers(), &gc) {
        // Query strings may contain presigned credentials; never log them.
        eprintln!("s3-guard: refused {}", req.method());
        return Ok(denied(msg));
    }
    let (parts, body) = req.into_parts();
    let cap = if cfg!(feature = "mutate-unbounded-body") { usize::MAX } else { MAX_BODY };
    let body = match Limited::new(body, cap).collect().await {
        Ok(b) => b.to_bytes(),
        Err(e) => return Ok(error(StatusCode::BAD_REQUEST, &format!("request body: {e}"))),
    };
    if !content_matches(&parts.method, &parts.uri, &body) {
        eprintln!("s3-guard: refused PUT whose body does not hash to its key");
        return Ok(denied("the body's SHA-256 differs from the object key"));
    }
    Ok(forward(&client, &upstreams, parts, body).await)
}

async fn forward(
    client: &Client<HttpConnector, Full<Bytes>>,
    upstreams: &[String],
    parts: hyper::http::request::Parts,
    body: Bytes,
) -> Response<Body> {
    let pq = parts.uri.path_and_query().map(|p| p.as_str().to_string()).unwrap_or_else(|| "/".into());
    let mut last = String::new();
    for up in upstreams.iter() {
        let mut r = Request::from_parts(parts.clone(), Full::new(body.clone()));
        if let Some(path) = up.strip_prefix("unix:") {
            let stream = match UnixStream::connect(path).await {
                Ok(stream) => stream,
                Err(e) => { last = e.to_string(); continue; }
            };
            *r.uri_mut() = pq.parse().unwrap();
            let (mut sender, connection) = match hyper::client::conn::http1::handshake(TokioIo::new(stream)).await {
                Ok(pair) => pair,
                Err(_) => return error(StatusCode::BAD_GATEWAY, "upstream handshake failed"),
            };
            tokio::spawn(async move { let _ = connection.await; });
            return match sender.send_request(r).await {
                Ok(resp) => resp.map(|b| b.boxed()),
                Err(_) => error(StatusCode::BAD_GATEWAY, "upstream error"),
            };
        }
        *r.uri_mut() = format!("http://{up}{pq}").parse().unwrap();
        match client.request(r).await {
            Ok(resp) => return resp.map(|b| b.boxed()),
            // Only a refused or failed connection moves on: a request that reached a node
            // may have had an effect, and its reply is that node's answer.
            Err(e) if e.is_connect() => last = format!("{up}: {e}"),
            Err(e) => {
                eprintln!("s3-guard: upstream {up} error: {e}");
                return error(StatusCode::BAD_GATEWAY, "upstream error");
            }
        }
    }
    eprintln!("s3-guard: no upstream reachable ({last})");
    error(StatusCode::BAD_GATEWAY, "no upstream reachable")
}

fn error(status: StatusCode, msg: &str) -> Response<Body> {
    Response::builder()
        .status(status)
        .body(Full::new(Bytes::from(msg.to_string())).map_err(|n: Infallible| match n {}).boxed())
        .unwrap()
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut listen: SocketAddr = "127.0.0.1:18433".parse()?;
    let mut upstream = String::new();
    let mut gc = GcPolicy::default();
    let mut gc_cluster: Option<String> = None;
    let mut gc_deployments: Vec<GcDeployment> = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--listen" => listen = args.next().ok_or("--listen needs a value")?.parse()?,
            "--upstream" => upstream = args.next().ok_or("--upstream needs a value")?,
            "--gc-access-key" => gc.key = Some(args.next().ok_or("--gc-access-key needs a value")?),
            "--gc-fdb-cluster" => gc_cluster = Some(args.next().ok_or("--gc-fdb-cluster needs a value")?),
            "--gc-deployment" => {
                let spec = args.next().ok_or("--gc-deployment needs a value")?;
                let (name, prefix) = match spec.split_once('=') {
                    Some((n, p)) => (n.to_string(), p.to_string()),
                    None => (spec.clone(), format!("paralean/{spec}/")),
                };
                if name.is_empty() || !name.bytes().all(|b| b.is_ascii_graphic()) || !valid_gc_deployment_prefix(&prefix) {
                    return Err(format!("--gc-deployment {spec:?} must be NAME[=BUCKET/KEYPREFIX/] outside {PROTECTED_SEGMENT}").into());
                }
                gc_deployments.push(GcDeployment { prefix, root: foundationdb::tuple::Subspace::from(("paralean", name.as_str())) });
            }
            "--gc-delete-prefix" => {
                let prefix = args.next().ok_or("--gc-delete-prefix needs a value")?;
                if !valid_gc_prefix(&prefix) {
                    return Err(format!("--gc-delete-prefix {prefix:?} must be BUCKET/KEYPREFIX outside {PROTECTED_SEGMENT}").into());
                }
                gc.prefixes.push(prefix)
            }
            other => return Err(format!("unknown argument {other}").into()),
        }
    }
    if upstream.is_empty() { return Err("--upstream unix:/private/path/s3.sock is required".into()); }
    if gc_cluster.is_some() != !gc_deployments.is_empty() {
        return Err("--gc-fdb-cluster and --gc-deployment must be given together".into());
    }
    if gc.key.is_some() != (!gc.prefixes.is_empty() || gc_cluster.is_some()) {
        return Err("--gc-access-key needs --gc-delete-prefix or --gc-fdb-cluster/--gc-deployment, and they need it".into());
    }
    // FDB's network thread lives for the process (the gateway is stopped by a signal).
    let _network = match &gc_cluster {
        Some(cluster) => {
            let builder = foundationdb::api::FdbApiBuilder::default().set_runtime_version(730).build()?;
            let network = unsafe { builder.boot() }?;
            let db = foundationdb::Database::new(Some(cluster))?;
            gc.store = Some((Arc::new(db), gc_deployments));
            eprintln!("s3-guard: store-GC content deletes enabled ({cluster})");
            Some(network)
        }
        None => None,
    };
    let gc = Arc::new(gc);
    let listener = TcpListener::bind(listen).await?;
    eprintln!("s3-guard: listening on {listen}, upstream {upstream}");
    let client: Client<HttpConnector, Full<Bytes>> = Client::builder(TokioExecutor::new()).build_http();
    let upstreams: Arc<Vec<String>> = Arc::new(upstream.split(',').map(str::to_string).collect());
    let admission = Admission::gateway();
    loop {
        let (stream, peer) = listener.accept().await?;
        let Some(permit) = admission.try_admit(peer.ip()) else { continue };
        let client = client.clone();
        let upstreams = upstreams.clone();
        let gc = gc.clone();
        tokio::spawn(async move {
            let _permit = permit;
            let svc = service_fn(move |req| handle(client.clone(), upstreams.clone(), gc.clone(), req));
            // Includes headers, chunked request bodies, upstream and response. No
            // keepalive lets an idle peer hold an admission slot without a bound.
            let mut builder = http1::Builder::new();
            builder.keep_alive(false).max_buf_size(32768);
            let _ = tokio::time::timeout(Duration::from_secs(60),
                builder.serve_connection(TokioIo::new(stream), svc)).await;
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const KEY: &str = "/b/p/obj/group/9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08";
    fn r(m: Method, u: &str) -> bool { refusal(&m, &u.parse().unwrap(), &HeaderMap::new(), &GcPolicy::default()).is_some() }
    fn with(m: Method, u: &str, name: &'static str, value: &str) -> bool {
        let mut h = HeaderMap::new();
        h.insert(name, value.parse().unwrap());
        refusal(&m, &u.parse().unwrap(), &h, &GcPolicy::default()).is_some()
    }
    #[test]
    fn refuses_deletes_and_config() {
        assert!(r(Method::DELETE, "/b/obj/x"));
        assert!(r(Method::DELETE, "/b"));
        assert!(r(Method::POST, "/b?delete"));
        assert!(r(Method::POST, "/b?delete="));
        assert!(r(Method::PUT, "/b?lifecycle"));
        assert!(r(Method::PUT, "/b?policy"));
        assert!(r(Method::PUT, "/b"));
        assert!(!r(Method::PUT, KEY));
        assert!(!r(Method::PUT, &format!("{KEY}?x-id=PutObject")));
        assert!(!r(Method::GET, "/b?list-type=2&prefix=obj/"));
        assert!(!r(Method::HEAD, "/b/obj/x"));
    }
    #[test]
    fn encoded_and_unknown_mutations_are_denied() {
        for url in ["/b?%64elete", "/b?%64%65lete=", "/b?x=1&delete", "/b?delete&uploads",
            "/b/obj?%64elete", "/b?%zz", "/b?uploads", "/b/obj/x?uploads", "/b/obj/x?uploadId=1"] {
            assert!(r(Method::POST, url), "{url}");
        }
        for url in ["/b?%6cifecycle", "/b?acl", "/b?x=1", "/b/obj?tagging", "/b/obj?%70olicy"] {
            assert!(r(Method::PUT, url), "{url}");
        }
        assert!(r(Method::PATCH, KEY));
    }
    #[test]
    fn overwrites_copies_and_unaddressed_keys_are_denied() {
        // Multipart parts and server-side copies never pass a whole body through here.
        assert!(r(Method::PUT, &format!("{KEY}?partNumber=1&uploadId=abc")));
        assert!(with(Method::PUT, KEY, "x-amz-copy-source", "/b/p/obj/group/other"));
        assert!(with(Method::PUT, KEY, "x-amz-copy-source-range", "bytes=0-1"));
        assert!(with(Method::PUT, KEY, "content-encoding", "aws-chunked"));
        assert!(with(Method::PUT, KEY, "x-amz-content-sha256", "STREAMING-UNSIGNED-PAYLOAD-TRAILER"));
        for url in ["/b/p/obj/group/abcd", "/b/p/obj/Group/9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08",
            "/b/p/obj/group/9F86D081884C7D659A2FEAA0C55AD015A3BF4F1B2B0B822CD15D6C15B0F00A08",
            "/b/p/obj/group/%39f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08",
            "/b/p/notobj/group/9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08", "/b/p/other"] {
            assert!(r(Method::PUT, url), "{url}");
        }
        // SHA-256("test"): the same bytes may be written again; other bytes may not.
        let uri: Uri = KEY.parse().unwrap();
        assert!(content_matches(&Method::PUT, &uri, b"test"));
        assert!(!content_matches(&Method::PUT, &uri, b"rot"));
        assert!(!content_matches(&Method::PUT, &uri, b""));
    }
    #[test]
    fn one_source_cannot_hold_every_connection_slot() {
        let admission = Admission::gateway();
        let ip = |s: &str| s.parse::<IpAddr>().unwrap();
        let mut a: Vec<Slot> = (0..MAX_CONNECTIONS_PER_SOURCE).map(|_| admission.try_admit(ip("127.0.0.2")).unwrap()).collect();
        assert!(admission.try_admit(ip("127.0.0.2")).is_none(), "one source exceeded its connection cap");
        // The IPv4-mapped spelling of the same address is the same source.
        assert!(admission.try_admit(ip("::ffff:127.0.0.2")).is_none());
        // Other sources still get in, up to the global bound of 16.
        let mut others = Vec::new();
        for i in 0..(MAX_CONNECTIONS - MAX_CONNECTIONS_PER_SOURCE) {
            others.push(admission.try_admit(ip(&format!("127.0.1.{}", i / 2))).expect("another source was locked out"));
        }
        assert_eq!(MAX_CONNECTIONS, 16);
        assert!(admission.try_admit(ip("127.0.9.9")).is_none(), "the global bound was exceeded");
        // A released slot is admitted again.
        a.pop();
        let again = admission.try_admit(ip("127.0.0.2"));
        assert!(again.is_some());
        assert!(admission.try_admit(ip("127.0.9.9")).is_none());
        drop((again, a, others));
        assert_eq!(admission.held.lock().unwrap().0, 0);
        assert!(admission.held.lock().unwrap().1.is_empty());
    }
    #[tokio::test]
    async fn streamed_body_limit_is_enforced() {
        let cap = if cfg!(feature = "mutate-unbounded-body") { usize::MAX } else { MAX_BODY };
        let body = Full::new(Bytes::from(vec![0; MAX_BODY + 1]));
        assert!(Limited::new(body, cap).collect().await.is_err());
    }

    #[test]
    fn decodes_query_keys_before_denying_destructive_subresources() {
        assert!(r(Method::POST, "/b?%64elete"));
        assert!(r(Method::POST, "/b?de%6Cete="));
        assert!(r(Method::PUT, "/b?%70olicy"));
        assert!(r(Method::PUT, "/b/obj/x?life%63ycle"));
        assert!(r(Method::GET, "/b?%GG"));
        assert!(r(Method::GET, "/b?%FF"));
        assert!(r(Method::GET, "/b?%2564elete"));
        assert!(r(Method::POST, "/b?prefix%26delete"));
        assert!(r(Method::POST, "/b?delete%3D"));
        // W2: multipart uploads are refused as well (the gateway must see whole bodies).
        assert!(r(Method::POST, "/b/obj/x?uploads"));
    }

    #[test]
    fn gc_key_only_allows_signed_object_delete_candidate() {
        let mut h = HeaderMap::new();
        h.insert(AUTHORIZATION, "AWS4-HMAC-SHA256 Credential=GC123/20261020/us-east-1/s3/aws4_request, SignedHeaders=host;x-amz-date, Signature=abcd".parse().unwrap());
        h.insert(hyper::header::HOST, "127.0.0.1:18433".parse().unwrap());
        let policy = |key: Option<&str>| GcPolicy {
            key: key.map(str::to_string),
            prefixes: vec!["b/scratch/".into()],
            ..Default::default()
        };
        let check = |h: &HeaderMap, method, uri: &str, key| refusal(&method, &uri.parse().unwrap(), h, &policy(key));
        assert!(check(&h, Method::DELETE, "/b/scratch/id", None).is_some());
        assert!(check(&h, Method::DELETE, "/b/scratch/id", Some("OTHER")).is_some());
        // The allowlist also refuses bucket paths; check that the bucket-level
        // rule itself fires first, so each layer stays independently tested.
        assert_eq!(check(&h, Method::DELETE, "/b", Some("GC123")), Some("bucket and configuration deletes are denied"));
        assert_eq!(check(&h, Method::DELETE, "/b/", Some("GC123")), Some("bucket and configuration deletes are denied"));
        assert!(check(&h, Method::DELETE, "/b?policy", Some("GC123")).is_some());
        assert!(check(&h, Method::DELETE, "/b/scratch/id?versionId=x", Some("GC123")).is_some());
        assert!(check(&h, Method::POST, "/b?delete", Some("GC123")).is_some());
        assert!(check(&h, Method::DELETE, "/b/scratch/id", Some("GC123")).is_none());
        h.insert(AUTHORIZATION, "AWS4-HMAC-SHA256 Credential=GC123/scope, Credential=APP/scope, SignedHeaders=host, Signature=abcd".parse().unwrap());
        assert!(check(&h, Method::DELETE, "/b/scratch/id", Some("GC123")).is_some());
        h.remove(AUTHORIZATION);
        assert!(check(&h, Method::DELETE, "/b/scratch/id", Some("GC123")).is_some());
    }

    #[test]
    fn gc_never_deletes_p2_content_or_unlisted_keys() {
        let mut h = HeaderMap::new();
        h.insert(AUTHORIZATION, "AWS4-HMAC-SHA256 Credential=GC123/20261020/us-east-1/s3/aws4_request, SignedHeaders=host;x-amz-date, Signature=abcd".parse().unwrap());
        h.insert(hyper::header::HOST, "127.0.0.1:18433".parse().unwrap());
        let policy = GcPolicy { key: Some("GC123".into()), prefixes: vec!["b/scratch/".into()], ..Default::default() };
        let denied = |h: &HeaderMap, uri: &str| refusal(&Method::DELETE, &uri.parse().unwrap(), h, &policy).is_some();
        for kind in ["group", "chunk", "capsule", "snapshot", "manifest", "blob", "marker", "tombstone"] {
            assert!(denied(&h, &format!("/b/obj/{kind}/ab")), "{kind}");
            assert!(denied(&h, &format!("/b/dep-1/obj/{kind}/ab")), "{kind}");
            assert!(denied(&h, &format!("/b/scratch/obj/{kind}/ab")), "{kind}");
            assert!(denied(&h, &format!("/b/scratch/%6Fbj/{kind}/ab")), "{kind}");
        }
        assert!(denied(&h, "/b/other/id"));
        assert!(denied(&h, "/c/scratch/id"));
        assert!(denied(&h, "/b/scratch/"));
        assert!(denied(&h, "/b/scratch/../obj/tombstone/ab"));
        assert!(denied(&h, "/b/scratch/%2E%2E/x"));
        assert!(denied(&h, "/b/scratch//x"));
        assert!(denied(&h, "/b/scratch/%GG"));
        assert!(denied(&h, "/b/scratch/%2541"));
        assert!(!denied(&h, "/b/scratch/id"));
        let mut virtual_host = h.clone();
        virtual_host.insert(hyper::header::HOST, "b.s3.localhost:18433".parse().unwrap());
        assert!(denied(&virtual_host, "/b/scratch/id"));
        let mut no_host = h.clone();
        no_host.remove(hyper::header::HOST);
        assert!(denied(&no_host, "/b/scratch/id"));
        assert!(valid_gc_prefix("b/scratch/"));
        for bad in ["", "b", "b/", "/b/x", "b/obj/", "b/x/obj/y", "b/%6Fbj/", "b/../x"] {
            assert!(!valid_gc_prefix(bad), "{bad}");
        }
    }

    fn store_deployments() -> Vec<GcDeployment> {
        vec![GcDeployment { prefix: "paralean/dep-a/".into(), root: foundationdb::tuple::Subspace::from(("paralean", "dep-a")) }]
    }
    const HEX: &str = "9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08";

    fn gc_headers(key: &str) -> HeaderMap {
        let mut h = HeaderMap::new();
        h.insert(AUTHORIZATION, format!("AWS4-HMAC-SHA256 Credential={key}/20261028/garage/s3/aws4_request, SignedHeaders=host;x-amz-date, Signature=abcd").parse().unwrap());
        h.insert(hyper::header::HOST, "127.0.0.1:32150".parse().unwrap());
        h
    }

    #[test]
    fn gc_content_targets_are_exact_configured_keys() {
        let d = store_deployments();
        let (dep, kind, id) = content_target(&format!("/paralean/dep-a/obj/snapshot/{HEX}"), &d).unwrap();
        assert_eq!((dep.prefix.as_str(), kind), ("paralean/dep-a/", "snapshot"));
        assert_eq!(id[0], 0x9f);
        for bad in [
            format!("/paralean/dep-b/obj/group/{HEX}"),           // unconfigured deployment
            format!("/paralean/dep-a/x/obj/group/{HEX}"),         // nested prefix
            format!("/paralean/dep-a/obj/other/{HEX}"),           // unknown kind
            format!("/paralean/dep-a/obj/group/{}", &HEX[..63]),   // short ID
            format!("/paralean/dep-a/obj/group/{}", HEX.to_uppercase()),
            format!("/paralean/dep-a/obj/group/{HEX}/x"),
            format!("/paralean/dep-a/obj/group/%2E%2E/{HEX}"),
            format!("/paralean/dep-a/../dep-a/obj/group/{HEX}"),
            format!("/paralean/dep-a/obj/group/{HEX}%00"),
            format!("/other/dep-a/obj/group/{HEX}"),
        ] {
            assert!(content_target(&bad, &d).is_none(), "{bad}");
        }
        // Percent-encoded spellings decode strictly to the same key or fail closed.
        assert!(content_target(&format!("/paralean/dep-a/%6Fbj/group/{HEX}"), &d).is_some());
        assert_eq!(gcobj_key(&d[0], "group", &[0xab; 32]),
            foundationdb::tuple::Subspace::from(("paralean", "dep-a")).pack(&("gcobj", "group", foundationdb::tuple::Bytes::from(&[0xab; 32][..]))));
        assert!(valid_gc_deployment_prefix("paralean/dep-a/"));
        assert!(valid_gc_deployment_prefix("paralean/"));
        for bad in ["paralean", "/paralean/x/", "paralean/obj/", "paralean/dep", "paralean/%41/", "paralean/../x/", "/"] {
            assert!(!valid_gc_deployment_prefix(bad), "{bad}");
        }
    }

    /// Only a doomed (or interrupted deleting) object may be deleted; every other state,
    /// including an unmarked key, is refused. Mutation: `mutate-storegc-guard-no-mark-check`.
    #[test]
    fn gc_content_delete_needs_doomed_mark() {
        assert!(gc_delete_admits(Some(GcState::Doomed { size: 5 })));
        assert!(gc_delete_admits(Some(GcState::Deleting { nonce: [1; 16], size: 5 })));
        assert!(!gc_delete_admits(None), "unmarked key");
        assert!(!gc_delete_admits(Some(GcState::Sighted)), "sighted key");
        assert!(!gc_delete_admits(Some(GcState::Gone)), "gone key");
        assert!(gc_put_admits(None) && gc_put_admits(Some(GcState::Sighted)) && gc_put_admits(Some(GcState::Gone)));
        assert!(!gc_put_admits(Some(GcState::Doomed { size: 1 })) && !gc_put_admits(Some(GcState::Deleting { nonce: [0; 16], size: 1 })));
    }

    /// Content deletes need the configured GC principal, no query and path-style addressing.
    /// Mutation: `mutate-storegc-guard-any-principal`.
    #[test]
    fn gc_content_delete_needs_gc_principal() {
        let policy = GcPolicy { key: Some("GKGC".into()), prefixes: vec![], store: None };
        let uri: Uri = format!("/paralean/dep-a/obj/group/{HEX}").parse().unwrap();
        assert_eq!(content_delete_refusal(&uri, &gc_headers("GKGC"), &policy), None);
        assert!(content_delete_refusal(&uri, &gc_headers("GKAPP"), &policy).is_some(), "application principal");
        assert!(content_delete_refusal(&uri, &gc_headers("GKGC2"), &policy).is_some(), "other access key");
        assert!(content_delete_refusal(&uri, &HeaderMap::new(), &policy).is_some(), "unsigned");
        let mut forged = gc_headers("GKGC");
        forged.insert(AUTHORIZATION, "AWS4-HMAC-SHA256 Credential=GKGC/x, Credential=GKAPP/x, SignedHeaders=host, Signature=ab".parse().unwrap());
        assert!(content_delete_refusal(&uri, &forged, &policy).is_some(), "ambiguous credential");
        let no_key = GcPolicy::default();
        assert!(content_delete_refusal(&uri, &gc_headers("GKGC"), &no_key).is_some(), "no configured GC key");
        let sdk: Uri = format!("/paralean/dep-a/obj/group/{HEX}?x-id=DeleteObject").parse().unwrap();
        assert_eq!(content_delete_refusal(&sdk, &gc_headers("GKGC"), &policy), None, "the SDK's operation marker");
        for q in ["versionId=1", "x-id=DeleteObject&versionId=1", "x-id=DeleteObjects", "x-%69d=DeleteObject", "delete", "x-id=DeleteObject&"] {
            let q: Uri = format!("/paralean/dep-a/obj/group/{HEX}?{q}").parse().unwrap();
            assert!(content_delete_refusal(&q, &gc_headers("GKGC"), &policy).is_some(), "query {q}");
        }
        let mut vhost = gc_headers("GKGC");
        vhost.insert(hyper::header::HOST, "paralean.s3.example:32150".parse().unwrap());
        assert!(content_delete_refusal(&uri, &vhost, &policy).is_some(), "virtual-hosted");
    }

    /// The byte layout shared with paralean-store `gc::GcState::encode`.
    #[test]
    fn gc_state_layout_matches_the_store() {
        let mut doomed = vec![2];
        doomed.extend_from_slice(&7u64.to_be_bytes());
        doomed.extend_from_slice(&1234u64.to_be_bytes());
        assert_eq!(GcState::decode(&doomed), Some(GcState::Doomed { size: 1234 }));
        assert_eq!(GcState::decode(&deleting([5; 16], 99)), Some(GcState::Deleting { nonce: [5; 16], size: 99 }));
        assert_eq!(GcState::decode(&gone(3, [5; 16])), Some(GcState::Gone));
        let mut sighted = vec![1];
        sighted.extend_from_slice(&3u64.to_be_bytes());
        assert_eq!(GcState::decode(&sighted), Some(GcState::Sighted));
        assert_eq!(GcState::decode(&[2, 0]), None);
    }
}
