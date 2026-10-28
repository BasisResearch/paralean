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
//! `--upstream` takes a comma-separated list (the S3 ports of a multi-node Garage cluster).
//! A request goes to the first upstream that accepts the connection, so the gateway rides
//! through the loss of a node; the request body is buffered for that.

use std::convert::Infallible;
use std::net::SocketAddr;
use std::sync::Arc;
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
use tokio::sync::Semaphore;

type Body = BoxBody<Bytes, hyper::Error>;

const MAX_BODY: usize = 65 * 1024 * 1024; // 64 MiB chunk plus domain/encoding
const MAX_CONNECTIONS: usize = 16;

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

/// The P2 content-kind segment. A key containing it is never a GC candidate.
const PROTECTED_SEGMENT: &str = "obj/";

/// The GC principal's delete boundary: allowlisted `bucket/key` prefixes.
#[derive(Clone, Debug, Default)]
struct GcPolicy {
    key: Option<String>,
    prefixes: Vec<String>,
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
    if let Some(msg) = refusal(req.method(), req.uri(), req.headers(), &gc) {
        // Query strings may contain presigned credentials; never log them.
        eprintln!("s3-guard: refused {}", req.method());
        return Ok(denied(msg));
    }
    let pq = req.uri().path_and_query().map(|p| p.as_str().to_string()).unwrap_or_else(|| "/".into());
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
                Err(_) => return Ok(error(StatusCode::BAD_GATEWAY, "upstream handshake failed")),
            };
            tokio::spawn(async move { let _ = connection.await; });
            return Ok(match sender.send_request(r).await {
                Ok(resp) => resp.map(|b| b.boxed()),
                Err(_) => error(StatusCode::BAD_GATEWAY, "upstream error"),
            });
        }
        *r.uri_mut() = format!("http://{up}{pq}").parse().unwrap();
        match client.request(r).await {
            Ok(resp) => return Ok(resp.map(|b| b.boxed())),
            // Only a refused or failed connection moves on: a request that reached a node
            // may have had an effect, and its reply is that node's answer.
            Err(e) if e.is_connect() => last = format!("{up}: {e}"),
            Err(e) => {
                eprintln!("s3-guard: upstream {up} error: {e}");
                return Ok(error(StatusCode::BAD_GATEWAY, "upstream error"));
            }
        }
    }
    eprintln!("s3-guard: no upstream reachable ({last})");
    Ok(error(StatusCode::BAD_GATEWAY, "no upstream reachable"))
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
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--listen" => listen = args.next().ok_or("--listen needs a value")?.parse()?,
            "--upstream" => upstream = args.next().ok_or("--upstream needs a value")?,
            "--gc-access-key" => gc.key = Some(args.next().ok_or("--gc-access-key needs a value")?),
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
    if gc.key.is_some() != !gc.prefixes.is_empty() {
        return Err("--gc-access-key and --gc-delete-prefix must be given together".into());
    }
    let gc = Arc::new(gc);
    let listener = TcpListener::bind(listen).await?;
    eprintln!("s3-guard: listening on {listen}, upstream {upstream}");
    let client: Client<HttpConnector, Full<Bytes>> = Client::builder(TokioExecutor::new()).build_http();
    let upstreams: Arc<Vec<String>> = Arc::new(upstream.split(',').map(str::to_string).collect());
    let slots = Arc::new(Semaphore::new(MAX_CONNECTIONS));
    loop {
        let (stream, _) = listener.accept().await?;
        let Ok(permit) = slots.clone().try_acquire_owned() else { continue };
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
        let policy = GcPolicy { key: Some("GC123".into()), prefixes: vec!["b/scratch/".into()] };
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
}
