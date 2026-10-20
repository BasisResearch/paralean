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
//! bytes). Refused (403 `AccessDenied`): every DELETE and POST (DeleteObjects, multipart
//! uploads); PUT with any sub-resource query, server-side copy or aws-chunked framing;
//! PUT of any other key, including bucket creation; and PUT of a body that does not hash
//! to its key, which would destroy the stored object as surely as a delete.
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
use hyper::{HeaderMap, Method, Request, Response, StatusCode, Uri};
use sha2::{Digest, Sha256};
use hyper_util::client::legacy::{connect::HttpConnector, Client};
use hyper_util::rt::{TokioExecutor, TokioIo};
use tokio::net::{TcpListener, UnixStream};
use tokio::sync::Semaphore;

type Body = BoxBody<Bytes, hyper::Error>;

const MAX_BODY: usize = 65 * 1024 * 1024; // 64 MiB chunk plus domain/encoding
const MAX_CONNECTIONS: usize = 16;

fn query_key(s: &str) -> Option<String> {
    let mut bytes = s.bytes();
    let mut decoded = Vec::new();
    while let Some(b) = bytes.next() {
        decoded.push(match b {
            b'%' => {
                let h = (bytes.next()? as char).to_digit(16)?;
                let l = (bytes.next()? as char).to_digit(16)?;
                (h * 16 + l) as u8
            }
            b'+' => b' ',
            other => other,
        });
    }
    String::from_utf8(decoded).ok()
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
fn refusal(method: &Method, uri: &Uri, headers: &HeaderMap) -> Option<&'static str> {
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
        return Some("deletes are denied on this store (GC is disabled)");
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
    req: Request<Incoming>,
) -> Result<Response<Body>, Infallible> {
    if let Some(msg) = refusal(req.method(), req.uri(), req.headers()) {
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
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--listen" => listen = args.next().ok_or("--listen needs a value")?.parse()?,
            "--upstream" => upstream = args.next().ok_or("--upstream needs a value")?,
            other => return Err(format!("unknown argument {other}").into()),
        }
    }
    if upstream.is_empty() { return Err("--upstream unix:/private/path/s3.sock is required".into()); }
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
        tokio::spawn(async move {
            let _permit = permit;
            let svc = service_fn(move |req| handle(client.clone(), upstreams.clone(), req));
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
    fn r(m: Method, u: &str) -> bool { refusal(&m, &u.parse().unwrap(), &HeaderMap::new()).is_some() }
    fn with(m: Method, u: &str, name: &'static str, value: &str) -> bool {
        let mut h = HeaderMap::new();
        h.insert(name, value.parse().unwrap());
        refusal(&m, &u.parse().unwrap(), &h).is_some()
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
}
