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
//! Refused (403 `AccessDenied`): any `DELETE` (DeleteObject, DeleteBucket,
//! AbortMultipartUpload, DeleteBucketPolicy/Lifecycle/Cors/Website/Tagging, ...);
//! `POST ?delete` (DeleteObjects); `PUT` with a `lifecycle`, `policy`, `website`, `cors`,
//! `versioning`, `object-lock`, `retention` or `legal-hold` sub-resource; `PUT` of a bucket
//! (create; buckets are created by up.sh through Garage's admin CLI).
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
use hyper::{Method, Request, Response, StatusCode, Uri};
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

/// Why a request is refused, or `None` if it may pass.
fn refusal(method: &Method, uri: &Uri) -> Option<&'static str> {
    let query = uri.query().unwrap_or("");
    let keys: Option<Vec<String>> = query
        .split('&')
        .filter(|s| !s.is_empty())
        .map(|kv| query_key(kv.split('=').next().unwrap_or("")))
        .collect();
    let Some(keys) = keys else { return Some("invalid query encoding"); };
    let path = uri.path().trim_start_matches('/');
    let is_bucket_level = !path.contains('/') || path.ends_with('/') && path.matches('/').count() == 1;
    if cfg!(feature = "mutate-allow-delete") { return None; }
    if method == Method::DELETE {
        return Some("deletes are denied on this store (GC is disabled)");
    }
    if method == Method::POST {
        if is_bucket_level || keys.is_empty() || keys.iter().any(|k| k != "uploads" && k != "uploadId" && k != "x-id") {
            return Some("only object multipart POST is allowed");
        }
    }
    if method == Method::PUT {
        if keys.iter().any(|k| k != "uploadId" && k != "partNumber" && k != "x-id") {
            return Some("bucket and object configuration changes are denied");
        }
        if is_bucket_level {
            return Some("bucket creation is denied through the gateway");
        }
    }
    if ![Method::GET, Method::HEAD, Method::PUT, Method::POST].contains(method) {
        return Some("unsupported method");
    }
    None
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
    if let Some(msg) = refusal(req.method(), req.uri()) {
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
    fn r(m: Method, u: &str) -> bool { refusal(&m, &u.parse().unwrap()).is_some() }
    #[test]
    fn refuses_deletes_and_config() {
        assert!(r(Method::DELETE, "/b/obj/x"));
        assert!(r(Method::DELETE, "/b"));
        assert!(r(Method::POST, "/b?delete"));
        assert!(r(Method::POST, "/b?delete="));
        assert!(r(Method::PUT, "/b?lifecycle"));
        assert!(r(Method::PUT, "/b?policy"));
        assert!(r(Method::PUT, "/b"));
        assert!(!r(Method::PUT, "/b/obj/group/abcd"));
        assert!(!r(Method::GET, "/b?list-type=2&prefix=obj/"));
        assert!(!r(Method::HEAD, "/b/obj/x"));
        assert!(!r(Method::POST, "/b/obj/x?uploads"));
    }
    #[test]
    fn encoded_and_unknown_mutations_are_denied() {
        for url in ["/b?%64elete", "/b?%64%65lete=", "/b?x=1&delete", "/b?delete&uploads",
            "/b/obj?%64elete", "/b?%zz", "/b?uploads"] {
            assert!(r(Method::POST, url), "{url}");
        }
        for url in ["/b?%6cifecycle", "/b?acl", "/b?x=1", "/b/obj?tagging", "/b/obj?%70olicy"] {
            assert!(r(Method::PUT, url), "{url}");
        }
        assert!(!r(Method::PUT, "/b/obj?partNumber=1&uploadId=abc%2fdef"));
        assert!(!r(Method::PUT, "/b/obj?x-id=PutObject"));
    }
    #[tokio::test]
    async fn streamed_body_limit_is_enforced() {
        let cap = if cfg!(feature = "mutate-unbounded-body") { usize::MAX } else { MAX_BODY };
        let body = Full::new(Bytes::from(vec![0; MAX_BODY + 1]));
        assert!(Limited::new(body, cap).collect().await.is_err());
    }
}
