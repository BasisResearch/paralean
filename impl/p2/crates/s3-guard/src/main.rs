//! s3-guard: an S3 passthrough that refuses destructive requests by default.
//!
//! store.md requires that "the bucket denies `DeleteObject` (or uses Object Lock)". Garage
//! has neither bucket policies nor Object Lock, and a Garage key with write permission may
//! delete. The P2 cluster therefore exposes Garage only through this gateway. Requests are
//! forwarded unchanged (method, path, query, headers including `Host`, body), so SigV4
//! signatures computed against the gateway's address verify at Garage, and clients use the
//! plain S3 API: replacing Garage by another S3 store changes only the upstream address.
//!
//! Refused (403 `AccessDenied`): any `DELETE` by default; bucket and configuration
//! deletes even with `--gc-access-key`. That option admits only object `DELETE`
//! requests bearing that SigV4 access key. It is an identity selector: Garage must
//! verify the signature and authorize the key. Keep Garage inaccessible to clients.
//! `AbortMultipartUpload`, DeleteBucketPolicy/Lifecycle/Cors/Website/Tagging, ...;
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

use bytes::Bytes;
use http_body_util::{combinators::BoxBody, BodyExt, Full};
use hyper::body::Incoming;
use hyper::header::{HeaderMap, AUTHORIZATION};
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::{Method, Request, Response, StatusCode, Uri};
use hyper_util::client::legacy::{connect::HttpConnector, Client};
use hyper_util::rt::{TokioExecutor, TokioIo};
use tokio::net::TcpListener;

type Body = BoxBody<Bytes, hyper::Error>;

const DENIED_SUBRESOURCES: &[&str] = &[
    "lifecycle",
    "policy",
    "website",
    "cors",
    "versioning",
    "object-lock",
    "retention",
    "legal-hold",
    "replication",
    "encryption",
];

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

/// Why a request is refused, or `None` if it may pass.
fn refusal(
    method: &Method,
    uri: &Uri,
    headers: &HeaderMap,
    gc_key: Option<&str>,
) -> Option<&'static str> {
    let query = uri.query().unwrap_or("");
    let keys: Option<Vec<String>> = query
        .split('&')
        .filter(|s| !s.is_empty())
        .map(|kv| query_key(kv.split('=').next().unwrap_or("")))
        .collect();
    let Some(keys) = keys else {
        return Some("malformed query key is denied");
    };
    let path = uri.path().trim_start_matches('/');
    let is_bucket_level =
        !path.contains('/') || path.ends_with('/') && path.matches('/').count() == 1;
    if method == Method::DELETE {
        // A GC principal may delete only an object. Bucket and bucket-configuration
        // deletion remains impossible through this gateway, even for GC.
        if (!cfg!(feature = "mutate-no-bucket-delete-check") && is_bucket_level) || !keys.is_empty()
        {
            return Some("bucket and configuration deletes are denied");
        }
        if !cfg!(feature = "mutate-no-gc-principal-check") && !gc_principal(headers, gc_key) {
            return Some("object deletes require the configured GC principal");
        }
        return None;
    }
    if method == Method::POST && keys.iter().any(|k| k == "delete") {
        return Some("DeleteObjects is denied on this store (GC is disabled)");
    }
    if method == Method::PUT {
        if keys
            .iter()
            .any(|k| DENIED_SUBRESOURCES.contains(&k.as_str()))
        {
            return Some("bucket and object configuration changes are denied");
        }
        if is_bucket_level && keys.is_empty() {
            return Some("bucket creation is denied through the gateway");
        }
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
        .body(
            Full::new(Bytes::from(xml))
                .map_err(|n: Infallible| match n {})
                .boxed(),
        )
        .unwrap()
}

async fn handle(
    client: Client<HttpConnector, Full<Bytes>>,
    upstreams: Arc<Vec<String>>,
    gc_key: Option<Arc<String>>,
    req: Request<Incoming>,
) -> Result<Response<Body>, Infallible> {
    if let Some(msg) = refusal(
        req.method(),
        req.uri(),
        req.headers(),
        gc_key.as_deref().map(String::as_str),
    ) {
        eprintln!("s3-guard: refused {} {}", req.method(), req.uri());
        return Ok(denied(msg));
    }
    let pq = req
        .uri()
        .path_and_query()
        .map(|p| p.as_str().to_string())
        .unwrap_or_else(|| "/".into());
    let (parts, body) = req.into_parts();
    let body = match body.collect().await {
        Ok(b) => b.to_bytes(),
        Err(e) => {
            return Ok(error(
                StatusCode::BAD_REQUEST,
                &format!("request body: {e}"),
            ))
        }
    };
    let mut last = String::new();
    for up in upstreams.iter() {
        let mut r = Request::from_parts(parts.clone(), Full::new(body.clone()));
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
        .body(
            Full::new(Bytes::from(msg.to_string()))
                .map_err(|n: Infallible| match n {})
                .boxed(),
        )
        .unwrap()
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut listen: SocketAddr = "127.0.0.1:18433".parse()?;
    let mut upstream = "127.0.0.1:18439".to_string();
    let mut gc_key: Option<Arc<String>> = None;
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--listen" => listen = args.next().ok_or("--listen needs a value")?.parse()?,
            "--upstream" => upstream = args.next().ok_or("--upstream needs a value")?,
            "--gc-access-key" => {
                gc_key = Some(Arc::new(
                    args.next().ok_or("--gc-access-key needs a value")?,
                ))
            }
            other => return Err(format!("unknown argument {other}").into()),
        }
    }
    let listener = TcpListener::bind(listen).await?;
    eprintln!("s3-guard: listening on {listen}, upstream {upstream}");
    let client: Client<HttpConnector, Full<Bytes>> =
        Client::builder(TokioExecutor::new()).build_http();
    let upstreams: Arc<Vec<String>> = Arc::new(upstream.split(',').map(str::to_string).collect());
    loop {
        let (stream, _) = listener.accept().await?;
        let client = client.clone();
        let upstreams = upstreams.clone();
        let gc_key = gc_key.clone();
        tokio::spawn(async move {
            let svc = service_fn(move |req| {
                handle(client.clone(), upstreams.clone(), gc_key.clone(), req)
            });
            if let Err(e) = http1::Builder::new()
                .serve_connection(TokioIo::new(stream), svc)
                .await
            {
                eprintln!("s3-guard: connection error: {e}");
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn r(m: Method, u: &str) -> bool {
        refusal(&m, &u.parse().unwrap(), &HeaderMap::new(), None).is_some()
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
        assert!(!r(Method::PUT, "/b/obj/group/abcd"));
        assert!(!r(Method::GET, "/b?list-type=2&prefix=obj/"));
        assert!(!r(Method::HEAD, "/b/obj/x"));
        assert!(!r(Method::POST, "/b/obj/x?uploads"));
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
        assert!(!r(Method::POST, "/b/obj/x?uploads"));
    }

    #[test]
    fn gc_key_only_allows_signed_object_delete_candidate() {
        let mut h = HeaderMap::new();
        h.insert(AUTHORIZATION, "AWS4-HMAC-SHA256 Credential=GC123/20261020/us-east-1/s3/aws4_request, SignedHeaders=host;x-amz-date, Signature=abcd".parse().unwrap());
        let check = |method, uri: &str, key| refusal(&method, &uri.parse().unwrap(), &h, key);
        assert!(check(Method::DELETE, "/b/obj/chunk/id", None).is_some());
        assert!(check(Method::DELETE, "/b/obj/chunk/id", Some("OTHER")).is_some());
        assert!(check(Method::DELETE, "/b", Some("GC123")).is_some());
        assert!(check(Method::DELETE, "/b?policy", Some("GC123")).is_some());
        assert!(check(Method::DELETE, "/b/obj/chunk/id?versionId=x", Some("GC123")).is_some());
        assert!(check(Method::POST, "/b?delete", Some("GC123")).is_some());
        assert!(check(Method::DELETE, "/b/obj/chunk/id", Some("GC123")).is_none());
        h.insert(AUTHORIZATION, "AWS4-HMAC-SHA256 Credential=GC123/scope, Credential=APP/scope, SignedHeaders=host, Signature=abcd".parse().unwrap());
        assert!(refusal(
            &Method::DELETE,
            &"/b/obj/chunk/id".parse().unwrap(),
            &h,
            Some("GC123")
        )
        .is_some());
        h.remove(AUTHORIZATION);
        assert!(refusal(
            &Method::DELETE,
            &"/b/obj/chunk/id".parse().unwrap(),
            &h,
            Some("GC123")
        )
        .is_some());
    }
}
