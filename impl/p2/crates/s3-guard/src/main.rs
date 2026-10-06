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

use std::convert::Infallible;
use std::net::SocketAddr;

use bytes::Bytes;
use http_body_util::{combinators::BoxBody, BodyExt, Full};
use hyper::body::Incoming;
use hyper::server::conn::http1;
use hyper::service::service_fn;
use hyper::{Method, Request, Response, StatusCode, Uri};
use hyper_util::client::legacy::{connect::HttpConnector, Client};
use hyper_util::rt::{TokioExecutor, TokioIo};
use tokio::net::TcpListener;

type Body = BoxBody<Bytes, hyper::Error>;

const DENIED_SUBRESOURCES: &[&str] = &[
    "lifecycle", "policy", "website", "cors", "versioning", "object-lock", "retention",
    "legal-hold", "replication", "encryption",
];

/// Why a request is refused, or `None` if it may pass.
fn refusal(method: &Method, uri: &Uri) -> Option<&'static str> {
    let query = uri.query().unwrap_or("");
    let keys: Vec<&str> = query
        .split('&')
        .filter(|s| !s.is_empty())
        .map(|kv| kv.split('=').next().unwrap_or(""))
        .collect();
    let path = uri.path().trim_start_matches('/');
    let is_bucket_level = !path.contains('/') || path.ends_with('/') && path.matches('/').count() == 1;
    if method == Method::DELETE {
        return Some("deletes are denied on this store (GC is disabled)");
    }
    if method == Method::POST && keys.contains(&"delete") {
        return Some("DeleteObjects is denied on this store (GC is disabled)");
    }
    if method == Method::PUT {
        if keys.iter().any(|k| DENIED_SUBRESOURCES.contains(k)) {
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
        .body(Full::new(Bytes::from(xml)).map_err(|n: Infallible| match n {}).boxed())
        .unwrap()
}

async fn handle(
    client: Client<HttpConnector, Incoming>,
    upstream: String,
    mut req: Request<Incoming>,
) -> Result<Response<Body>, Infallible> {
    if let Some(msg) = refusal(req.method(), req.uri()) {
        eprintln!("s3-guard: refused {} {}", req.method(), req.uri());
        return Ok(denied(msg));
    }
    let pq = req.uri().path_and_query().map(|p| p.as_str().to_string()).unwrap_or_else(|| "/".into());
    let uri: Uri = format!("http://{upstream}{pq}").parse().unwrap();
    *req.uri_mut() = uri;
    match client.request(req).await {
        Ok(resp) => Ok(resp.map(|b| b.boxed())),
        Err(e) => {
            eprintln!("s3-guard: upstream error: {e}");
            Ok(Response::builder()
                .status(StatusCode::BAD_GATEWAY)
                .body(Full::new(Bytes::from_static(b"upstream error")).map_err(|n: Infallible| match n {}).boxed())
                .unwrap())
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
    let mut listen: SocketAddr = "127.0.0.1:18433".parse()?;
    let mut upstream = "127.0.0.1:18439".to_string();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--listen" => listen = args.next().ok_or("--listen needs a value")?.parse()?,
            "--upstream" => upstream = args.next().ok_or("--upstream needs a value")?,
            other => return Err(format!("unknown argument {other}").into()),
        }
    }
    let listener = TcpListener::bind(listen).await?;
    eprintln!("s3-guard: listening on {listen}, upstream {upstream}");
    let client: Client<HttpConnector, Incoming> = Client::builder(TokioExecutor::new()).build_http();
    loop {
        let (stream, _) = listener.accept().await?;
        let client = client.clone();
        let upstream = upstream.clone();
        tokio::spawn(async move {
            let svc = service_fn(move |req| handle(client.clone(), upstream.clone(), req));
            if let Err(e) = http1::Builder::new().serve_connection(TokioIo::new(stream), svc).await {
                eprintln!("s3-guard: connection error: {e}");
            }
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
}
