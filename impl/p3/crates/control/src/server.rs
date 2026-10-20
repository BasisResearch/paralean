//! A minimal TCP service: each connection carries one framed request and its framed
//! response (`paralean_validator_api::rpc`).

use std::future::Future;
use std::sync::Arc;

use paralean_validator_api::rpc::{self, read_frame, write_frame};
use paralean_store::Signer;
use serde::de::DeserializeOwned;
use serde::Serialize;
use tokio::net::TcpListener;
use tokio::task::JoinHandle;

/// Serve `handle` on `listener` until the returned task is aborted.
pub fn serve<Q, A, F, Fut>(listener: TcpListener, handle: F) -> JoinHandle<()>
where
    Q: DeserializeOwned + Send + 'static,
    A: Serialize + Send + Sync + 'static,
    F: Fn(Q) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = A> + Send + 'static,
{
    let handle = Arc::new(handle);
    tokio::spawn(async move {
        loop {
            let Ok((mut sock, _)) = listener.accept().await else { continue };
            let handle = handle.clone();
            tokio::spawn(async move {
                let _ = sock.set_nodelay(true);
                let Ok(req) = read_frame::<Q>(&mut sock).await else { return };
                let resp = handle(req).await;
                let _ = write_frame(&mut sock, &resp).await;
            });
        }
    })
}

/// Serve authenticated one-shot exchanges. `authorize` binds the verified public key
/// to the operation and any identity claimed in the request.
pub fn serve_authenticated<Q, A, F, Fut, Auth>(
    listener: TcpListener, signer: Signer, authorize: Auth, handle: F,
) -> JoinHandle<()>
where
    Q: DeserializeOwned + Serialize + Send + 'static,
    A: Serialize + Send + Sync + 'static,
    F: Fn(Q) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = A> + Send + 'static,
    Auth: Fn(&Q, &[u8; 32]) -> bool + Send + Sync + 'static,
{
    let handle = Arc::new(handle);
    let authorize = Arc::new(authorize);
    tokio::spawn(async move {
        loop {
            let Ok((mut sock, _)) = listener.accept().await else { continue };
            let handle = handle.clone();
            let authorize = authorize.clone();
            let signer = signer.clone();
            tokio::spawn(async move {
                let _ = sock.set_nodelay(true);
                let c = rpc::challenge(&signer);
                if write_frame(&mut sock, &c).await.is_err() { return; }
                let Ok(req) = read_frame::<rpc::SignedRequest<Q>>(&mut sock).await else { return };
                if !rpc::verify_request(&req, &c.nonce) || !authorize(&req.payload, &req.public) {
                    return;
                }
                let resp = handle(req.payload).await;
                let Ok(resp) = rpc::signed_response(resp, &signer, &c.nonce) else { return };
                let _ = write_frame(&mut sock, &resp).await;
            });
        }
    })
}
