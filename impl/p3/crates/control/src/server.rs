//! A minimal TCP service: each connection carries one framed request and its framed
//! response (`paralean_validator_api::rpc`).

use std::future::Future;
use std::sync::Arc;

use paralean_validator_api::rpc::{read_frame, write_frame};
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
