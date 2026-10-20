//! A minimal TCP service: each connection carries one framed request and its framed
//! response (`paralean_validator_api::rpc`).

use std::future::Future;
use std::sync::Arc;
use std::time::Duration;

use paralean_validator_api::rpc::{self, read_frame, write_frame};
use paralean_store::Signer;
use serde::de::DeserializeOwned;
use serde::Serialize;
use tokio::net::TcpListener;
use tokio::task::JoinHandle;
use tokio::sync::Semaphore;

/// Bounds apply before authentication: an idle stranger must not reserve a task
/// or a frame buffer indefinitely. Handler deadlines are separate from handshake
/// deadlines because legitimate Lean checks can take minutes.
#[derive(Clone, Copy)]
struct Limits {
    connections: usize,
    handshake: Duration,
    execution: Duration,
}

impl Default for Limits {
    fn default() -> Self {
        Self { connections: 32, handshake: Duration::from_secs(5), execution: Duration::from_secs(900) }
    }
}

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
    serve_authenticated_limited(listener, signer, authorize, handle, Limits::default())
}

fn serve_authenticated_limited<Q, A, F, Fut, Auth>(
    listener: TcpListener, signer: Signer, authorize: Auth, handle: F, limits: Limits,
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
    let slots = Arc::new(Semaphore::new(if cfg!(feature = "mutate-unbounded-rpc") { 65536 } else { limits.connections }));
    tokio::spawn(async move {
        loop {
            let Ok((mut sock, _)) = listener.accept().await else { continue };
            // Do not queue a task waiting for a permit: that queue itself is a DoS.
            let Ok(permit) = slots.clone().try_acquire_owned() else { continue };
            let handle = handle.clone();
            let authorize = authorize.clone();
            let signer = signer.clone();
            tokio::spawn(async move {
                let _permit = permit;
                let _ = sock.set_nodelay(true);
                let c = rpc::challenge(&signer);
                let handshake = async {
                    write_frame(&mut sock, &c).await?;
                    read_frame::<rpc::SignedRequest<Q>>(&mut sock).await
                };
                let deadline = if cfg!(feature = "mutate-no-rpc-deadline") { Duration::from_secs(86400) } else { limits.handshake };
                let Ok(Ok(req)) = tokio::time::timeout(deadline, handshake).await else { return };
                if !rpc::verify_request(&req, &c.nonce) || !authorize(&req.payload, &req.public) {
                    return;
                }
                let Ok(resp) = tokio::time::timeout(limits.execution, handle(req.payload)).await else { return };
                let Ok(resp) = rpc::signed_response(resp, &signer, &c.nonce) else { return };
                let _ = tokio::time::timeout(limits.handshake, write_frame(&mut sock, &resp)).await;
            });
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::net::TcpStream;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    async fn server(connections: usize) -> (String, Signer, JoinHandle<()>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let signer = Signer::generate();
        let key = signer.public();
        let task = serve_authenticated_limited(listener, signer.clone(), move |_: &u32, p| p == &key,
            |n: u32| async move { n + 1 },
            Limits { connections, handshake: Duration::from_millis(150), execution: Duration::from_secs(1) });
        (addr, signer, task)
    }

    #[tokio::test]
    async fn connection_admission_is_bounded_before_authentication() {
        let (addr, _, task) = server(1).await;
        let mut held = TcpStream::connect(&addr).await.unwrap();
        let _: rpc::Challenge = read_frame(&mut held).await.unwrap();
        let mut extra = TcpStream::connect(&addr).await.unwrap();
        let result = tokio::time::timeout(Duration::from_millis(100), read_frame::<rpc::Challenge>(&mut extra)).await;
        task.abort();
        assert!(matches!(result, Ok(Err(_))), "excess unauthenticated connection got a challenge: {result:?}");
    }

    #[tokio::test]
    async fn incomplete_frames_expire_and_release_admission() {
        let (addr, signer, task) = server(1).await;
        let mut held = TcpStream::connect(&addr).await.unwrap();
        let _: rpc::Challenge = read_frame(&mut held).await.unwrap();
        // Advertise a permitted frame then send no body (slowloris).
        held.write_all(&4096u32.to_be_bytes()).await.unwrap();
        let result = tokio::time::timeout(Duration::from_millis(500), held.read_u8()).await;
        assert!(matches!(result, Ok(Err(_))), "incomplete frame survived its deadline");
        let answer: u32 = rpc::call_authenticated(&addr, &41u32, &signer, &signer.public(), Duration::from_secs(1)).await.unwrap();
        task.abort();
        assert_eq!(answer, 42);
    }
}
