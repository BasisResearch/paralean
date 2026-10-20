//! Framing for the P3 services: one JSON value per frame, each frame a 4-byte big-endian
//! length followed by that many bytes. A connection carries one request and its response
//! (no multiplexing); clients open one connection per call.

use std::time::Duration;

use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;
use paralean_store::{Id, Signer};
use paralean_store::id::sha256;

/// Every RPC signature (challenge, request, response) is checked here.
fn verify(public: &[u8; 32], id: &Id, sig: &[u8]) -> bool {
    paralean_store::sign::verify_path(cfg!(feature = "mutate-relaxed-rpc-sig"), public, id, sig)
}

/// Frames larger than this are refused (requests carry envelopes and receipts only).
pub const MAX_FRAME: usize = 16 << 20;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Challenge {
    pub nonce: [u8; 32],
    pub signature: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SignedRequest<Q> {
    pub public: [u8; 32],
    pub payload: Q,
    pub signature: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SignedResponse<A> {
    pub payload: A,
    pub signature: Vec<u8>,
}

/// Domain separation and the connection nonce bind a signature to one exchange. A
/// captured request cannot be replayed on the next connection's fresh challenge.
pub fn auth_id<T: Serialize>(domain: &[u8], nonce: &[u8; 32], payload: &T) -> std::io::Result<Id> {
    let bytes = serde_json::to_vec(payload).map_err(std::io::Error::other)?;
    let mut preimage = Vec::with_capacity(domain.len() + nonce.len() + bytes.len());
    preimage.extend_from_slice(domain);
    preimage.extend_from_slice(nonce);
    preimage.extend_from_slice(&bytes);
    Ok(Id(sha256(&preimage)))
}

pub fn challenge(signer: &Signer) -> Challenge {
    let nonce = rand::random();
    let signature = signer.sign(&auth_id(b"paralean/rpc/challenge/v1", &nonce, &()).expect("unit encodes")).to_vec();
    Challenge { nonce, signature }
}

pub fn verify_challenge(c: &Challenge, public: &[u8; 32]) -> bool {
    auth_id(b"paralean/rpc/challenge/v1", &c.nonce, &())
        .is_ok_and(|id| verify(public, &id, &c.signature))
}

pub fn signed_request<Q: Serialize>(payload: Q, signer: &Signer, nonce: &[u8; 32]) -> std::io::Result<SignedRequest<Q>> {
    let signature = signer.sign(&auth_id(b"paralean/rpc/request/v1", nonce, &payload)?).to_vec();
    Ok(SignedRequest { public: signer.public(), payload, signature })
}

pub fn verify_request<Q: Serialize>(r: &SignedRequest<Q>, nonce: &[u8; 32]) -> bool {
    auth_id(b"paralean/rpc/request/v1", nonce, &r.payload)
        .is_ok_and(|id| verify(&r.public, &id, &r.signature))
}

pub fn signed_response<A: Serialize>(payload: A, signer: &Signer, nonce: &[u8; 32]) -> std::io::Result<SignedResponse<A>> {
    let signature = signer.sign(&auth_id(b"paralean/rpc/response/v1", nonce, &payload)?).to_vec();
    Ok(SignedResponse { payload, signature })
}

/// Authenticate both peers, the request, and the response on this connection.
pub async fn call_authenticated<Q: Serialize, A: DeserializeOwned + Serialize>(
    addr: &str, req: &Q, signer: &Signer, server_public: &[u8; 32], timeout: Duration,
) -> std::io::Result<A> {
    let fut = async {
        let mut s = tokio::time::timeout(Duration::from_secs(2), TcpStream::connect(addr)).await
            .map_err(|_| std::io::Error::new(std::io::ErrorKind::TimedOut, "RPC connect timed out"))??;
        s.set_nodelay(true)?;
        let c: Challenge = read_frame(&mut s).await?;
        if !verify_challenge(&c, server_public) {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "server authentication failed"));
        }
        write_frame(&mut s, &signed_request(req, signer, &c.nonce)?).await?;
        let resp: SignedResponse<A> = read_frame(&mut s).await?;
        let id = auth_id(b"paralean/rpc/response/v1", &c.nonce, &resp.payload)?;
        if !verify(server_public, &id, &resp.signature) {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "response authentication failed"));
        }
        Ok(resp.payload)
    };
    tokio::time::timeout(timeout, fut).await.unwrap_or_else(|_| Err(std::io::Error::new(std::io::ErrorKind::TimedOut, format!("call to {addr} timed out"))))
}

/// Accept a server signed by any currently configured validator key. The key that
/// signed the challenge must also sign the response.
pub async fn call_authenticated_any<Q: Serialize, A: DeserializeOwned + Serialize>(
    addr: &str, req: &Q, signer: &Signer, server_keys: &[[u8; 32]], timeout: Duration,
) -> std::io::Result<A> {
    let fut = async {
        let mut s = tokio::time::timeout(Duration::from_secs(2), TcpStream::connect(addr)).await
            .map_err(|_| std::io::Error::new(std::io::ErrorKind::TimedOut, "RPC connect timed out"))??;
        s.set_nodelay(true)?;
        let c: Challenge = read_frame(&mut s).await?;
        let Some(public) = server_keys.iter().find(|key| verify_challenge(&c, key)) else {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "validator authentication failed"));
        };
        write_frame(&mut s, &signed_request(req, signer, &c.nonce)?).await?;
        let resp: SignedResponse<A> = read_frame(&mut s).await?;
        let id = auth_id(b"paralean/rpc/response/v1", &c.nonce, &resp.payload)?;
        if !verify(public, &id, &resp.signature) {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "validator response authentication failed"));
        }
        Ok(resp.payload)
    };
    tokio::time::timeout(timeout, fut).await.unwrap_or_else(|_| Err(std::io::Error::new(std::io::ErrorKind::TimedOut, format!("call to {addr} timed out"))))
}

pub async fn write_frame<T: Serialize>(s: &mut TcpStream, v: &T) -> std::io::Result<()> {
    let b = serde_json::to_vec(v).map_err(std::io::Error::other)?;
    if !cfg!(feature = "mutate-oversized-frame") && b.len() > MAX_FRAME {
        return Err(std::io::Error::other("outgoing frame exceeds MAX_FRAME"));
    }
    s.write_all(&(b.len() as u32).to_be_bytes()).await?;
    s.write_all(&b).await?;
    s.flush().await
}

pub async fn read_frame<T: DeserializeOwned>(s: &mut TcpStream) -> std::io::Result<T> {
    let mut len = [0u8; 4];
    s.read_exact(&mut len).await?;
    let n = u32::from_be_bytes(len) as usize;
    if !cfg!(feature = "mutate-oversized-frame") && n > MAX_FRAME {
        return Err(std::io::Error::other(format!("frame of {n} bytes")));
    }
    let mut b = vec![0; n];
    s.read_exact(&mut b).await?;
    serde_json::from_slice(&b).map_err(std::io::Error::other)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::net::TcpListener;

    #[tokio::test]
    async fn oversized_frame_is_rejected_without_waiting_for_body() {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let mut sender = TcpStream::connect(listener.local_addr().unwrap()).await.unwrap();
        let (mut receiver, _) = listener.accept().await.unwrap();
        sender.write_all(&((MAX_FRAME + 1) as u32).to_be_bytes()).await.unwrap();
        let result = tokio::time::timeout(Duration::from_millis(100), read_frame::<serde_json::Value>(&mut receiver)).await;
        assert!(matches!(result, Ok(Err(_))), "oversized frame waited for attacker body");
    }
}

/// One request/response exchange with a deadline covering connect, send and receive.
pub async fn call<Q: Serialize, A: DeserializeOwned>(addr: &str, req: &Q, timeout: Duration) -> std::io::Result<A> {
    let fut = async {
        let mut s = TcpStream::connect(addr).await?;
        s.set_nodelay(true)?;
        write_frame(&mut s, req).await?;
        read_frame(&mut s).await
    };
    match tokio::time::timeout(timeout, fut).await {
        Ok(r) => r,
        Err(_) => Err(std::io::Error::new(std::io::ErrorKind::TimedOut, format!("call to {addr} timed out"))),
    }
}
