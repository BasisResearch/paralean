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

/// The service a request type is for. It is part of every signature of an exchange, so
/// a request signed for one service (a validator) is not valid at another (the
/// controller), even where the two request encodings coincide.
pub trait Service {
    const NAME: &'static str;
}

impl<T: Service + ?Sized> Service for &T {
    const NAME: &'static str = T::NAME;
}

/// What a signature of one exchange binds: domain (challenge, request or response), the
/// service, the server's public key, the connection nonce and the payload. The nonce
/// stops a captured request from being replayed on the next connection's challenge;
/// the server key and service stop a server (a malicious validator) from relaying a
/// request it was sent, with a nonce it chose, to another server.
pub fn auth_id<T: Serialize>(domain: &[u8], service: &str, server: &[u8; 32], nonce: &[u8; 32], payload: &T) -> std::io::Result<Id> {
    let bytes = serde_json::to_vec(payload).map_err(std::io::Error::other)?;
    let mut preimage = Vec::with_capacity(domain.len() + 4 + service.len() + 64 + bytes.len());
    preimage.extend_from_slice(domain);
    if !cfg!(feature = "mutate-unbound-rpc-peer") {
        preimage.extend_from_slice(&(service.len() as u32).to_be_bytes());
        preimage.extend_from_slice(service.as_bytes());
        preimage.extend_from_slice(server);
    }
    preimage.extend_from_slice(nonce);
    preimage.extend_from_slice(&bytes);
    Ok(Id(sha256(&preimage)))
}

const CHALLENGE: &[u8] = b"paralean/rpc/challenge/v2";
const REQUEST: &[u8] = b"paralean/rpc/request/v2";
const RESPONSE: &[u8] = b"paralean/rpc/response/v2";

pub fn challenge(signer: &Signer, service: &str) -> Challenge {
    let nonce = rand::random();
    let signature = signer.sign(&auth_id(CHALLENGE, service, &signer.public(), &nonce, &()).expect("unit encodes")).to_vec();
    Challenge { nonce, signature }
}

pub fn verify_challenge(c: &Challenge, service: &str, public: &[u8; 32]) -> bool {
    auth_id(CHALLENGE, service, public, &c.nonce, &())
        .is_ok_and(|id| verify(public, &id, &c.signature))
}

/// A request for the server with key `server`, on the connection whose challenge carried
/// `nonce`.
pub fn signed_request<Q: Serialize + Service>(payload: Q, signer: &Signer, server: &[u8; 32], nonce: &[u8; 32]) -> std::io::Result<SignedRequest<Q>> {
    let signature = signer.sign(&auth_id(REQUEST, Q::NAME, server, nonce, &payload)?).to_vec();
    Ok(SignedRequest { public: signer.public(), payload, signature })
}

/// The server with key `server` checks a request on its connection (challenge `nonce`).
pub fn verify_request<Q: Serialize + Service>(r: &SignedRequest<Q>, server: &[u8; 32], nonce: &[u8; 32]) -> bool {
    auth_id(REQUEST, Q::NAME, server, nonce, &r.payload)
        .is_ok_and(|id| verify(&r.public, &id, &r.signature))
}

pub fn signed_response<A: Serialize>(payload: A, signer: &Signer, service: &str, nonce: &[u8; 32]) -> std::io::Result<SignedResponse<A>> {
    let signature = signer.sign(&auth_id(RESPONSE, service, &signer.public(), nonce, &payload)?).to_vec();
    Ok(SignedResponse { payload, signature })
}

pub fn verify_response<A: Serialize>(r: &SignedResponse<A>, service: &str, server: &[u8; 32], nonce: &[u8; 32]) -> bool {
    auth_id(RESPONSE, service, server, nonce, &r.payload)
        .is_ok_and(|id| verify(server, &id, &r.signature))
}

/// Authenticate both peers, the request, and the response on this connection.
pub async fn call_authenticated<Q: Serialize + Service, A: DeserializeOwned + Serialize>(
    addr: &str, req: &Q, signer: &Signer, server_public: &[u8; 32], timeout: Duration,
) -> std::io::Result<A> {
    let fut = async {
        let mut s = tokio::time::timeout(Duration::from_secs(2), TcpStream::connect(addr)).await
            .map_err(|_| std::io::Error::new(std::io::ErrorKind::TimedOut, "RPC connect timed out"))??;
        s.set_nodelay(true)?;
        let c: Challenge = read_frame(&mut s).await?;
        if !verify_challenge(&c, Q::NAME, server_public) {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "server authentication failed"));
        }
        write_frame(&mut s, &signed_request(req, signer, server_public, &c.nonce)?).await?;
        let resp: SignedResponse<A> = read_frame(&mut s).await?;
        if !verify_response(&resp, Q::NAME, server_public, &c.nonce) {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "response authentication failed"));
        }
        Ok(resp.payload)
    };
    tokio::time::timeout(timeout, fut).await.unwrap_or_else(|_| Err(std::io::Error::new(std::io::ErrorKind::TimedOut, format!("call to {addr} timed out"))))
}

/// Accept a server signed by any currently configured validator key. The key that
/// signed the challenge must also sign the response.
pub async fn call_authenticated_any<Q: Serialize + Service, A: DeserializeOwned + Serialize>(
    addr: &str, req: &Q, signer: &Signer, server_keys: &[[u8; 32]], timeout: Duration,
) -> std::io::Result<A> {
    let fut = async {
        let mut s = tokio::time::timeout(Duration::from_secs(2), TcpStream::connect(addr)).await
            .map_err(|_| std::io::Error::new(std::io::ErrorKind::TimedOut, "RPC connect timed out"))??;
        s.set_nodelay(true)?;
        let c: Challenge = read_frame(&mut s).await?;
        let Some(public) = server_keys.iter().find(|key| verify_challenge(&c, Q::NAME, key)) else {
            return Err(std::io::Error::new(std::io::ErrorKind::PermissionDenied, "validator authentication failed"));
        };
        write_frame(&mut s, &signed_request(req, signer, public, &c.nonce)?).await?;
        let resp: SignedResponse<A> = read_frame(&mut s).await?;
        if !verify_response(&resp, Q::NAME, public, &c.nonce) {
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

    /// Another service whose request encodes exactly like the validator's `Status`.
    #[derive(Serialize)]
    #[serde(tag = "op", rename_all = "snake_case")]
    enum Other { Status }
    impl Service for Other { const NAME: &'static str = "paralean/test-other"; }

    #[test]
    fn request_signature_binds_server_key_and_service() {
        // A malicious validator chooses the nonce of its own challenge: it can copy the
        // controller's challenge nonce and have the authority sign a request with it.
        let authority = Signer::derive("rpc-binding-authority");
        let validator = Signer::derive("rpc-binding-validator");
        let controller = Signer::derive("rpc-binding-controller");
        let nonce = challenge(&controller, "paralean/controller").nonce;
        let sent = signed_request(crate::ValidatorRequest::Status, &authority, &validator.public(), &nonce).unwrap();
        assert!(verify_request(&sent, &validator.public(), &nonce), "genuine request refused");
        // Relayed to another server on that nonce: refused.
        assert!(!verify_request(&sent, &controller.public(), &nonce), "request valid at another server");
        // Read as another service's request with the same encoding: refused.
        let relabelled = SignedRequest { public: sent.public, payload: Other::Status, signature: sent.signature.clone() };
        assert_eq!(serde_json::to_vec(&relabelled.payload).unwrap(), serde_json::to_vec(&sent.payload).unwrap());
        assert!(!verify_request(&relabelled, &validator.public(), &nonce), "request valid for another service");
        // Challenges and responses are bound the same way.
        let c = challenge(&validator, "paralean/validator");
        assert!(verify_challenge(&c, "paralean/validator", &validator.public()));
        assert!(!verify_challenge(&c, "paralean/controller", &validator.public()));
        let r = signed_response(1u32, &validator, "paralean/validator", &c.nonce).unwrap();
        assert!(verify_response(&r, "paralean/validator", &validator.public(), &c.nonce));
        assert!(!verify_response(&r, "paralean/controller", &validator.public(), &c.nonce));
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
