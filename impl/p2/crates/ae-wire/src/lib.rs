//! Bounded authenticated request/response transport for anti-entropy.
//!
//! One TCP connection carries one request and one response. Each frame signs the
//! protocol version, source/target deployment identities, a client nonce, the
//! request digest (response only), body lengths, and both body hashes. Peers are
//! accepted only when their deployment ID maps to their pinned Ed25519 public key.
//! Authentication and integrity are provided; the TCP bytes are plaintext. Deploy
//! it on a private network or behind a confidential transport if secrecy is needed.
//! The request nonce is random; the signed response must echo it and the exact
//! signed request digest. Requests are read-only at the service layer, so replay
//! of an old *request* is harmless; replay of an old response is detected.
//!
//! Metadata is capped at 1 MiB and optional object bytes at 64 MiB. Lengths are
//! checked before allocation, and object bytes are read into a bounded Vec in
//! 16 KiB chunks. One timeout covers an entire frame read or write; a slow peer cannot extend
//! the deadline by sending one byte at a time. Server concurrency is bounded.

use std::collections::HashMap;
use std::fmt;
use std::future::Future;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use rand::rngs::OsRng;
use rand::RngCore;
use sha2::{Digest, Sha256};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::{watch, Semaphore};
use tokio::task::JoinSet;

const MAGIC: &[u8; 4] = b"PAE1";
pub const VERSION: u16 = 1;
const REQUEST: u8 = 1;
const RESPONSE: u8 = 2;
const MAX_ID: usize = 128;
const TRAILER_LEN: usize = 32 + 32 + 4 + 8 + 32 + 32 + 64;
pub const MAX_METADATA: usize = 1024 * 1024;
pub const MAX_OBJECT: usize = 64 * 1024 * 1024;

#[derive(Clone)]
pub struct Identity {
    pub deployment: String,
    pub signing_key: SigningKey,
}

#[derive(Clone, Debug)]
pub struct Peer {
    pub deployment: String,
    pub verifying_key: VerifyingKey,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Payload {
    pub metadata: Vec<u8>,
    pub object: Vec<u8>,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub timeout: Duration,
    pub max_connections: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            max_connections: 2,
        }
    }
}

#[derive(Debug)]
pub enum WireError {
    Io(std::io::Error),
    Timeout,
    Invalid(&'static str),
    Authentication(&'static str),
    TooLarge(&'static str),
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "I/O: {error}"),
            Self::Timeout => write!(f, "wire operation timed out"),
            Self::Invalid(why) => write!(f, "invalid wire frame: {why}"),
            Self::Authentication(why) => write!(f, "wire authentication failed: {why}"),
            Self::TooLarge(what) => write!(f, "wire limit exceeded: {what}"),
        }
    }
}

impl std::error::Error for WireError {}
impl From<std::io::Error> for WireError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

type Result<T> = std::result::Result<T, WireError>;

fn digest(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn valid_id(id: &str) -> bool {
    !id.is_empty() && id.len() <= MAX_ID && id.bytes().all(|b| b.is_ascii_graphic())
}

fn validate_payload(payload: &Payload) -> Result<()> {
    if payload.metadata.len() > MAX_METADATA {
        return Err(WireError::TooLarge("metadata"));
    }
    if payload.object.len() > MAX_OBJECT {
        return Err(WireError::TooLarge("object"));
    }
    Ok(())
}

struct Frame {
    kind: u8,
    source: String,
    target: String,
    nonce: [u8; 32],
    request_digest: [u8; 32],
    payload: Payload,
    signature: Signature,
    signed_header: Vec<u8>,
}

impl Frame {
    fn new(
        kind: u8,
        source: &Identity,
        target: &str,
        nonce: [u8; 32],
        request_digest: [u8; 32],
        payload: Payload,
    ) -> Result<Self> {
        if !valid_id(&source.deployment) || !valid_id(target) {
            return Err(WireError::Invalid("deployment identity"));
        }
        validate_payload(&payload)?;
        let signed_header = header(
            kind,
            &source.deployment,
            target,
            nonce,
            request_digest,
            &payload,
        );
        let signature = source.signing_key.sign(&signed_header);
        Ok(Self {
            kind,
            source: source.deployment.clone(),
            target: target.to_owned(),
            nonce,
            request_digest,
            payload,
            signature,
            signed_header,
        })
    }

    fn digest(&self) -> [u8; 32] {
        let mut h = Sha256::new();
        h.update(&self.signed_header);
        h.update(self.signature.to_bytes());
        h.finalize().into()
    }

    fn verify_header(&self, peer: &Peer, target: &str, kind: u8) -> Result<()> {
        if self.kind != kind || self.source != peer.deployment || self.target != target {
            return Err(WireError::Authentication(
                "peer, target or message type mismatch",
            ));
        }
        let verified = if cfg!(feature = "mutate-weak-signature") {
            ed25519_dalek::Verifier::verify(&peer.verifying_key, &self.signed_header, &self.signature).is_ok()
        } else {
            paralean_crypto::verify(&peer.verifying_key.to_bytes(), &self.signed_header, &self.signature.to_bytes())
        };
        if !verified { return Err(WireError::Authentication("signature")); }
        Ok(())
    }

    fn verify_body(&self) -> Result<()> {
        if digest(&self.payload.metadata) != metadata_hash(&self.signed_header)
            || digest(&self.payload.object) != object_hash(&self.signed_header)
        {
            return Err(WireError::Authentication("body hash"));
        }
        Ok(())
    }
}

fn header(
    kind: u8,
    source: &str,
    target: &str,
    nonce: [u8; 32],
    request_digest: [u8; 32],
    payload: &Payload,
) -> Vec<u8> {
    let mut h = Vec::with_capacity(4 + 2 + 1 + 2 + 2 + source.len() + target.len() + TRAILER_LEN);
    h.extend_from_slice(MAGIC);
    h.extend_from_slice(&VERSION.to_be_bytes());
    h.push(kind);
    h.extend_from_slice(&(source.len() as u16).to_be_bytes());
    h.extend_from_slice(&(target.len() as u16).to_be_bytes());
    h.extend_from_slice(source.as_bytes());
    h.extend_from_slice(target.as_bytes());
    h.extend_from_slice(&nonce);
    h.extend_from_slice(&request_digest);
    h.extend_from_slice(&(payload.metadata.len() as u32).to_be_bytes());
    h.extend_from_slice(&(payload.object.len() as u64).to_be_bytes());
    h.extend_from_slice(&digest(&payload.metadata));
    h.extend_from_slice(&digest(&payload.object));
    h
}

fn metadata_hash(header: &[u8]) -> [u8; 32] {
    header[header.len() - 64..header.len() - 32]
        .try_into()
        .unwrap()
}
fn object_hash(header: &[u8]) -> [u8; 32] {
    header[header.len() - 32..].try_into().unwrap()
}

async fn write_frame<W: AsyncWrite + Unpin>(
    writer: &mut W,
    frame: &Frame,
    timeout: Duration,
) -> Result<()> {
    tokio::time::timeout(timeout, async {
        writer.write_all(&frame.signed_header).await?;
        writer.write_all(&frame.signature.to_bytes()).await?;
        writer.write_all(&frame.payload.metadata).await?;
        writer.write_all(&frame.payload.object).await?;
        writer.flush().await
    })
    .await
    .map_err(|_| WireError::Timeout)??;
    Ok(())
}

async fn read_body<R: AsyncRead + Unpin>(reader: &mut R, len: usize) -> std::io::Result<Vec<u8>> {
    let mut body = Vec::with_capacity(len);
    let mut chunk = [0u8; 16 * 1024];
    while body.len() < len {
        let n = (len - body.len()).min(chunk.len());
        reader.read_exact(&mut chunk[..n]).await?;
        body.extend_from_slice(&chunk[..n]);
    }
    Ok(body)
}

async fn read_frame<R, V>(reader: &mut R, timeout: Duration, validate_header: V) -> Result<Frame>
where
    R: AsyncRead + Unpin,
    V: FnOnce(&Frame) -> Result<()>,
{
    tokio::time::timeout(timeout, read_frame_inner(reader, validate_header))
        .await
        .map_err(|_| WireError::Timeout)?
}

async fn read_frame_inner<R, V>(reader: &mut R, validate_header: V) -> Result<Frame>
where
    R: AsyncRead + Unpin,
    V: FnOnce(&Frame) -> Result<()>,
{
    let mut prefix = [0u8; 11];
    reader.read_exact(&mut prefix).await?;
    if &prefix[..4] != MAGIC || u16::from_be_bytes([prefix[4], prefix[5]]) != VERSION {
        return Err(WireError::Invalid("magic or protocol version"));
    }
    let kind = prefix[6];
    if kind != REQUEST && kind != RESPONSE {
        return Err(WireError::Invalid("message type"));
    }
    let source_len = u16::from_be_bytes([prefix[7], prefix[8]]) as usize;
    let target_len = u16::from_be_bytes([prefix[9], prefix[10]]) as usize;
    if source_len == 0 || source_len > MAX_ID || target_len == 0 || target_len > MAX_ID {
        return Err(WireError::TooLarge("deployment identity"));
    }
    let mut rest = vec![0u8; source_len + target_len + TRAILER_LEN];
    reader.read_exact(&mut rest).await?;
    let source = std::str::from_utf8(&rest[..source_len])
        .map_err(|_| WireError::Invalid("source UTF-8"))?
        .to_owned();
    let target = std::str::from_utf8(&rest[source_len..source_len + target_len])
        .map_err(|_| WireError::Invalid("target UTF-8"))?
        .to_owned();
    if !valid_id(&source) || !valid_id(&target) {
        return Err(WireError::Invalid("deployment identity"));
    }
    let mut offset = source_len + target_len;
    let nonce: [u8; 32] = rest[offset..offset + 32].try_into().unwrap();
    offset += 32;
    let request_digest: [u8; 32] = rest[offset..offset + 32].try_into().unwrap();
    offset += 32;
    let metadata_len = u32::from_be_bytes(rest[offset..offset + 4].try_into().unwrap()) as usize;
    offset += 4;
    let object_len = u64::from_be_bytes(rest[offset..offset + 8].try_into().unwrap());
    offset += 8;
    if metadata_len > MAX_METADATA {
        return Err(WireError::TooLarge("metadata"));
    }
    if object_len > MAX_OBJECT as u64 {
        return Err(WireError::TooLarge("object"));
    }
    offset += 64; // two body hashes in the signed header
    let signature = Signature::from_bytes(&rest[offset..offset + 64].try_into().unwrap());
    let mut signed_header = prefix.to_vec();
    signed_header.extend_from_slice(&rest[..offset]);
    let mut frame = Frame {
        kind,
        source,
        target,
        nonce,
        request_digest,
        payload: Payload::default(),
        signature,
        signed_header,
    };
    // Authenticate a few hundred header bytes before allocating up to 64 MiB.
    validate_header(&frame)?;
    frame.payload.metadata = read_body(reader, metadata_len).await?;
    frame.payload.object = read_body(reader, object_len as usize).await?;
    frame.verify_body()?;
    Ok(frame)
}

/// Make one authenticated request. The server identity and key must be pinned by the caller.
pub async fn exchange(
    addr: SocketAddr,
    own: &Identity,
    server: &Peer,
    payload: Payload,
    limits: Limits,
) -> Result<Payload> {
    let mut nonce = [0u8; 32];
    OsRng.fill_bytes(&mut nonce);
    let request = Frame::new(REQUEST, own, &server.deployment, nonce, [0; 32], payload)?;
    let mut stream = tokio::time::timeout(limits.timeout, TcpStream::connect(addr))
        .await
        .map_err(|_| WireError::Timeout)??;
    write_frame(&mut stream, &request, limits.timeout).await?;
    let response = read_frame(&mut stream, limits.timeout, |frame| {
        frame.verify_header(server, &own.deployment, RESPONSE)?;
        if frame.nonce != nonce || frame.request_digest != request.digest() {
            return Err(WireError::Authentication(
                "response nonce or request digest",
            ));
        }
        Ok(())
    })
    .await?;
    Ok(response.payload)
}

/// Serve read-only requests. `peers` maps deployment IDs to pinned public keys.
/// The handler receives authenticated peer identity and bounded opaque bytes.
pub async fn serve<H, F>(
    listener: TcpListener,
    own: Identity,
    peers: HashMap<String, VerifyingKey>,
    limits: Limits,
    handler: H,
) -> Result<()>
where
    H: Fn(Peer, Payload) -> F + Send + Sync + 'static,
    F: Future<Output = Payload> + Send + 'static,
{
    let (_stop_tx, stop_rx) = watch::channel(false);
    serve_with_shutdown(listener, own, peers, limits, stop_rx, handler).await
}

/// Serve until shutdown, then abort and join in-flight handlers. Dropping this
/// future also aborts tracked handlers through `JoinSet`'s drop behavior.
pub async fn serve_with_shutdown<H, F>(
    listener: TcpListener,
    own: Identity,
    peers: HashMap<String, VerifyingKey>,
    limits: Limits,
    mut shutdown: watch::Receiver<bool>,
    handler: H,
) -> Result<()>
where
    H: Fn(Peer, Payload) -> F + Send + Sync + 'static,
    F: Future<Output = Payload> + Send + 'static,
{
    if !valid_id(&own.deployment) || limits.max_connections == 0 {
        return Err(WireError::Invalid("server identity or connection limit"));
    }
    let semaphore = Arc::new(Semaphore::new(limits.max_connections));
    let handler = Arc::new(handler);
    let own = Arc::new(own);
    let peers = Arc::new(peers);
    let mut tasks = JoinSet::new();
    loop {
        if *shutdown.borrow() {
            break;
        }
        tokio::select! {
            changed = shutdown.changed() => {
                if changed.is_err() || *shutdown.borrow() {
                    break;
                }
            }
            completed = tasks.join_next(), if !tasks.is_empty() => {
                if let Some(Err(error)) = completed {
                    eprintln!("ae-wire: connection task: {error}");
                }
            }
            accepted = listener.accept() => {
                let (mut stream, _) = accepted?;
                let Ok(permit) = semaphore.clone().try_acquire_owned() else {
                    continue;
                };
                let (handler, own, peers) = (handler.clone(), own.clone(), peers.clone());
                tasks.spawn(async move {
                    let _permit = permit;
                    if let Err(error) = serve_one(&mut stream, &own, &peers, limits, &*handler).await {
                        eprintln!("ae-wire: {error}");
                    }
                });
            }
        }
    }
    tasks.abort_all();
    while tasks.join_next().await.is_some() {}
    Ok(())
}

async fn serve_one<H, F>(
    stream: &mut TcpStream,
    own: &Identity,
    peers: &HashMap<String, VerifyingKey>,
    limits: Limits,
    handler: &H,
) -> Result<()>
where
    H: Fn(Peer, Payload) -> F,
    F: Future<Output = Payload>,
{
    let request = read_frame(stream, limits.timeout, |frame| {
        let key = peers
            .get(&frame.source)
            .ok_or(WireError::Authentication("unknown source deployment"))?;
        let peer = Peer {
            deployment: frame.source.clone(),
            verifying_key: *key,
        };
        frame.verify_header(&peer, &own.deployment, REQUEST)?;
        if frame.request_digest != [0; 32] {
            return Err(WireError::Invalid("request digest must be zero"));
        }
        Ok(())
    })
    .await?;
    let key = peers
        .get(&request.source)
        .ok_or(WireError::Authentication("unknown source deployment"))?;
    let peer = Peer {
        deployment: request.source.clone(),
        verifying_key: *key,
    };
    let nonce = request.nonce;
    let request_digest = request.digest();
    let source = request.source.clone();
    let response_body = tokio::time::timeout(limits.timeout, handler(peer, request.payload))
        .await
        .map_err(|_| WireError::Timeout)?;
    let response = Frame::new(RESPONSE, own, &source, nonce, request_digest, response_body)?;
    write_frame(stream, &response, limits.timeout).await
}

#[cfg(test)]
#[path = "../../../../../verification/fixtures/ed25519_cases.rs"]
mod strict_vectors;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transport_strict_signature_vectors() {
        let source = identity("peer", 1);
        let frame = Frame::new(REQUEST, &source, "local", [9; 32], [0; 32], Payload::default()).unwrap();
        for case in strict_vectors::cases(source.signing_key.verifying_key().to_bytes(), frame.signature.to_bytes()) {
            let mut f = Frame::new(REQUEST, &source, "local", [9; 32], [0; 32], Payload::default()).unwrap();
            f.signature = Signature::from_bytes(&case.signature);
            let accepted = VerifyingKey::from_bytes(&case.public).is_ok_and(|verifying_key| {
                f.verify_header(&Peer { deployment: "peer".into(), verifying_key }, "local", REQUEST).is_ok()
            });
            assert_eq!(accepted, case.expected, "{}", case.name);
        }
    }

    #[test]
    fn weak_pinned_peer_key_is_rejected() {
        let source = identity("peer", 1);
        let mut frame = Frame::new(REQUEST, &source, "local", [9; 32], [0; 32], Payload::default()).unwrap();
        let mut public = [0; 32];
        public[0] = 1;
        let mut signature = [0; 64];
        signature[0] = 1;
        frame.signature = Signature::from_bytes(&signature);
        let weak = Peer { deployment: "peer".into(), verifying_key: VerifyingKey::from_bytes(&public).unwrap() };
        assert!(matches!(frame.verify_header(&weak, "local", REQUEST), Err(WireError::Authentication("signature"))));
        let valid = Frame::new(REQUEST, &source, "local", [9; 32], [0; 32], Payload::default()).unwrap();
        assert!(valid.verify_header(&peer(&source), "local", REQUEST).is_ok());
    }

    fn identity(name: &str, seed: u8) -> Identity {
        Identity {
            deployment: name.into(),
            signing_key: SigningKey::from_bytes(&[seed; 32]),
        }
    }

    fn peer(identity: &Identity) -> Peer {
        Peer {
            deployment: identity.deployment.clone(),
            verifying_key: identity.signing_key.verifying_key(),
        }
    }

    fn limits() -> Limits {
        Limits {
            timeout: Duration::from_millis(500),
            max_connections: 2,
        }
    }

    #[tokio::test]
    async fn binary_pages_round_trip_with_authenticated_peer() {
        let (client, server) = (identity("deployment-a", 1), identity("deployment-b", 2));
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let mut peers = HashMap::new();
        peers.insert(
            client.deployment.clone(),
            client.signing_key.verifying_key(),
        );
        let task = tokio::spawn(serve(
            listener,
            server.clone(),
            peers,
            limits(),
            |authenticated, request| async move {
                assert_eq!(authenticated.deployment, "deployment-a");
                Payload {
                    metadata: vec![request.metadata[0] + 1, 0, 255],
                    object: request.object,
                }
            },
        ));
        for cursor in 0..3 {
            let object = vec![0, 255, cursor, 0, 17];
            let response = exchange(
                addr,
                &client,
                &peer(&server),
                Payload {
                    metadata: vec![cursor, 255, 0],
                    object: object.clone(),
                },
                limits(),
            )
            .await
            .unwrap();
            assert_eq!(response.metadata, vec![cursor + 1, 0, 255]);
            assert_eq!(response.object, object);
        }
        task.abort();
    }

    #[tokio::test]
    async fn shutdown_aborts_and_joins_in_flight_handler() {
        struct OnDrop(Arc<std::sync::atomic::AtomicBool>);
        impl Drop for OnDrop {
            fn drop(&mut self) {
                self.0.store(true, std::sync::atomic::Ordering::SeqCst);
            }
        }

        let (client, server) = (identity("deployment-a", 1), identity("deployment-b", 2));
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let peers = HashMap::from([(
            client.deployment.clone(),
            client.signing_key.verifying_key(),
        )]);
        let (stop_tx, stop_rx) = watch::channel(false);
        let entered = Arc::new(tokio::sync::Notify::new());
        let dropped = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let entered_handler = entered.clone();
        let dropped_handler = dropped.clone();
        let server_task = tokio::spawn(serve_with_shutdown(
            listener,
            server.clone(),
            peers,
            limits(),
            stop_rx,
            move |_, _| {
                let entered = entered_handler.clone();
                let dropped = dropped_handler.clone();
                async move {
                    let _guard = OnDrop(dropped);
                    entered.notify_one();
                    std::future::pending::<Payload>().await
                }
            },
        ));
        let client_task = tokio::spawn(async move {
            exchange(addr, &client, &peer(&server), Payload::default(), limits()).await
        });
        tokio::time::timeout(Duration::from_secs(2), entered.notified())
            .await
            .unwrap();
        stop_tx.send(true).unwrap();
        tokio::time::timeout(Duration::from_secs(2), server_task)
            .await
            .expect("server did not stop")
            .unwrap()
            .unwrap();
        assert!(dropped.load(std::sync::atomic::Ordering::SeqCst));
        assert!(client_task.await.unwrap().is_err());
    }

    #[tokio::test]
    async fn wrong_server_signer_is_rejected() {
        let (client, expected, impostor) = (
            identity("deployment-a", 1),
            identity("deployment-b", 2),
            identity("deployment-b", 3),
        );
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let mut peers = HashMap::new();
        peers.insert(
            client.deployment.clone(),
            client.signing_key.verifying_key(),
        );
        let task = tokio::spawn(serve(
            listener,
            impostor,
            peers,
            limits(),
            |_, request| async move { request },
        ));
        let result = exchange(
            addr,
            &client,
            &peer(&expected),
            Payload::default(),
            limits(),
        )
        .await;
        assert!(matches!(
            result,
            Err(WireError::Authentication("signature"))
        ));
        task.abort();
    }

    #[tokio::test]
    async fn wrong_client_signer_is_rejected_before_handler() {
        let (expected_client, impostor, server) = (
            identity("deployment-a", 1),
            identity("deployment-a", 3),
            identity("deployment-b", 2),
        );
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let mut peers = HashMap::new();
        peers.insert(
            expected_client.deployment.clone(),
            expected_client.signing_key.verifying_key(),
        );
        let called = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let marker = called.clone();
        let task = tokio::spawn(serve(
            listener,
            server.clone(),
            peers,
            limits(),
            move |_, request| {
                let marker = marker.clone();
                async move {
                    marker.store(true, std::sync::atomic::Ordering::SeqCst);
                    request
                }
            },
        ));
        assert!(exchange(
            addr,
            &impostor,
            &peer(&server),
            Payload::default(),
            limits()
        )
        .await
        .is_err());
        assert!(!called.load(std::sync::atomic::Ordering::SeqCst));
        task.abort();
    }

    #[tokio::test]
    async fn signed_response_must_bind_fresh_nonce_and_request_hash() {
        for wrong_hash in [false, true] {
            let (client, server) = (identity("deployment-a", 1), identity("deployment-b", 2));
            let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let addr = listener.local_addr().unwrap();
            let server_clone = server.clone();
            let task = tokio::spawn(async move {
                let (mut stream, _) = listener.accept().await.unwrap();
                let request = read_frame(&mut stream, limits().timeout, |_| Ok(()))
                    .await
                    .unwrap();
                let mut nonce = request.nonce;
                let mut request_digest = request.digest();
                if wrong_hash {
                    request_digest[0] ^= 1;
                } else {
                    nonce[0] ^= 1;
                }
                let response = Frame::new(
                    RESPONSE,
                    &server_clone,
                    "deployment-a",
                    nonce,
                    request_digest,
                    Payload::default(),
                )
                .unwrap();
                write_frame(&mut stream, &response, limits().timeout)
                    .await
                    .unwrap();
            });
            let result =
                exchange(addr, &client, &peer(&server), Payload::default(), limits()).await;
            assert!(matches!(
                result,
                Err(WireError::Authentication(
                    "response nonce or request digest"
                ))
            ));
            task.await.unwrap();
        }
    }

    #[tokio::test]
    async fn tampered_body_is_rejected_after_signature_check() {
        let source = identity("deployment-a", 1);
        let frame = Frame::new(
            REQUEST,
            &source,
            "deployment-b",
            [9; 32],
            [0; 32],
            Payload {
                metadata: vec![0, 255],
                object: vec![1, 2, 3],
            },
        )
        .unwrap();
        let mut bytes = frame.signed_header.clone();
        bytes.extend_from_slice(&frame.signature.to_bytes());
        bytes.extend_from_slice(&frame.payload.metadata);
        bytes.extend_from_slice(&frame.payload.object);
        *bytes.last_mut().unwrap() ^= 1;
        let (mut writer, mut reader) = tokio::io::duplex(1024);
        writer.write_all(&bytes).await.unwrap();
        assert!(matches!(
            read_frame(&mut reader, limits().timeout, |frame| frame.verify_header(
                &peer(&source),
                "deployment-b",
                REQUEST
            ))
            .await,
            Err(WireError::Authentication("body hash"))
        ));
    }

    #[tokio::test]
    async fn oversized_declared_body_is_rejected_before_allocation() {
        let source = identity("deployment-a", 1);
        let frame = Frame::new(
            REQUEST,
            &source,
            "deployment-b",
            [9; 32],
            [0; 32],
            Payload::default(),
        )
        .unwrap();
        let mut header = frame.signed_header.clone();
        let metadata_len_offset = header.len() - (4 + 8 + 32 + 32);
        header[metadata_len_offset..metadata_len_offset + 4]
            .copy_from_slice(&((MAX_METADATA + 1) as u32).to_be_bytes());
        let (mut writer, mut reader) = tokio::io::duplex(1024);
        writer.write_all(&header).await.unwrap();
        writer.write_all(&frame.signature.to_bytes()).await.unwrap();
        assert!(matches!(
            read_frame(&mut reader, limits().timeout, |_| Ok(())).await,
            Err(WireError::TooLarge("metadata"))
        ));
        let mut header = frame.signed_header.clone();
        let object_len_offset = header.len() - (8 + 32 + 32);
        header[object_len_offset..object_len_offset + 8]
            .copy_from_slice(&((MAX_OBJECT + 1) as u64).to_be_bytes());
        let (mut writer, mut reader) = tokio::io::duplex(1024);
        writer.write_all(&header).await.unwrap();
        writer.write_all(&frame.signature.to_bytes()).await.unwrap();
        assert!(matches!(
            read_frame(&mut reader, limits().timeout, |_| Ok(())).await,
            Err(WireError::TooLarge("object"))
        ));
    }

    #[tokio::test]
    async fn unknown_or_bad_signer_with_large_declared_body_is_rejected_before_body() {
        let expected = identity("deployment-a", 1);
        let server = identity("deployment-b", 2);
        for attacker in [identity("unknown", 3), identity("deployment-a", 3)] {
            let frame = Frame::new(
                REQUEST,
                &attacker,
                "deployment-b",
                [9; 32],
                [0; 32],
                Payload::default(),
            )
            .unwrap();
            let mut header = frame.signed_header.clone();
            let object_len_offset = header.len() - (8 + 32 + 32);
            header[object_len_offset..object_len_offset + 8]
                .copy_from_slice(&(MAX_OBJECT as u64).to_be_bytes());
            let mut bytes = header;
            bytes.extend_from_slice(&frame.signature.to_bytes());
            let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let addr = listener.local_addr().unwrap();
            let writer = tokio::spawn(async move {
                let mut stream = TcpStream::connect(addr).await.unwrap();
                stream.write_all(&bytes).await.unwrap();
                tokio::time::sleep(Duration::from_millis(200)).await;
            });
            let (mut stream, _) = listener.accept().await.unwrap();
            let mut peers = HashMap::new();
            peers.insert(
                expected.deployment.clone(),
                expected.signing_key.verifying_key(),
            );
            let handler = |_, request: Payload| async move { request };
            let result = tokio::time::timeout(
                Duration::from_millis(100),
                serve_one(&mut stream, &server, &peers, limits(), &handler),
            )
            .await
            .expect("header rejection must not wait for the declared object body");
            assert!(matches!(result, Err(WireError::Authentication(_))));
            writer.abort();
        }
    }

    #[tokio::test]
    async fn silent_peer_times_out() {
        let (client, server) = (identity("deployment-a", 1), identity("deployment-b", 2));
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let task = tokio::spawn(async move {
            let (_stream, _) = listener.accept().await.unwrap();
            tokio::time::sleep(Duration::from_secs(1)).await;
        });
        let result = exchange(
            addr,
            &client,
            &peer(&server),
            Payload::default(),
            Limits {
                timeout: Duration::from_millis(50),
                max_connections: 2,
            },
        )
        .await;
        assert!(matches!(result, Err(WireError::Timeout)));
        task.abort();
    }
}
