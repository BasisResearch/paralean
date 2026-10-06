//! Framing for the P3 services: one JSON value per frame, each frame a 4-byte big-endian
//! length followed by that many bytes. A connection carries one request and its response
//! (no multiplexing); clients open one connection per call.

use std::time::Duration;

use serde::de::DeserializeOwned;
use serde::Serialize;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

/// Frames larger than this are refused (requests carry envelopes and receipts only).
pub const MAX_FRAME: usize = 16 << 20;

pub async fn write_frame<T: Serialize>(s: &mut TcpStream, v: &T) -> std::io::Result<()> {
    let b = serde_json::to_vec(v).map_err(std::io::Error::other)?;
    s.write_all(&(b.len() as u32).to_be_bytes()).await?;
    s.write_all(&b).await?;
    s.flush().await
}

pub async fn read_frame<T: DeserializeOwned>(s: &mut TcpStream) -> std::io::Result<T> {
    let mut len = [0u8; 4];
    s.read_exact(&mut len).await?;
    let n = u32::from_be_bytes(len) as usize;
    if n > MAX_FRAME {
        return Err(std::io::Error::other(format!("frame of {n} bytes")));
    }
    let mut b = vec![0; n];
    s.read_exact(&mut b).await?;
    serde_json::from_slice(&b).map_err(std::io::Error::other)
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
