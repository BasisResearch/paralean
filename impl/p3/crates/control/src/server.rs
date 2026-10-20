//! A minimal TCP service: each connection carries one framed request and its framed
//! response (`paralean_validator_api::rpc`).

use std::collections::HashMap;
use std::future::Future;
use std::hash::Hash;
use std::net::IpAddr;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use paralean_validator_api::rpc::{self, read_frame, write_frame, Service};
use paralean_store::Signer;
use serde::de::DeserializeOwned;
use serde::Serialize;
use tokio::net::TcpListener;
use tokio::task::JoinHandle;
use tokio::sync::{OwnedSemaphorePermit, Semaphore};

/// Admission happens in two separate stages, so neither can starve the other.
///
/// Before authentication a connection holds a handshake slot: bounded in all and per
/// source address, and released as soon as the request is authenticated (or the short
/// handshake deadline passes), so idle strangers cannot hold the service.
///
/// After authentication a connection holds an execution slot: the privileged principal
/// (the authority: Cancel, Status, the controller's dispatch to validators) has its own
/// reserved slots; every other principal shares the rest, at most `per_principal` each,
/// so one worker's long validations cannot take every slot. The execution deadline is
/// separate from the handshake deadline because legitimate Lean checks take minutes.
#[derive(Clone, Copy)]
struct Limits {
    handshakes: usize,
    handshakes_per_source: usize,
    executions: usize,
    per_principal: usize,
    privileged: usize,
    handshake: Duration,
    execution: Duration,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            handshakes: 128,
            handshakes_per_source: 32,
            executions: 64,
            per_principal: 16,
            privileged: 32,
            handshake: Duration::from_secs(5),
            execution: Duration::from_secs(900),
        }
    }
}

/// Counts per key (source address, principal), each at most `cap`.
struct PerKey<K: Eq + Hash + Copy> {
    cap: usize,
    counts: Mutex<HashMap<K, usize>>,
}

struct PerKeySlot<K: Eq + Hash + Copy> {
    owner: Arc<PerKey<K>>,
    key: K,
}

impl<K: Eq + Hash + Copy> PerKey<K> {
    fn new(cap: usize) -> Arc<Self> {
        Arc::new(PerKey { cap, counts: Mutex::new(HashMap::new()) })
    }
    fn try_enter(self: &Arc<Self>, key: K) -> Option<PerKeySlot<K>> {
        let mut counts = self.counts.lock().unwrap();
        let n = counts.entry(key).or_insert(0);
        if *n >= self.cap {
            return None;
        }
        *n += 1;
        Some(PerKeySlot { owner: self.clone(), key })
    }
}

impl<K: Eq + Hash + Copy> Drop for PerKeySlot<K> {
    fn drop(&mut self) {
        let mut counts = self.owner.counts.lock().unwrap();
        if let Some(n) = counts.get_mut(&self.key) {
            *n -= 1;
            if *n == 0 {
                counts.remove(&self.key);
            }
        }
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
/// to the operation and any identity claimed in the request. `privileged` (the
/// authority key) gets execution slots no other principal can take.
pub fn serve_authenticated<Q, A, F, Fut, Auth>(
    listener: TcpListener, signer: Signer, privileged: [u8; 32], authorize: Auth, handle: F,
) -> JoinHandle<()>
where
    Q: DeserializeOwned + Serialize + Service + Send + 'static,
    A: Serialize + Send + Sync + 'static,
    F: Fn(Q) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = A> + Send + 'static,
    Auth: Fn(&Q, &[u8; 32]) -> bool + Send + Sync + 'static,
{
    serve_authenticated_limited(listener, signer, privileged, authorize, handle, Limits::default())
}

fn serve_authenticated_limited<Q, A, F, Fut, Auth>(
    listener: TcpListener, signer: Signer, privileged: [u8; 32], authorize: Auth, handle: F, limits: Limits,
) -> JoinHandle<()>
where
    Q: DeserializeOwned + Serialize + Service + Send + 'static,
    A: Serialize + Send + Sync + 'static,
    F: Fn(Q) -> Fut + Send + Sync + 'static,
    Fut: Future<Output = A> + Send + 'static,
    Auth: Fn(&Q, &[u8; 32]) -> bool + Send + Sync + 'static,
{
    let handle = Arc::new(handle);
    let authorize = Arc::new(authorize);
    let unbounded = cfg!(feature = "mutate-unbounded-rpc");
    let shared_pool = cfg!(feature = "mutate-shared-rpc-pool");
    let handshakes = Arc::new(Semaphore::new(if unbounded { 65536 } else { limits.handshakes }));
    let sources = PerKey::<IpAddr>::new(if cfg!(feature = "mutate-no-per-source-admission") { usize::MAX } else { limits.handshakes_per_source });
    let executions = Arc::new(Semaphore::new(limits.executions));
    let reserved = Arc::new(Semaphore::new(limits.privileged));
    let principals = PerKey::<[u8; 32]>::new(if shared_pool { usize::MAX } else { limits.per_principal });
    tokio::spawn(async move {
        loop {
            let Ok((mut sock, peer)) = listener.accept().await else { continue };
            // Do not queue a task waiting for a permit: that queue itself is a DoS.
            let Ok(handshake_slot) = handshakes.clone().try_acquire_owned() else { continue };
            let Some(source_slot) = sources.try_enter(peer.ip()) else { continue };
            let handle = handle.clone();
            let authorize = authorize.clone();
            let signer = signer.clone();
            let (executions, reserved, principals) = (executions.clone(), reserved.clone(), principals.clone());
            tokio::spawn(async move {
                let _ = sock.set_nodelay(true);
                let c = rpc::challenge(&signer, Q::NAME);
                let handshake = async {
                    write_frame(&mut sock, &c).await?;
                    read_frame::<rpc::SignedRequest<Q>>(&mut sock).await
                };
                let deadline = if cfg!(feature = "mutate-no-rpc-deadline") { Duration::from_secs(86400) } else { limits.handshake };
                let Ok(Ok(req)) = tokio::time::timeout(deadline, handshake).await else { return };
                if !rpc::verify_request(&req, &signer.public(), &c.nonce) || !authorize(&req.payload, &req.public) {
                    return;
                }
                drop((handshake_slot, source_slot));
                // Authenticated: an execution slot of this principal's pool, or nothing.
                let _execution: (OwnedSemaphorePermit, Option<PerKeySlot<[u8; 32]>>) = if req.public == privileged && !shared_pool {
                    let Ok(p) = reserved.try_acquire_owned() else { return };
                    (p, None)
                } else {
                    let Some(mine) = principals.try_enter(req.public) else { return };
                    let Ok(p) = executions.try_acquire_owned() else { return };
                    (p, Some(mine))
                };
                let Ok(resp) = tokio::time::timeout(limits.execution, handle(req.payload)).await else { return };
                let Ok(resp) = rpc::signed_response(resp, &signer, Q::NAME, &c.nonce) else { return };
                let _ = tokio::time::timeout(limits.handshake, write_frame(&mut sock, &resp)).await;
            });
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::net::{TcpSocket, TcpStream};
    use tokio::io::{AsyncReadExt, AsyncWriteExt};

    /// A test service: `Num(0)` holds its execution slot for three seconds.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
    #[serde(transparent)]
    struct Num(u32);
    impl Service for Num { const NAME: &'static str = "paralean/test-num"; }

    const TEST: &str = "paralean/test-num";

    fn limits(handshakes: usize) -> Limits {
        Limits {
            handshakes, handshakes_per_source: handshakes + 64, executions: 8, per_principal: 8, privileged: 2,
            handshake: Duration::from_millis(150), execution: Duration::from_secs(5),
        }
    }

    async fn server_with(limits: Limits, allowed: Vec<[u8; 32]>, privileged: [u8; 32]) -> (String, Signer, JoinHandle<()>) {
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let signer = Signer::generate();
        let task = serve_authenticated_limited(listener, signer.clone(), privileged, move |_: &Num, p| allowed.contains(p),
            |n: Num| async move {
                if n.0 == 0 { tokio::time::sleep(Duration::from_secs(3)).await }
                Num(n.0 + 1)
            },
            limits);
        (addr, signer, task)
    }

    async fn server(handshakes: usize) -> (String, Signer, JoinHandle<()>) {
        let key = Signer::derive("server-test-caller");
        let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap().to_string();
        let signer = key.clone();
        let public = key.public();
        let task = serve_authenticated_limited(listener, signer.clone(), [0; 32], move |_: &Num, p| p == &public,
            |n: Num| async move { Num(n.0 + 1) }, limits(handshakes));
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
        let answer: Num = rpc::call_authenticated(&addr, &Num(41), &signer, &signer.public(), Duration::from_secs(1)).await.unwrap();
        task.abort();
        assert_eq!(answer, Num(42));
    }

    #[tokio::test]
    async fn long_authenticated_calls_cannot_lock_out_the_authority() {
        let (authority, b, c, d) = (Signer::derive("srv-authority"), Signer::derive("srv-b"), Signer::derive("srv-c"), Signer::derive("srv-d"));
        let l = Limits { executions: 3, per_principal: 2, privileged: 1, ..limits(64) };
        let allowed = vec![authority.public(), b.public(), c.public(), d.public()];
        let (addr, server_key, task) = server_with(l, allowed, authority.public()).await;
        let server = server_key.public();
        let call = |who: &Signer, n: u32| {
            let (addr, who) = (addr.clone(), who.clone());
            async move { rpc::call_authenticated::<_, Num>(&addr, &Num(n), &who, &server, Duration::from_secs(5)).await }
        };
        let spawn_long = |who: &Signer| tokio::spawn(call(who, 0));
        let held_b = [spawn_long(&b), spawn_long(&b)];
        tokio::time::sleep(Duration::from_millis(300)).await;
        // One principal holds at most `per_principal` executions ...
        assert!(call(&b, 1).await.is_err(), "a principal exceeded its execution cap");
        // ... so another principal is still served.
        assert_eq!(call(&c, 1).await.unwrap(), Num(2));
        let held_c = spawn_long(&c);
        tokio::time::sleep(Duration::from_millis(300)).await;
        // Every shared execution slot is taken now; the authority's reserved one is not.
        assert!(call(&d, 1).await.is_err(), "the shared pool exceeded its bound");
        let t0 = std::time::Instant::now();
        assert_eq!(call(&authority, 7).await.unwrap(), Num(8), "the authority was locked out");
        assert!(t0.elapsed() < Duration::from_secs(1));
        for h in held_b { assert_eq!(h.await.unwrap().unwrap(), Num(1)); }
        assert_eq!(held_c.await.unwrap().unwrap(), Num(1));
        task.abort();
    }

    #[tokio::test]
    async fn one_source_cannot_hold_every_handshake_slot() {
        let caller = Signer::derive("srv-source-caller");
        let l = Limits { handshakes_per_source: 2, ..limits(8) };
        let (addr, server_key, task) = server_with(l, vec![caller.public()], [0; 32]).await;
        let from = |ip: &str| {
            let (ip, addr) = (ip.parse::<std::net::IpAddr>().unwrap(), addr.clone());
            async move {
                let s = TcpSocket::new_v4().unwrap();
                s.bind(std::net::SocketAddr::new(ip, 0)).unwrap();
                s.connect(addr.parse().unwrap()).await.unwrap()
            }
        };
        // Two idle connections from 127.0.0.2 hold that source's handshake slots.
        let mut idle = Vec::new();
        for _ in 0..2 {
            let mut s = from("127.0.0.2").await;
            let _: rpc::Challenge = read_frame(&mut s).await.unwrap();
            idle.push(s);
        }
        let mut third = from("127.0.0.2").await;
        let result = tokio::time::timeout(Duration::from_millis(100), read_frame::<rpc::Challenge>(&mut third)).await;
        assert!(matches!(result, Ok(Err(_))), "a source exceeded its handshake cap: {result:?}");
        // Another source still completes an authenticated call meanwhile.
        let mut other = from("127.0.0.1").await;
        let c: rpc::Challenge = read_frame(&mut other).await.unwrap();
        assert!(rpc::verify_challenge(&c, TEST, &server_key.public()));
        write_frame(&mut other, &rpc::signed_request(Num(1), &caller, &server_key.public(), &c.nonce).unwrap()).await.unwrap();
        let resp: rpc::SignedResponse<Num> = read_frame(&mut other).await.unwrap();
        assert!(rpc::verify_response(&resp, TEST, &server_key.public(), &c.nonce));
        assert_eq!(resp.payload, Num(2));
        task.abort();
    }
}
