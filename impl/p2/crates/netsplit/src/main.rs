//! netsplit: network partitions between local fdbserver processes, without root.
//!
//! Each fdbserver listens on a private port and advertises a public port served by this
//! proxy (`fdbserver -l 127.0.0.1:<private> -p 127.0.0.1:<public>`). Every connection to a
//! process (from another process, a coordinator lookup or a client) therefore passes
//! through the proxy of its destination. FDB's first bytes on a connection are its
//! `ConnectPacket` (`u32 length, u64 protocolVersion, u16 canonicalRemotePort, ...`, little
//! endian), whose port is the connecting process's public port; that identifies the source.
//!
//! The state file holds the isolated side `S` of the partition: whitespace-separated process
//! indices (empty: healed). A link is cut iff exactly one of its ends is in `S` (clients are
//! never in `S`). Cut links are blackholed, not closed: both sockets stay open and nothing
//! is forwarded, as in a real partition, until the link heals, when they are closed and
//! the processes reconnect. New connections across the cut hang the same way.
//!
//! Usage: `netsplit --state <file> --map <index>:<public port>:<private port> ...`

use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use std::time::Duration;

use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::watch;

type Split = Arc<BTreeSet<usize>>;

fn parse_state(s: &str) -> BTreeSet<usize> {
    s.split_whitespace().filter_map(|x| x.parse().ok()).collect()
}

fn is_cut(s: &BTreeSet<usize>, dest: usize, src: Option<usize>) -> bool {
    s.contains(&dest) != src.is_some_and(|i| s.contains(&i))
}

/// Wait until the cut status of the link differs from `now`.
async fn until_change(rx: &mut watch::Receiver<Split>, dest: usize, src: Option<usize>, now: bool) {
    loop {
        if rx.changed().await.is_err() {
            std::future::pending::<()>().await;
        }
        if is_cut(&rx.borrow(), dest, src) != now {
            return;
        }
    }
}

async fn conn(
    dest: usize,
    mut inbound: TcpStream,
    private: u16,
    mut rx: watch::Receiver<Split>,
    ports: Arc<HashMap<u16, usize>>,
) {
    // Identify the source from the ConnectPacket (clients and unknown peers: none).
    let mut head = [0u8; 14];
    let src = match tokio::time::timeout(Duration::from_secs(5), inbound.read_exact(&mut head)).await {
        Ok(Ok(_)) => ports.get(&u16::from_le_bytes([head[12], head[13]])).copied(),
        _ => return,
    };
    let now = is_cut(&rx.borrow(), dest, src);
    if now {
        // A new connection across the cut hangs until the link heals, then closes.
        until_change(&mut rx, dest, src, true).await;
        return;
    }
    let Ok(mut up) = TcpStream::connect(("127.0.0.1", private)).await else { return };
    let _ = up.set_nodelay(true);
    let _ = inbound.set_nodelay(true);
    if up.write_all(&head).await.is_err() {
        return;
    }
    tokio::select! {
        _ = tokio::io::copy_bidirectional(&mut inbound, &mut up) => {}
        _ = until_change(&mut rx, dest, src, false) => {
            eprintln!("netsplit: blackholed link {src:?} -> {dest}");
            // Hold both sockets open, forwarding nothing, until the link heals.
            until_change(&mut rx, dest, src, true).await;
            eprintln!("netsplit: healed link {src:?} -> {dest}; closing it");
        }
    }
}

async fn serve(dest: usize, public: u16, private: u16, rx: watch::Receiver<Split>, ports: Arc<HashMap<u16, usize>>) {
    let l = TcpListener::bind(("127.0.0.1", public)).await.unwrap_or_else(|e| panic!("bind {public}: {e}"));
    loop {
        let Ok((s, _)) = l.accept().await else { continue };
        tokio::spawn(conn(dest, s, private, rx.clone(), ports.clone()));
    }
}

#[tokio::main]
async fn main() {
    let mut state = None;
    let mut maps = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--state" => state = args.next(),
            "--map" => {
                let m = args.next().expect("--map needs index:public:private");
                let v: Vec<u16> = m.split(':').map(|x| x.parse().expect("--map index:public:private")).collect();
                assert_eq!(v.len(), 3, "--map index:public:private");
                maps.push((v[0] as usize, v[1], v[2]));
            }
            other => panic!("unknown argument {other}"),
        }
    }
    let state = state.expect("--state <file>");
    let ports: Arc<HashMap<u16, usize>> = Arc::new(maps.iter().map(|(i, p, _)| (*p, *i)).collect());
    let read = |f: &str| parse_state(&std::fs::read_to_string(f).unwrap_or_default());
    let (tx, rx) = watch::channel(Arc::new(read(&state)));
    for (i, p, q) in &maps {
        tokio::spawn(serve(*i, *p, *q, rx.clone(), ports.clone()));
    }
    eprintln!("netsplit: {} processes, state file {state}", maps.len());
    loop {
        tokio::time::sleep(Duration::from_millis(100)).await;
        let s = read(&state);
        if *tx.borrow() != Arc::new(s.clone()) {
            eprintln!("netsplit: isolated side now {s:?}");
            let _ = tx.send(Arc::new(s));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn cut_rule() {
        let s: BTreeSet<usize> = [1, 2].into();
        assert!(is_cut(&s, 1, Some(0)));
        assert!(is_cut(&s, 0, Some(2)));
        assert!(is_cut(&s, 1, None), "clients are on the majority side");
        assert!(!is_cut(&s, 1, Some(2)), "links inside the isolated side stay");
        assert!(!is_cut(&s, 0, Some(3)));
        assert!(!is_cut(&BTreeSet::new(), 0, Some(1)));
    }
}
