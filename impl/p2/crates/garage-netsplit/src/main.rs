//! Partition local Garage nodes at their RPC ports without firewall privileges.
//!
//! A Garage node `i` binds RPC to `127.0.0.(i+2):port`, advertises `127.0.0.1:port`,
//! and sets `rpc_bind_outgoing = true`. Garage therefore uses its private IP as the
//! source of every outgoing RPC connection. The public address is served here, so
//! peer links (including links already open when a split starts) have known ends.
//!
//! The state file contains the isolated nodes' indices, separated by whitespace.
//! An empty file heals the partition. Links between the two sides are blackholed:
//! sockets stay open and no bytes move until healing, at which point the sockets
//! close so Garage can reconnect. Local CLI clients use 127.0.0.1 and are considered
//! outside the isolated side. The proxy is for instance clusters only.
//!
//! Usage: garage-netsplit --state FILE --map INDEX:PUBLIC_PORT:PRIVATE_IP ...

use std::collections::{BTreeSet, HashMap};
use std::net::{IpAddr, Ipv4Addr};
use std::sync::Arc;
use std::time::Duration;

use tokio::io::copy_bidirectional;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::watch;

type Split = Arc<BTreeSet<usize>>;
type Sources = Arc<HashMap<IpAddr, usize>>;

#[derive(Clone, Copy)]
struct Node {
    index: usize,
    port: u16,
    private_ip: Ipv4Addr,
}

fn parse_state(contents: &str, valid: &BTreeSet<usize>) -> Result<BTreeSet<usize>, String> {
    contents
        .split_whitespace()
        .map(|index| {
            let parsed = index
                .parse::<usize>()
                .map_err(|_| format!("invalid Garage split node index {index:?}"))?;
            if !valid.contains(&parsed) {
                return Err(format!("unknown Garage split node index {parsed}"));
            }
            Ok(parsed)
        })
        .collect()
}

fn read_state(file: &str, valid: &BTreeSet<usize>) -> Result<BTreeSet<usize>, String> {
    let contents = std::fs::read_to_string(file)
        .map_err(|error| format!("read Garage split state {file}: {error}"))?;
    parse_state(&contents, valid)
}

fn is_cut(split: &BTreeSet<usize>, destination: usize, source: Option<usize>) -> bool {
    split.contains(&destination) != source.is_some_and(|i| split.contains(&i))
}

async fn until_change(
    receiver: &mut watch::Receiver<Split>,
    destination: usize,
    source: Option<usize>,
    was_cut: bool,
) {
    loop {
        if receiver.changed().await.is_err() {
            std::future::pending::<()>().await;
        }
        if is_cut(&receiver.borrow(), destination, source) != was_cut {
            return;
        }
    }
}

async fn connection(
    destination: Node,
    mut incoming: TcpStream,
    source: Option<usize>,
    mut receiver: watch::Receiver<Split>,
) {
    if is_cut(&receiver.borrow(), destination.index, source) {
        until_change(&mut receiver, destination.index, source, true).await;
        return;
    }

    let Ok(mut upstream) = TcpStream::connect((destination.private_ip, destination.port)).await
    else {
        return;
    };
    let _ = incoming.set_nodelay(true);
    let _ = upstream.set_nodelay(true);
    tokio::select! {
        _ = copy_bidirectional(&mut incoming, &mut upstream) => {}
        _ = until_change(&mut receiver, destination.index, source, false) => {
            eprintln!("garage-netsplit: blackholed link {source:?} -> {}", destination.index);
            until_change(&mut receiver, destination.index, source, true).await;
            eprintln!("garage-netsplit: healed link {source:?} -> {}; closing it", destination.index);
        }
    }
}

async fn serve(
    node: Node,
    listener: TcpListener,
    receiver: watch::Receiver<Split>,
    sources: Sources,
) {
    loop {
        let Ok((stream, peer)) = listener.accept().await else {
            continue;
        };
        let source = sources.get(&peer.ip()).copied();
        if source.is_none() && peer.ip() != IpAddr::V4(Ipv4Addr::LOCALHOST) {
            eprintln!("garage-netsplit: rejected unknown RPC source {}", peer.ip());
            continue;
        }
        tokio::spawn(connection(node, stream, source, receiver.clone()));
    }
}

fn parse_args() -> (String, Vec<Node>) {
    let mut state = None;
    let mut nodes = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--state" => state = Some(args.next().expect("--state needs a file")),
            "--map" => {
                let arg = args
                    .next()
                    .expect("--map needs INDEX:PUBLIC_PORT:PRIVATE_IP");
                let fields: Vec<_> = arg.split(':').collect();
                assert_eq!(fields.len(), 3, "--map needs INDEX:PUBLIC_PORT:PRIVATE_IP");
                let node = Node {
                    index: fields[0].parse().expect("invalid node index"),
                    port: fields[1].parse().expect("invalid public RPC port"),
                    private_ip: fields[2].parse().expect("invalid private IPv4 address"),
                };
                assert!(
                    node.private_ip.is_loopback() && node.private_ip != Ipv4Addr::LOCALHOST,
                    "private IP must be loopback and distinct from 127.0.0.1"
                );
                nodes.push(node);
            }
            _ => panic!("unknown argument {arg}"),
        }
    }
    assert!(!nodes.is_empty(), "at least one --map is required");
    let mut indices = BTreeSet::new();
    let mut ports = BTreeSet::new();
    let mut addresses = BTreeSet::new();
    for node in &nodes {
        assert!(indices.insert(node.index), "duplicate Garage node index");
        assert!(ports.insert(node.port), "duplicate Garage public RPC port");
        assert!(
            addresses.insert(node.private_ip),
            "duplicate Garage private IP"
        );
    }
    (state.expect("--state FILE is required"), nodes)
}

#[tokio::main]
async fn main() {
    let (state, nodes) = parse_args();
    let valid: BTreeSet<_> = nodes.iter().map(|node| node.index).collect();
    let sources: Sources = Arc::new(
        nodes
            .iter()
            .map(|n| (IpAddr::V4(n.private_ip), n.index))
            .collect(),
    );
    let initial = read_state(&state, &valid).unwrap_or_else(|error| panic!("{error}"));
    let (sender, receiver) = watch::channel(Arc::new(initial));
    let mut listeners = Vec::new();
    for node in &nodes {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, node.port))
            .await
            .unwrap_or_else(|error| panic!("bind Garage public RPC port {}: {error}", node.port));
        listeners.push((*node, listener));
    }
    for (node, listener) in listeners {
        tokio::spawn(serve(node, listener, receiver.clone(), sources.clone()));
    }
    eprintln!("garage-netsplit: {} nodes, state file {state}", nodes.len());
    let mut last_error = None;
    loop {
        tokio::time::sleep(Duration::from_millis(100)).await;
        let next = match read_state(&state, &valid) {
            Ok(next) => {
                last_error = None;
                next
            }
            Err(error) => {
                if last_error.as_ref() != Some(&error) {
                    eprintln!("garage-netsplit: {error}; retaining last valid split");
                    last_error = Some(error);
                }
                continue;
            }
        };
        if sender.borrow().as_ref() != &next {
            eprintln!("garage-netsplit: isolated nodes now {next:?}");
            let _ = sender.send(Arc::new(next));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::ErrorKind;
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    use tokio::net::TcpSocket;

    fn closed_after_dropping_unread_bytes(result: std::io::Result<usize>) -> bool {
        match result {
            Ok(0) => true,
            Err(error) if error.kind() == ErrorKind::ConnectionReset => true,
            _ => false,
        }
    }

    #[test]
    fn split_cuts_exactly_the_crossing_links() {
        let split = parse_state("1 2\n", &[0, 1, 2, 3].into()).unwrap();
        assert!(is_cut(&split, 1, Some(0)));
        assert!(is_cut(&split, 0, Some(2)));
        assert!(is_cut(&split, 1, None));
        assert!(!is_cut(&split, 1, Some(2)));
        assert!(!is_cut(&split, 0, Some(3)));
        assert!(!is_cut(&BTreeSet::new(), 1, Some(0)));
    }

    #[test]
    fn malformed_state_is_rejected() {
        let valid = [0, 1].into();
        assert!(parse_state("1 unknown", &valid).is_err());
        assert!(parse_state("2", &valid).is_err());
    }

    #[tokio::test]
    async fn loopback_source_ip_identifies_node_on_real_tcp_connection() {
        let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let socket = TcpSocket::new_v4().unwrap();
        socket
            .bind((Ipv4Addr::new(127, 0, 0, 2), 0).into())
            .unwrap();
        let _client = socket
            .connect(listener.local_addr().unwrap())
            .await
            .unwrap();
        let (_incoming, peer) = listener.accept().await.unwrap();
        assert_eq!(peer.ip(), IpAddr::V4(Ipv4Addr::new(127, 0, 0, 2)));
    }

    #[tokio::test]
    async fn open_link_blackholes_and_heal_closes_it() {
        let upstream = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let port = upstream.local_addr().unwrap().port();
        let public = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let public_port = public.local_addr().unwrap().port();
        let node = Node {
            index: 1,
            port,
            private_ip: Ipv4Addr::LOCALHOST,
        };
        let (sender, receiver) = watch::channel(Arc::new(BTreeSet::new()));
        let task = tokio::spawn(async move {
            let (incoming, _) = public.accept().await.unwrap();
            connection(node, incoming, Some(0), receiver).await;
        });
        let mut client = TcpStream::connect((Ipv4Addr::LOCALHOST, public_port))
            .await
            .unwrap();
        let (mut server, _) = upstream.accept().await.unwrap();
        client.write_all(b"a").await.unwrap();
        let mut byte = [0];
        server.read_exact(&mut byte).await.unwrap();
        assert_eq!(&byte, b"a");
        server.write_all(b"x").await.unwrap();
        client.read_exact(&mut byte).await.unwrap();
        assert_eq!(&byte, b"x");
        sender.send(Arc::new([1].into())).unwrap();
        tokio::time::sleep(Duration::from_millis(30)).await;
        client.write_all(b"b").await.unwrap();
        server.write_all(b"y").await.unwrap();
        assert!(
            tokio::time::timeout(Duration::from_millis(100), server.read_exact(&mut byte))
                .await
                .is_err()
        );
        assert!(
            tokio::time::timeout(Duration::from_millis(100), client.read_exact(&mut byte))
                .await
                .is_err()
        );
        sender.send(Arc::new(BTreeSet::new())).unwrap();
        assert!(closed_after_dropping_unread_bytes(
            tokio::time::timeout(Duration::from_secs(1), server.read(&mut byte))
                .await
                .unwrap()
        ));
        task.await.unwrap();
    }

    #[tokio::test]
    async fn new_connection_during_cut_hangs_then_closes_on_heal() {
        let upstream = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let public = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let node = Node {
            index: 1,
            port: upstream.local_addr().unwrap().port(),
            private_ip: Ipv4Addr::LOCALHOST,
        };
        let public_port = public.local_addr().unwrap().port();
        let (sender, receiver) = watch::channel(Arc::new([1].into()));
        let task = tokio::spawn(async move {
            let (incoming, _) = public.accept().await.unwrap();
            connection(node, incoming, Some(0), receiver).await;
        });
        let mut client = TcpStream::connect((Ipv4Addr::LOCALHOST, public_port))
            .await
            .unwrap();
        client.write_all(b"blocked").await.unwrap();
        assert!(
            tokio::time::timeout(Duration::from_millis(100), upstream.accept())
                .await
                .is_err()
        );
        let mut byte = [0];
        assert!(
            tokio::time::timeout(Duration::from_millis(100), client.read(&mut byte))
                .await
                .is_err()
        );
        sender.send(Arc::new(BTreeSet::new())).unwrap();
        assert!(closed_after_dropping_unread_bytes(
            tokio::time::timeout(Duration::from_secs(1), client.read(&mut byte))
                .await
                .unwrap()
        ));
        task.await.unwrap();
    }

    #[tokio::test]
    async fn peers_on_same_side_keep_transferring() {
        let upstream = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let public = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).await.unwrap();
        let node = Node {
            index: 1,
            port: upstream.local_addr().unwrap().port(),
            private_ip: Ipv4Addr::LOCALHOST,
        };
        let public_port = public.local_addr().unwrap().port();
        let (sender, receiver) = watch::channel(Arc::new([1, 2].into()));
        let task = tokio::spawn(async move {
            let (incoming, _) = public.accept().await.unwrap();
            connection(node, incoming, Some(2), receiver).await;
        });
        let mut client = TcpStream::connect((Ipv4Addr::LOCALHOST, public_port))
            .await
            .unwrap();
        let (mut server, _) = upstream.accept().await.unwrap();
        client.write_all(b"same side").await.unwrap();
        let mut received = [0; 9];
        tokio::time::timeout(Duration::from_secs(1), server.read_exact(&mut received))
            .await
            .unwrap()
            .unwrap();
        assert_eq!(&received, b"same side");
        drop(client);
        drop(server);
        drop(sender);
        task.await.unwrap();
    }
}
