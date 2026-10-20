//! CLI configuration for the network service. The federation file contains
//! public membership; the transport seed is read from a separate local file.
use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::process::ExitCode;
use std::time::Duration;

use ae_wire::{Identity, Limits, Peer};
use ed25519_dalek::{SigningKey, VerifyingKey};
use paralean_ae_service::{Endpoint, Puller};
use paralean_store::ae::{FederationConfig, FederationMember};
use paralean_store::*;
use serde_json::Value;

use crate::R;

pub fn keygen(path: &str) -> R<()> {
    use std::io::Write;
    #[cfg(unix)]
    use std::os::unix::fs::OpenOptionsExt;
    let seed: [u8; 32] = rand::random();
    let mut options = std::fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    options.mode(0o600);
    let mut file = options.open(path).map_err(|e| format!("{path}: {e}"))?;
    writeln!(file, "{}", hex::encode(seed)).map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())?;
    println!(
        "{}",
        hex::encode(SigningKey::from_bytes(&seed).verifying_key().to_bytes())
    );
    Ok(())
}

pub fn member(deployment: &str, public: &str) -> R<()> {
    let transport_public = bytes32(public)?;
    VerifyingKey::from_bytes(&transport_public).map_err(|e| e.to_string())?;
    let keys = crate::keyfile()?;
    let ring = keys.ring();
    let cfg = StoreConfig::from_env(deployment).map_err(|e| e.to_string())?;
    let writers: BTreeMap<_, _> = ring
        .writers
        .iter()
        .map(|(id, key)| (id.hex(), hex::encode(key)))
        .collect();
    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "replica": cfg.replica.hex(),
            "transport_public": hex::encode(transport_public),
            "authority": hex::encode(ring.authority),
            "writers": writers,
            "job_issuers": ring.job_issuers.iter().map(hex::encode).collect::<Vec<_>>(),
        }))
        .map_err(|e| e.to_string())?
    );
    Ok(())
}

struct Config {
    federation: FederationConfig,
    value: Value,
}

fn string<'a>(v: &'a Value, key: &str) -> R<&'a str> {
    v.get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing string field {key}"))
}

fn bytes32(value: &str) -> R<[u8; 32]> {
    hex::decode(value)
        .map_err(|e| e.to_string())?
        .try_into()
        .map_err(|_| "expected 32-byte hex key".into())
}

fn key_list(value: Option<&Value>) -> R<Vec<[u8; 32]>> {
    match value {
        None => Ok(Vec::new()),
        Some(Value::Array(values)) => values
            .iter()
            .map(|v| bytes32(v.as_str().ok_or("key must be hex string")?))
            .collect(),
        _ => Err("key list must be an array".into()),
    }
}

impl Config {
    fn read(path: &str) -> R<Self> {
        let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
        if bytes.len() > 1024 * 1024 {
            return Err("federation configuration exceeds 1 MiB".into());
        }
        let value: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        let deployment = string(&value, "deployment")?.to_owned();
        let member_values = value
            .get("members")
            .and_then(Value::as_object)
            .ok_or("members must be an object")?;
        let mut members = BTreeMap::new();
        for (name, member) in member_values {
            let mut writers = BTreeMap::new();
            for (id, public) in member
                .get("writers")
                .and_then(Value::as_object)
                .ok_or("writers must map IDs to public keys")?
            {
                writers.insert(
                    WorkspaceId::from_hex(id).ok_or("invalid writer ID")?,
                    bytes32(public.as_str().ok_or("writer key must be hex")?)?,
                );
            }
            members.insert(
                name.clone(),
                FederationMember {
                    replica: ReplicaId::from_hex(string(member, "replica")?)
                        .ok_or("invalid replica ID")?,
                    transport_public: bytes32(string(member, "transport_public")?)?,
                    authority: bytes32(string(member, "authority")?)?,
                    writers,
                    job_issuers: key_list(member.get("job_issuers"))?,
                },
            );
        }
        let mut target_homes = BTreeMap::new();
        if let Some(values) = value.get("target_homes") {
            for (name, home) in values.as_object().ok_or("target_homes must be an object")? {
                let parsed = Name::parse(name);
                if parsed.0.is_empty()
                    || target_homes
                        .insert(
                            parsed,
                            home.as_str().ok_or("home must be a deployment")?.to_owned(),
                        )
                        .is_some()
                {
                    return Err("empty or duplicate canonical target name".into());
                }
            }
        }
        let federation = FederationConfig {
            deployment,
            members,
            target_homes,
        };
        federation.validate().map_err(|e| e.to_string())?;
        Ok(Self { federation, value })
    }

    fn trust(&self, ring: &mut KeyRing) -> R<()> {
        for member in self.federation.members.values() {
            for (id, public) in &member.writers {
                if ring
                    .writers
                    .get(id)
                    .is_some_and(|existing| existing != public)
                {
                    return Err(
                        "federation writer public key conflicts with the local key ring".into(),
                    );
                }
                ring.writers.insert(*id, *public);
            }
            for public in std::iter::once(&member.authority).chain(&member.job_issuers) {
                if public != &ring.authority && !ring.job_issuers.contains(public) {
                    ring.job_issuers.push(*public);
                }
            }
        }
        for public in key_list(self.value.get("trusted_validators"))? {
            if !ring.validators.contains(&public) {
                ring.validators.push(public);
            }
        }
        Ok(())
    }

    fn identity(&self) -> R<Identity> {
        let path = string(&self.value, "signing_seed_file")?;
        let seed = std::fs::read_to_string(path)
            .map_err(|e| format!("cannot read transport seed file {path}: {e}"))?;
        let signing_key = SigningKey::from_bytes(&bytes32(seed.trim())?);
        let member = &self.federation.members[&self.federation.deployment];
        if signing_key.verifying_key().to_bytes() != member.transport_public {
            return Err("transport seed does not match this member's pinned public key".into());
        }
        Ok(Identity {
            deployment: self.federation.deployment.clone(),
            signing_key,
        })
    }

    fn peers(&self) -> R<Vec<Endpoint>> {
        let mut peers = Vec::new();
        if let Some(values) = self.value.get("peers") {
            for (name, address) in values
                .as_object()
                .ok_or("peers must map deployments to addresses")?
            {
                let member = self
                    .federation
                    .members
                    .get(name)
                    .ok_or("peer is absent from federation members")?;
                peers.push(Endpoint {
                    address: address
                        .as_str()
                        .ok_or("peer address must be a string")?
                        .parse()
                        .map_err(|e| format!("peer address: {e}"))?,
                    peer: Peer {
                        deployment: name.clone(),
                        verifying_key: VerifyingKey::from_bytes(&member.transport_public)
                            .map_err(|e| e.to_string())?,
                    },
                });
            }
        }
        Ok(peers)
    }

    fn open(&self) -> R<(Store, KeyFile)> {
        let keys = crate::keyfile()?;
        let mut ring = keys.ring();
        self.trust(&mut ring)?;
        let cfg = StoreConfig::from_env(&self.federation.deployment).map_err(|e| e.to_string())?;
        Ok((
            Store::open(&cfg, ring, Faults::none()).map_err(|e| e.to_string())?,
            keys,
        ))
    }
}

/// Ordinary publish/audit commands opt into the same public peer trust using
/// PARALEAN_FEDERATION_CONFIG. Transactional home checks read the pinned config
/// even if this environment variable is absent.
pub fn trust_from_env(ring: &mut KeyRing) -> R<()> {
    if let Ok(path) = std::env::var("PARALEAN_FEDERATION_CONFIG") {
        let config = Config::read(&path)?;
        let deployment = std::env::var("PARALEAN_DEPLOYMENT").unwrap_or_else(|_| "default".into());
        if config.federation.deployment != deployment {
            return Err("federation config and PARALEAN_DEPLOYMENT differ".into());
        }
        config.trust(ring)?;
    }
    Ok(())
}

async fn shutdown_signal() -> std::io::Result<()> {
    #[cfg(unix)]
    {
        let mut terminate =
            tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;
        tokio::select! {
            result = tokio::signal::ctrl_c() => result,
            _ = terminate.recv() => Ok(()),
        }
    }
    #[cfg(not(unix))]
    tokio::signal::ctrl_c().await
}

pub async fn run(command: &str, path: &str, once: bool) -> R<ExitCode> {
    let config = Config::read(path)?;
    let (store, keys) = config.open()?;
    if command == "federation-init" {
        let identity = store
            .ae_pin_config(&config.federation)
            .await
            .map_err(|e| e.to_string())?;
        println!(
            "pinned {} replica {} federation {} generation {}",
            identity.deployment,
            identity.replica.hex(),
            identity.config_digest.hex(),
            identity.generation.hex()
        );
        return Ok(ExitCode::SUCCESS);
    }
    let pinned = store
        .ae_federation()
        .await
        .map_err(|e| e.to_string())?
        .ok_or("run federation-init first")?;
    if pinned != config.federation {
        return Err("configuration differs from the pinned federation".into());
    }
    if command == "ae-status" {
        for peer in config.peers()? {
            let source = &peer.peer.deployment;
            let progress = store.ae_progress(source).await.map_err(|e| e.to_string())?;
            println!("{source}: {progress:?}");
            let pending = store
                .ae_pending_page(source, None, 64)
                .await
                .map_err(|e| e.to_string())?;
            for entry in pending.entries {
                println!(
                    "  event {} {:?}: {:?}",
                    hex::encode(entry.event.key),
                    entry.event.kind,
                    entry.state
                );
                if let Some(why) = entry.last_error {
                    println!("    last retry error: {why}");
                }
            }
            if pending.more {
                println!("  more pending entries exist");
            }
            let terminal = store
                .ae_terminal_page(source, None, 64)
                .await
                .map_err(|e| e.to_string())?;
            for entry in terminal.entries {
                println!(
                    "  archived event {} {:?}: {:?}",
                    hex::encode(entry.event.key),
                    entry.event.kind,
                    entry.state
                );
            }
            if terminal.more {
                println!("  more archived terminal diagnostics exist");
            }
        }
        return Ok(ExitCode::SUCCESS);
    }
    let own = config.identity()?;
    let peers = config.peers()?;
    let writer_name = config
        .value
        .get("sync_writer")
        .and_then(Value::as_str)
        .unwrap_or("w0");
    let writer = crate::writer(&store, &keys, writer_name)?;
    let limits = Limits::default();
    if once {
        let mut failed = false;
        for peer in peers {
            let mut puller = Puller::new(writer.clone(), own.clone(), peer, limits).await?;
            let stats = puller.round().await?;
            println!("{stats:?}");
            failed |= stats.terminal > 0;
        }
        return Ok(if failed {
            ExitCode::from(1)
        } else {
            ExitCode::SUCCESS
        });
    }
    let listen: SocketAddr = string(&config.value, "listen")?
        .parse()
        .map_err(|e| format!("listen address: {e}"))?;
    let interval = Duration::from_millis(
        config
            .value
            .get("interval_ms")
            .and_then(Value::as_u64)
            .unwrap_or(5000),
    );
    let listener = tokio::net::TcpListener::bind(listen)
        .await
        .map_err(|e| e.to_string())?;
    eprintln!(
        "anti-entropy {} listening on {}",
        own.deployment,
        listener.local_addr().map_err(|e| e.to_string())?
    );
    let (stop, stopped) = tokio::sync::watch::channel(false);
    let server = paralean_ae_service::serve_with_shutdown(
        listener,
        store,
        own.clone(),
        limits,
        stopped.clone(),
    );
    let scheduler = paralean_ae_service::schedule(writer, own, peers, interval, limits, stopped);
    tokio::pin!(server, scheduler);
    tokio::select! {
        result = &mut server => {
            let _ = stop.send(true);
            scheduler.await?;
            result?;
        }
        result = &mut scheduler => {
            let _ = stop.send(true);
            server.await?;
            result?;
        }
        signal = shutdown_signal() => {
            signal.map_err(|e| e.to_string())?;
            let _ = stop.send(true);
            scheduler.await?;
            server.await?;
        }
    }
    Ok(ExitCode::SUCCESS)
}
