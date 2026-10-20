//! Scheduled anti-entropy over authenticated TCP. Every peer needs only this
//! service's address and public key; remote FDB and S3 credentials are not used.
pub mod protocol;

use std::collections::HashMap;
use std::net::SocketAddr;
use std::sync::Arc;
use std::time::Duration;

use ae_wire::{Identity, Limits, Payload, Peer};
use ed25519_dalek::VerifyingKey;
use paralean_store::ae::{AeIdentity, AePending, PendingState};
use paralean_store::antientropy::Outcome;
use paralean_store::id::sha256;
use paralean_store::pce::Pce;
use paralean_store::{Id, Store, Writer};
use tokio::net::TcpListener;
use tokio::sync::watch;

use protocol::{Request, Response};

pub type Result<T> = std::result::Result<T, String>;
const PAGE_ITEMS: usize = 32;
// Leave room for the enclosing response tag.
const PAGE_BYTES: usize = ae_wire::MAX_METADATA - 1024;
const PENDING_ITEMS: usize = 64;
const PART_PAGES_PER_TURN: usize = 8;
const OBJECTS_PER_TURN: usize = 16;

#[derive(Clone, Debug)]
pub struct Endpoint {
    pub address: SocketAddr,
    pub peer: Peer,
}

/// A caller keeps one Puller per peer, so pending work rotates fairly even when
/// an early event has a permanently missing dependency.
pub struct Puller {
    writer: Writer,
    own: Identity,
    remote: Endpoint,
    limits: Limits,
    pending_after: Option<Vec<u8>>,
}

#[derive(Clone, Debug, Default)]
pub struct RoundStats {
    pub received_events: usize,
    pub received_parts: usize,
    pub fetched_objects: usize,
    pub applied: usize,
    pub present: usize,
    pub deferred: usize,
    /// Conflicts archived this turn, or at least one when an older diagnostic exists.
    pub terminal: usize,
}

async fn checked_identity(store: &Store, own: &Identity) -> Result<AeIdentity> {
    let i = store.ae_identity().await.map_err(|e| e.to_string())?;
    if i.deployment != own.deployment
        || i.transport_public != own.signing_key.verifying_key().to_bytes()
    {
        return Err("service signing identity does not match the pinned federation".into());
    }
    Ok(i)
}

async fn checked_peer(store: &Store, endpoint: &Endpoint) -> Result<()> {
    let config = store
        .ae_federation()
        .await
        .map_err(|e| e.to_string())?
        .ok_or("store has no pinned federation")?;
    let member = config
        .members
        .get(&endpoint.peer.deployment)
        .ok_or("peer is not a federation member")?;
    if member.transport_public != endpoint.peer.verifying_key.to_bytes() {
        return Err("peer transport key does not match the pinned federation".into());
    }
    if endpoint.peer.deployment == config.deployment {
        return Err("a deployment cannot pull from itself".into());
    }
    Ok(())
}

fn response(metadata: Response, object: Vec<u8>) -> Payload {
    Payload {
        metadata: metadata.to_pce(),
        object,
    }
}

async fn handle(store: &Store, own: &Identity, payload: Payload) -> Result<Payload> {
    if !payload.object.is_empty() {
        return Err("read-only requests cannot contain an object body".into());
    }
    let request = Request::from_pce(&payload.metadata).map_err(|e| e.to_string())?;
    let identity = checked_identity(store, own).await?;
    let generation = match &request {
        Request::Hello => return Ok(response(Response::Hello(identity), Vec::new())),
        Request::Changes { generation, .. }
        | Request::Materialize { generation, .. }
        | Request::Fetch { generation, .. } => generation,
    };
    if *generation != identity.generation {
        return Err("source generation changed; verified bootstrap is required".into());
    }
    match request {
        Request::Hello => unreachable!(),
        Request::Changes {
            after,
            max_items,
            max_bytes,
            ..
        } => {
            let page = store
                .ae_page(
                    after,
                    max_items.min(128) as usize,
                    max_bytes.min(PAGE_BYTES as u64) as usize,
                )
                .await
                .map_err(|e| e.to_string())?;
            Ok(response(Response::Changes(page), Vec::new()))
        }
        Request::Materialize {
            event,
            after_part,
            max_bytes,
            ..
        } => {
            let page = store
                .ae_materialize(
                    &event,
                    after_part,
                    max_bytes.min(PAGE_BYTES as u64) as usize,
                )
                .await
                .map_err(|e| e.to_string())?;
            Ok(response(Response::Materialize(page), Vec::new()))
        }
        Request::Fetch { kind, id, .. } => {
            match store.s3.get(kind, &id).await.map_err(|e| e.to_string())? {
                None => Ok(response(Response::Missing { kind, id }, Vec::new())),
                Some(bytes) => {
                    if bytes.len() > ae_wire::MAX_OBJECT {
                        return Err(format!(
                            "{} {} exceeds the 64 MiB object limit",
                            kind.name(),
                            id.hex()
                        ));
                    }
                    Ok(response(
                        Response::Object {
                            kind,
                            id,
                            length: bytes.len() as u64,
                        },
                        bytes,
                    ))
                }
            }
        }
    }
}

/// Serve until the caller cancels this future. The pinned membership supplies
/// every permitted transport public key. Requests never mutate store state.
pub async fn serve(
    listener: TcpListener,
    store: Store,
    own: Identity,
    limits: Limits,
) -> Result<()> {
    let (_stop, stopped) = watch::channel(false);
    serve_with_shutdown(listener, store, own, limits, stopped).await
}

/// Stop accepting requests, cancel and drain handlers before returning. This
/// lets a CLI stop its FoundationDB network thread after all service work ends.
pub async fn serve_with_shutdown(
    listener: TcpListener,
    store: Store,
    own: Identity,
    limits: Limits,
    shutdown: watch::Receiver<bool>,
) -> Result<()> {
    checked_identity(&store, &own).await?;
    let config = store
        .ae_federation()
        .await
        .map_err(|e| e.to_string())?
        .ok_or("store has no federation")?;
    let mut peers = HashMap::new();
    for (name, member) in config.members {
        peers.insert(
            name,
            VerifyingKey::from_bytes(&member.transport_public).map_err(|e| e.to_string())?,
        );
    }
    let own_for_handler = own.clone();
    ae_wire::serve_with_shutdown(listener, own, peers, limits, shutdown, move |_, payload| {
        let store = store.clone();
        let own = own_for_handler.clone();
        async move {
            match handle(&store, &own, payload).await {
                Ok(value) => value,
                Err(why) => response(
                    Response::Error(why.chars().take(4096).collect()),
                    Vec::new(),
                ),
            }
        }
    })
    .await
    .map_err(|e| e.to_string())
}

impl Puller {
    pub async fn new(
        writer: Writer,
        own: Identity,
        remote: Endpoint,
        limits: Limits,
    ) -> Result<Self> {
        checked_identity(&writer.store, &own).await?;
        checked_peer(&writer.store, &remote).await?;
        Ok(Self {
            writer,
            own,
            remote,
            limits,
            pending_after: None,
        })
    }

    async fn rpc(&self, request: Request) -> Result<(Response, Vec<u8>)> {
        let payload = ae_wire::exchange(
            self.remote.address,
            &self.own,
            &self.remote.peer,
            Payload {
                metadata: request.to_pce(),
                object: Vec::new(),
            },
            self.limits,
        )
        .await
        .map_err(|e| e.to_string())?;
        let decoded = Response::from_pce(&payload.metadata).map_err(|e| e.to_string())?;
        if let Response::Error(why) = decoded {
            return Err(format!("{}: {why}", self.remote.peer.deployment));
        }
        if !matches!(decoded, Response::Object { .. }) && !payload.object.is_empty() {
            return Err("unexpected object body on metadata response".into());
        }
        Ok((decoded, payload.object))
    }

    async fn hello(&self) -> Result<AeIdentity> {
        let own = checked_identity(&self.writer.store, &self.own).await?;
        let (Response::Hello(remote), _) = self.rpc(Request::Hello).await? else {
            return Err("expected Hello response".into());
        };
        let config = self
            .writer
            .store
            .ae_federation()
            .await
            .map_err(|e| e.to_string())?
            .ok_or("store federation disappeared")?;
        let member = config
            .members
            .get(&remote.deployment)
            .ok_or("Hello names an unknown member")?;
        if remote.deployment != self.remote.peer.deployment
            || remote.config_digest != own.config_digest
            || remote.transport_public != self.remote.peer.verifying_key.to_bytes()
            || remote.replica != member.replica
        {
            return Err("Hello deployment, replica, key or federation digest mismatch".into());
        }
        Ok(remote)
    }

    async fn save_pending(
        &self,
        generation: Id,
        cursor: Option<Vec<u8>>,
        p: &AePending,
        parts: &[(Vec<u8>, u64, paralean_store::ae::AePart)],
    ) -> Result<()> {
        self.writer
            .store
            .ae_save_progress(
                &self.remote.peer.deployment,
                generation,
                cursor,
                std::slice::from_ref(p),
                &[],
                parts,
            )
            .await
            .map_err(|e| e.to_string())
    }

    async fn replay(
        &self,
        mut p: AePending,
        cursor: Option<Vec<u8>>,
        stats: &mut RoundStats,
    ) -> Result<()> {
        if matches!(p.state, PendingState::Terminal(_)) {
            // Migrate terminal rows left by older deployments out of the active
            // queue so they cannot consume the receiver's pending quota.
            self.save_pending(p.generation, cursor, &p, &[]).await?;
            stats.terminal += 1;
            return Ok(());
        }
        let source = &self.remote.peer.deployment;
        if matches!(p.state, PendingState::Collecting) {
            for _ in 0..PART_PAGES_PER_TURN {
                let (Response::Materialize(page), _) = self
                    .rpc(Request::Materialize {
                        generation: p.generation,
                        event: p.event.clone(),
                        after_part: p.next_part,
                        max_bytes: PAGE_BYTES as u64,
                    })
                    .await?
                else {
                    return Err("expected materialized page".into());
                };
                if page.event_key != p.event.key || page.after_part != p.next_part {
                    return Err(
                        "materialized page does not bind the requested event and cursor".into(),
                    );
                }
                let mut previous = p.next_part;
                for (sequence, _) in &page.parts {
                    if previous.is_some_and(|n| *sequence <= n) {
                        return Err("materialized part sequence did not advance".into());
                    }
                    previous = Some(*sequence);
                }
                if page.next_part != previous || (!page.complete && page.parts.is_empty()) {
                    return Err("invalid materialized continuation".into());
                }
                p.next_part = page.next_part;
                if page.complete {
                    p.state = PendingState::Deferred("metadata collected".into());
                }
                stats.received_parts += page.parts.len();
                let parts: Vec<_> = page
                    .parts
                    .into_iter()
                    .map(|(seq, part)| (p.event.key.clone(), seq, part))
                    .collect();
                self.save_pending(p.generation, cursor.clone(), &p, &parts)
                    .await?;
                if page.complete {
                    break;
                }
            }
            if matches!(p.state, PendingState::Collecting) {
                return Ok(());
            }
        }
        // The store enumerates only references whose local S3 acknowledgement is
        // still missing. Already fetched objects survive a service restart.
        let missing = self
            .writer
            .store
            .ae_missing_objects(source, &p.event, p.objects_after.clone(), OBJECTS_PER_TURN)
            .await
            .map_err(|e| e.to_string())?;
        for (kind, id, length) in &missing.refs {
            let (reply, bytes) = self
                .rpc(Request::Fetch {
                    generation: p.generation,
                    kind: *kind,
                    id: *id,
                })
                .await?;
            match reply {
                Response::Object {
                    kind: got_kind,
                    id: got_id,
                    length: got_length,
                } if got_kind == *kind
                    && got_id == *id
                    && got_length == bytes.len() as u64
                    && got_length == *length =>
                {
                    if Id(sha256(&bytes)) != *id || kind.domain().strip(&bytes).is_err() {
                        return Err(format!(
                            "{source}: {} {} failed content verification",
                            kind.name(),
                            id.hex()
                        ));
                    }
                    self.writer
                        .store
                        .s3
                        .put(*kind, &bytes)
                        .await
                        .map_err(|e| e.to_string())?;
                    stats.fetched_objects += 1;
                }
                Response::Missing {
                    kind: got_kind,
                    id: got_id,
                } if got_kind == *kind && got_id == *id => {
                    p.state = PendingState::Deferred(format!(
                        "{source}: missing {} {}",
                        kind.name(),
                        id.hex()
                    ));
                    p.missing_count = missing.refs.len() as u64;
                    self.save_pending(p.generation, cursor, &p, &[]).await?;
                    stats.deferred += 1;
                    return Ok(());
                }
                _ => {
                    return Err(format!(
                        "{source}: object response identity or length mismatch"
                    ))
                }
            }
        }
        if missing.more {
            if missing.next == p.objects_after {
                return Err("object reference scan did not advance".into());
            }
            p.objects_after = missing.next;
            p.state = PendingState::Deferred("more objects to fetch".into());
            self.save_pending(p.generation, cursor, &p, &[]).await?;
            stats.deferred += 1;
            return Ok(());
        }
        p.objects_after = None;
        let outcome = self
            .writer
            .ae_import_staged(source, &p.event)
            .await
            .map_err(|e| e.to_string())?;
        match outcome {
            Outcome::Applied | Outcome::Present => {
                if outcome == Outcome::Applied {
                    stats.applied += 1;
                } else {
                    stats.present += 1;
                }
                self.writer
                    .store
                    .ae_save_progress(source, p.generation, cursor, &[], &[p.event.key], &[])
                    .await
                    .map_err(|e| e.to_string())?;
            }
            Outcome::Deferred(why) => {
                p.state = PendingState::Deferred(why);
                self.save_pending(p.generation, cursor, &p, &[]).await?;
                stats.deferred += 1;
            }
            other => {
                let why = format!("{other:?}");
                eprintln!(
                    "anti-entropy {source} event {}: {why}",
                    hex_key(&p.event.key)
                );
                p.state = PendingState::Terminal(why);
                self.save_pending(p.generation, cursor, &p, &[]).await?;
                stats.terminal += 1;
            }
        }
        Ok(())
    }

    /// One bounded scheduling turn. First durably queue descriptors, then replay
    /// one rotating pending page. A crash can replay an import, never skip it.
    pub async fn round(&mut self) -> Result<RoundStats> {
        let remote = self.hello().await?;
        let source = &self.remote.peer.deployment;
        let progress = self
            .writer
            .store
            .ae_progress(source)
            .await
            .map_err(|e| e.to_string())?;
        if progress
            .as_ref()
            .is_some_and(|p| p.generation != remote.generation)
        {
            return Err("peer generation changed; refusing to reset the incremental cursor".into());
        }
        let cursor = progress.and_then(|p| p.cursor);
        let (Response::Changes(page), _) = self
            .rpc(Request::Changes {
                generation: remote.generation,
                after: cursor.clone(),
                max_items: PAGE_ITEMS as u64,
                max_bytes: PAGE_BYTES as u64,
            })
            .await?
        else {
            return Err("expected Changes response".into());
        };
        if page.generation != remote.generation || page.events.len() > PAGE_ITEMS {
            return Err("change page generation or size mismatch".into());
        }
        let mut previous = cursor.clone();
        for event in &page.events {
            if previous.as_ref().is_some_and(|key| event.key <= *key) {
                return Err("change cursor did not advance".into());
            }
            previous = Some(event.key.clone());
        }
        if page.next != previous || (page.more && page.events.is_empty()) {
            return Err("invalid change page continuation".into());
        }
        let pending: Vec<_> = page
            .events
            .iter()
            .map(|event| AePending {
                source: source.clone(),
                generation: remote.generation,
                event: event.clone(),
                next_part: None,
                missing_count: 0,
                objects_after: None,
                last_error: None,
                state: PendingState::Collecting,
            })
            .collect();
        let queued = self
            .writer
            .store
            .ae_save_progress(
                source,
                remote.generation,
                page.next.clone(),
                &pending,
                &[],
                &[],
            )
            .await
            .map_err(|e| e.to_string());
        // A full pending quota must not prevent old entries from draining.
        // If enqueue failed, replay using only the previously committed cursor.
        let replay_cursor = if queued.is_ok() {
            page.next.clone()
        } else {
            cursor
        };
        let mut stats = RoundStats {
            received_events: if queued.is_ok() { pending.len() } else { 0 },
            ..Default::default()
        };
        let work = self
            .writer
            .store
            .ae_pending_page(source, self.pending_after.clone(), PENDING_ITEMS)
            .await
            .map_err(|e| e.to_string())?;
        self.pending_after = if work.more { work.next } else { None };
        for p in work.entries {
            // A failing object or metadata fetch must not starve unrelated events.
            let event = p.event.clone();
            if let Err(why) = self.replay(p, replay_cursor.clone(), &mut stats).await {
                eprintln!("anti-entropy {source}: retryable event failure: {why}");
                self.writer
                    .store
                    .ae_note_error(source, &event, &why)
                    .await
                    .map_err(|e| e.to_string())?;
                stats.deferred += 1;
            }
        }
        queued?;
        // A single bounded read preserves --once's nonzero conflict exit status
        // without replaying the (potentially large) diagnostic archive.
        if !self
            .writer
            .store
            .ae_terminal_page(source, None, 1)
            .await
            .map_err(|e| e.to_string())?
            .entries
            .is_empty()
        {
            stats.terminal = stats.terminal.max(1);
        }
        Ok(stats)
    }
}

fn hex_key(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Start one scheduled pull loop per peer, with an immediate first round and
/// bounded exponential retry backoff. Stop by sending true on `shutdown`.
pub async fn schedule(
    writer: Writer,
    own: Identity,
    peers: Vec<Endpoint>,
    interval: Duration,
    limits: Limits,
    mut shutdown: watch::Receiver<bool>,
) -> Result<()> {
    if interval < Duration::from_millis(100) || peers.len() > 32 {
        return Err("interval must be >=100ms and peer count <=32".into());
    }
    let mut unique = std::collections::BTreeSet::new();
    let mut pullers = Vec::new();
    for peer in peers {
        if !unique.insert(peer.peer.deployment.clone()) {
            return Err("duplicate scheduled peer".into());
        }
        pullers.push(Puller::new(writer.clone(), own.clone(), peer, limits).await?);
    }
    if pullers.is_empty() {
        while !*shutdown.borrow() {
            if shutdown.changed().await.is_err() {
                break;
            }
        }
        return Ok(());
    }
    // Limit simultaneous peers as well as each peer's requests.
    let semaphore = Arc::new(tokio::sync::Semaphore::new(2));
    let mut tasks = tokio::task::JoinSet::new();
    for mut puller in pullers {
        let mut stop = shutdown.clone();
        let semaphore = semaphore.clone();
        tasks.spawn(async move {
            let mut failures = 0u32;
            loop {
                if *stop.borrow() { break; }
                tokio::select! {
                    changed = stop.changed() => { if changed.is_err() || *stop.borrow() { break; } }
                    result = async {
                        let _permit = semaphore.acquire().await.map_err(|e| e.to_string())?;
                        puller.round().await
                    } => {
                        match result {
                            Ok(stats) => { failures = 0; eprintln!("anti-entropy {}: {stats:?}", puller.remote.peer.deployment); }
                            Err(why) => { failures = failures.saturating_add(1); eprintln!("anti-entropy {}: {why}", puller.remote.peer.deployment); }
                        }
                    }
                }
                let factor = 1u32 << failures.min(5);
                let base = interval.saturating_mul(factor).min(Duration::from_secs(60));
                let jitter = Duration::from_millis(rand::random::<u64>() % 251);
                tokio::select! {
                    _ = tokio::time::sleep(base + jitter) => {}
                    changed = stop.changed() => { if changed.is_err() || *stop.borrow() { break; } }
                }
            }
        });
    }
    while let Some(result) = tasks.join_next().await {
        if let Err(error) = result {
            tasks.abort_all();
            while tasks.join_next().await.is_some() {}
            return Err(error.to_string());
        }
    }
    Ok(())
}
