//! Real TCP anti-entropy between three logical deployments with distinct FDB roots,
//! S3 prefixes, replicas, writers and transport keys. Run via scripts/test.sh on an
//! owned P2 instance; all three can share that instance's physical FDB and Garage.

#[path = "../../store/tests/common/mod.rs"]
mod common;

use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ae_wire::{Identity, Limits, Peer};
use ed25519_dalek::SigningKey;
use paralean_ae_service::protocol::{Request, Response};
use paralean_ae_service::{schedule, serve, Endpoint, Puller};
use paralean_store::ae::{AeEvent, AeKind, AePart, AePending, PendingState};
use paralean_store::antientropy::Outcome;
use paralean_store::antientropy::published_set;
use paralean_store::pce::Pce;
use paralean_store::*;
use tokio::task::JoinHandle;

use common::{deployment, Env};

const SYNC: usize = 2;

struct Net {
    envs: Vec<Env>,
    identities: Vec<Identity>,
    addresses: Vec<SocketAddr>,
    tasks: Vec<JoinHandle<paralean_ae_service::Result<()>>>,
}

impl Net {
    async fn new(label: &str, target_home: Option<Name>) -> Self {
        let names: Vec<_> = (0..3)
            .map(|i| deployment(&format!("{label}-{i}")))
            .collect();
        let homes = target_home
            .map(|name| BTreeMap::from([(name, names[0].clone())]))
            .unwrap_or_default();
        let configs: Vec<_> = names
            .iter()
            .map(|name| StoreConfig::from_env(name).unwrap())
            .collect();
        let keys: Vec<_> = (0..3)
            .map(|i| {
                let mut keys = KeyFile::demo_prefixed(&format!("{label}/{i}/"), 3);
                keys.add_validator("v0", &Signer::derive(&format!("{label}/{i}/validator")));
                keys
            })
            .collect();
        let identities: Vec<_> = names
            .iter()
            .enumerate()
            .map(|(i, name)| Identity {
                deployment: name.clone(),
                signing_key: SigningKey::from_bytes(&[i as u8 + 1; 32]),
            })
            .collect();
        let members: BTreeMap<_, _> = (0..3)
            .map(|i| {
                let ring = keys[i].ring();
                (
                    names[i].clone(),
                    FederationMember {
                        replica: configs[i].replica,
                        transport_public: identities[i].signing_key.verifying_key().to_bytes(),
                        authority: ring.authority,
                        writers: ring.writers,
                        job_issuers: ring.job_issuers,
                    },
                )
            })
            .collect();
        let mut envs = Vec::new();
        for i in 0..3 {
            let mut trusted = KeyRing::default();
            for (j, keys) in keys.iter().enumerate() {
                if i != j {
                    trusted.trust(&keys.ring());
                }
            }
            let env = Env::open_keys(
                configs[i].clone(),
                keys[i].clone(),
                3,
                Faults::none(),
                Some(&trusted),
            );
            env.store
                .ae_pin_config(&FederationConfig {
                    deployment: names[i].clone(),
                    members: members.clone(),
                    target_homes: homes.clone(),
                })
                .await
                .unwrap();
            envs.push(env);
        }
        let mut addresses = Vec::new();
        let mut tasks = Vec::new();
        for i in 0..3 {
            let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
            addresses.push(listener.local_addr().unwrap());
            tasks.push(tokio::spawn(serve(
                listener,
                envs[i].store.clone(),
                identities[i].clone(),
                Limits::default(),
            )));
        }
        Self {
            envs,
            identities,
            addresses,
            tasks,
        }
    }

    async fn puller(&self, destination: usize, source: usize) -> Puller {
        Puller::new(
            self.envs[destination].w[SYNC].clone(),
            self.identities[destination].clone(),
            Endpoint {
                address: self.addresses[source],
                peer: Peer {
                    deployment: self.identities[source].deployment.clone(),
                    verifying_key: self.identities[source].signing_key.verifying_key(),
                },
            },
            Limits {
                timeout: Duration::from_secs(15),
                max_connections: 2,
            },
        )
        .await
        .unwrap()
    }
}

impl Drop for Net {
    fn drop(&mut self) {
        for task in &self.tasks {
            task.abort();
        }
    }
}

async fn until_group(puller: &mut Puller, destination: &Env, group: Id) {
    for _ in 0..20 {
        puller.round().await.unwrap();
        if published_set(&destination.store)
            .await
            .unwrap()
            .groups
            .contains_key(&group)
        {
            return;
        }
    }
    panic!("group {group:?} did not arrive over the network");
}

#[tokio::test]
async fn three_deployment_group_and_tombstone_relay_preserves_origin_evidence() {
    let net = Net::new("net-relay", None).await;
    let a = &net.envs[0];
    let group = a.plain_package(0, "Net.relay", "relay");
    a.w[0].publish(&group).await.unwrap();
    let tombstone = fixture::tombstone_of(&group.marker, 2);
    a.w[0].tombstone(&tombstone).await.unwrap();

    let mut b_from_a = net.puller(1, 0).await;
    let mut c_from_b = net.puller(2, 1).await;
    for _ in 0..20 {
        b_from_a.round().await.unwrap();
        c_from_b.round().await.unwrap();
        if published_set(&net.envs[2].store)
            .await
            .unwrap()
            .tombstones
            .contains(&tombstone.id())
        {
            break;
        }
    }
    let pa = published_set(&a.store).await.unwrap();
    let pb = published_set(&net.envs[1].store).await.unwrap();
    let pc = published_set(&net.envs[2].store).await.unwrap();
    assert_eq!(pa, pb);
    assert_eq!(pa, pc);
    let c = &net.envs[2];
    let original_cert = a
        .store
        .certs(&group.group.id())
        .await
        .unwrap()
        .into_iter()
        .find(|cert| cert.body.writer == a.w[0].id)
        .unwrap();
    let original = c
        .store
        .meta
        .keys
        .xcertv("cert", &group.group.id(), &original_cert.id());
    assert_eq!(
        c.store.meta.get(original).await.unwrap(),
        Some(original_cert.to_bytes()),
        "C must retain A's original publication certificate"
    );
    let original_tomb_cert = a
        .store
        .tcerts(&tombstone.id())
        .await
        .unwrap()
        .into_iter()
        .find(|cert| cert.body.writer == a.w[0].id)
        .unwrap();
    let tomb_original =
        c.store
            .meta
            .keys
            .xcertv("tcert", &tombstone.id(), &original_tomb_cert.id());
    assert_eq!(
        c.store.meta.get(tomb_original).await.unwrap(),
        Some(original_tomb_cert.to_bytes()),
        "C must retain A's original tombstone certificate"
    );
    for env in &net.envs {
        env.audit_ok().await;
    }

    // A fresh Puller simulates a restarted service. C's durable cursor is already
    // complete, and repeated A→B→C rounds do not create new change events.
    let before = c
        .store
        .ae_page(None, 1024, ae_wire::MAX_METADATA)
        .await
        .unwrap()
        .events
        .len();
    let mut restarted = net.puller(2, 1).await;
    for _ in 0..3 {
        b_from_a.round().await.unwrap();
        restarted.round().await.unwrap();
    }
    let after = c
        .store
        .ae_page(None, 1024, ae_wire::MAX_METADATA)
        .await
        .unwrap()
        .events
        .len();
    assert_eq!(before, after, "evidence replay must not echo indefinitely");
}

#[tokio::test]
async fn target_home_publication_reaches_third_deployment_without_local_target_key() {
    let target = Name::parse("Target.network");
    let net = Net::new("net-home", Some(target.clone())).await;
    let a = &net.envs[0];
    a.ctl
        .reassign(&target, a.w[0].id, b"assign network home")
        .await
        .unwrap();
    let binding = a.w[0].prepare_target(&target).await.unwrap();
    let parents = binding.head.into_iter().collect();
    let group = fixture::package_by(
        &a.authority(),
        "target",
        a.w[0].id,
        &a.validator,
        &target,
        parents,
        Some(binding),
        1,
    );
    a.w[0].publish(&group).await.unwrap();

    let mut b_from_a = net.puller(1, 0).await;
    let mut c_from_b = net.puller(2, 1).await;
    until_group(&mut b_from_a, &net.envs[1], group.group.id()).await;
    until_group(&mut c_from_b, &net.envs[2], group.group.id()).await;
    let c = &net.envs[2];
    assert!(
        c.store.target(&target).await.unwrap().is_none(),
        "receiver does not create a local target record"
    );
    assert_eq!(
        published_set(&c.store)
            .await
            .unwrap()
            .groups
            .get(&group.group.id()),
        published_set(&a.store)
            .await
            .unwrap()
            .groups
            .get(&group.group.id())
    );
    let original_cert = a
        .store
        .certs(&group.group.id())
        .await
        .unwrap()
        .into_iter()
        .find(|cert| cert.body.writer == a.w[0].id)
        .unwrap();
    let original = c
        .store
        .meta
        .keys
        .xcertv("cert", &group.group.id(), &original_cert.id());
    assert_eq!(
        c.store.meta.get(original).await.unwrap(),
        Some(original_cert.to_bytes()),
        "third deployment must retain the home publisher's certificate"
    );
    for env in &net.envs {
        env.audit_ok().await;
    }
}

#[tokio::test]
async fn pinned_target_home_rejects_a_foreign_write_on_an_old_store_handle() {
    let target = Name::parse("Target.foreign-network");
    let net = Net::new("net-wrong-home", Some(target.clone())).await;
    let foreign = &net.envs[1];

    // Net opened all Store handles before pinning the federation. The metadata
    // write transaction must still read the pinned home, rather than relying on
    // a Store field captured at construction time.
    let err = foreign
        .ctl
        .reassign(&target, foreign.w[0].id, b"foreign assignment")
        .await
        .unwrap_err();
    assert!(
        err.to_string().contains("home") || err.to_string().contains("foreign"),
        "unexpected wrong-home diagnostic: {err}"
    );
    assert!(foreign.store.target(&target).await.unwrap().is_none());
}

#[tokio::test]
async fn server_rejects_a_stale_generation_before_serving_changes() {
    let net = Net::new("net-stale-generation", None).await;
    let current = net.envs[0].store.ae_identity().await.unwrap().generation;
    let stale = Id([0; 32]);
    assert_ne!(current, stale);
    let response = ae_wire::exchange(
        net.addresses[0],
        &net.identities[1],
        &Peer {
            deployment: net.identities[0].deployment.clone(),
            verifying_key: net.identities[0].signing_key.verifying_key(),
        },
        ae_wire::Payload {
            metadata: Request::Changes {
                generation: stale,
                after: None,
                max_items: 1,
                max_bytes: 1024,
            }
            .to_pce(),
            object: Vec::new(),
        },
        Limits::default(),
    )
    .await
    .unwrap();
    let Response::Error(reason) = Response::from_pce(&response.metadata).unwrap() else {
        panic!("stale generation must be rejected");
    };
    assert!(reason.contains("generation"), "unexpected error: {reason}");
    assert!(response.object.is_empty());
}

#[tokio::test]
async fn pinned_federation_rejects_changed_roster_and_wrong_peer_key() {
    let net = Net::new("net-config-fence", None).await;
    let b = &net.envs[1];
    let mut changed = b.store.ae_federation().await.unwrap().unwrap();
    changed.target_homes.insert(
        Name::parse("Target.after-pin"),
        net.identities[0].deployment.clone(),
    );
    let err = b.store.ae_pin_config(&changed).await.unwrap_err();
    assert!(
        err.to_string().contains("pinned"),
        "unexpected pin error: {err}"
    );

    let wrong = Endpoint {
        address: net.addresses[0],
        peer: Peer {
            deployment: net.identities[0].deployment.clone(),
            verifying_key: net.identities[2].signing_key.verifying_key(),
        },
    };
    let err = Puller::new(
        b.w[SYNC].clone(),
        net.identities[1].clone(),
        wrong,
        Limits::default(),
    )
    .await
    .err()
    .expect("wrong pinned peer key must fail before network use");
    assert!(
        err.contains("pinned federation"),
        "unexpected peer error: {err}"
    );
}

#[tokio::test]
async fn scheduled_pull_observes_publication_after_service_start_and_stops_cleanly() {
    let net = Net::new("net-scheduled", None).await;
    let (stop_tx, stop_rx) = tokio::sync::watch::channel(false);
    let task = tokio::spawn(schedule(
        net.envs[1].w[SYNC].clone(),
        net.identities[1].clone(),
        vec![Endpoint {
            address: net.addresses[0],
            peer: Peer {
                deployment: net.identities[0].deployment.clone(),
                verifying_key: net.identities[0].signing_key.verifying_key(),
            },
        }],
        Duration::from_millis(100),
        Limits::default(),
        stop_rx,
    ));
    tokio::time::sleep(Duration::from_millis(200)).await;
    let package = net.envs[0].plain_package(0, "Net.scheduled", "scheduled");
    net.envs[0].w[0].publish(&package).await.unwrap();
    tokio::time::timeout(Duration::from_secs(30), async {
        loop {
            if published_set(&net.envs[1].store)
                .await
                .unwrap()
                .groups
                .contains_key(&package.group.id())
            {
                break;
            }
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    })
    .await
    .expect("scheduled pull did not observe a new publication");
    stop_tx.send(true).unwrap();
    tokio::time::timeout(Duration::from_secs(5), task)
        .await
        .expect("scheduled pull did not stop")
        .unwrap()
        .unwrap();
    net.envs[1].audit_ok().await;
}

#[tokio::test]
async fn receipt_only_marker_variants_converge_and_keep_both_certificates() {
    let net = Net::new("net-marker-variants", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let pa = a.plain_package(0, "Net.variant", "variant");
    let mut pb = pa.clone();
    pb.job = SignedJob::sign(pb.job.body.clone(), &b.authority());
    let mut receipt_body = pb.receipt.body.clone();
    receipt_body.request = Some(pb.job.id().0.to_vec());
    receipt_body.validator_key = b.validator.public();
    receipt_body.axioms = vec![Name::parse("Classical.choice")];
    pb.receipt = Receipt::sign(receipt_body, &b.validator);
    pb.marker.receipt = pb.receipt.id();
    assert_ne!(pa.marker.id(), pb.marker.id());
    assert_eq!(pa.marker.group, pb.marker.group);
    assert_eq!(pa.marker.revisions, pb.marker.revisions);

    a.w[0].publish(&pa).await.unwrap();
    b.w[0].publish(&pb).await.unwrap();
    let a_cert = a
        .store
        .certs(&pa.group.id())
        .await
        .unwrap()
        .into_iter()
        .find(|c| c.body.writer == a.w[0].id)
        .unwrap();
    let b_cert = b
        .store
        .certs(&pb.group.id())
        .await
        .unwrap()
        .into_iter()
        .find(|c| c.body.writer == b.w[0].id)
        .unwrap();

    let mut a_from_b = net.puller(0, 1).await;
    let mut b_from_a = net.puller(1, 0).await;
    let mut c_from_a = net.puller(2, 0).await;
    let mut c_from_b = net.puller(2, 1).await;
    for _ in 0..20 {
        a_from_b.round().await.unwrap();
        b_from_a.round().await.unwrap();
        c_from_a.round().await.unwrap();
        c_from_b.round().await.unwrap();
    }
    let sets = [
        published_set(&a.store).await.unwrap(),
        published_set(&b.store).await.unwrap(),
        published_set(&net.envs[2].store).await.unwrap(),
    ];
    assert_eq!(sets[0], sets[1]);
    assert_eq!(sets[1], sets[2]);
    let canonical = sets[0].groups[&pa.group.id()];
    assert!(canonical == pa.marker.id() || canonical == pb.marker.id());
    for (i, env) in net.envs.iter().enumerate() {
        for (j, identity) in net.identities.iter().enumerate() {
            if i == j {
                continue;
            }
            let pending = env
                .store
                .ae_pending_page(&identity.deployment, None, 100)
                .await
                .unwrap();
            assert!(
                pending.entries.iter().all(|p| !matches!(p.state, paralean_store::ae::PendingState::Terminal(_))),
                "valid marker variants must not leave terminal replay errors at {i} from {j}: {pending:?}"
            );
        }
        let local = env.store.certs(&pa.group.id()).await.unwrap();
        for cert in [&a_cert, &b_cert] {
            let foreign = env
                .store
                .meta
                .get(
                    env.store
                        .meta
                        .keys
                        .xcertv("cert", &pa.group.id(), &cert.id()),
                )
                .await
                .unwrap();
            assert!(
                foreign == Some(cert.to_bytes()) || local.iter().any(|c| c == cert),
                "both immutable origin certificates must survive convergence"
            );
        }
        env.audit_ok().await;
    }
    // A restarted puller must see the already chosen canonical marker.
    let mut restarted = net.puller(2, 1).await;
    restarted.round().await.unwrap();
    assert_eq!(
        published_set(&net.envs[2].store).await.unwrap().groups[&pa.group.id()],
        canonical
    );

    // Revoking only A's validator makes its certificate-backed marker
    // ineligible. The intact B receipt and marker remain discoverable.
    a.revoke(a.validator.public()).await;
    assert_eq!(
        a.store.marker(&pa.group.id()).await.unwrap().unwrap().0,
        pb.marker.id()
    );
    assert_eq!(
        published_set(&a.store).await.unwrap().groups[&pa.group.id()],
        pb.marker.id()
    );
    a.audit_ok().await;
}

#[tokio::test]
async fn lower_receipt_variant_does_not_redirect_base_certification_or_tombstone_guards() {
    let net = Net::new("net-base-marker-guards", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let c = &net.envs[2];
    // Select an immutable A base whose compatible B receipt-only variant sorts
    // lower. This forces Store::marker to differ from the base guarded by T2/T8/T10.
    let (pa, pb) = (0..64)
        .find_map(|attempt| {
            let pa = a.plain_package(0, "Net.baseMarker", &format!("base-marker-{attempt}"));
            let mut pb = pa.clone();
            pb.job = SignedJob::sign(pb.job.body.clone(), &b.authority());
            let mut receipt = pb.receipt.body.clone();
            receipt.request = Some(pb.job.id().0.to_vec());
            receipt.validator_key = b.validator.public();
            receipt.axioms = vec![Name::parse("Classical.choice")];
            pb.receipt = Receipt::sign(receipt, &b.validator);
            pb.marker.receipt = pb.receipt.id();
            (pb.marker.id() < pa.marker.id()).then_some((pa, pb))
        })
        .expect("64 deterministic receipt candidates should include a lower variant");
    assert_eq!(pa.marker.group, pb.marker.group);
    assert_eq!(pa.marker.revisions, pb.marker.revisions);
    assert!(pb.marker.id() < pa.marker.id());

    a.w[0].publish(&pa).await.unwrap();
    b.w[0].publish(&pb).await.unwrap();
    let mut c_from_a = net.puller(2, 0).await;
    until_group(&mut c_from_a, c, pa.group.id()).await;
    assert_eq!(
        c.store
            .marker_base(&pa.group.id())
            .await
            .unwrap()
            .unwrap()
            .0,
        pa.marker.id(),
        "C must first install A's high marker as its immutable base"
    );
    let mut a_from_b = net.puller(0, 1).await;
    let mut c_from_b = net.puller(2, 1).await;
    for _ in 0..20 {
        a_from_b.round().await.unwrap();
        c_from_b.round().await.unwrap();
        if a.store.marker(&pa.group.id()).await.unwrap().unwrap().0 == pb.marker.id()
            && c.store.marker(&pa.group.id()).await.unwrap().unwrap().0 == pb.marker.id()
        {
            break;
        }
    }
    for receiver in [a, c] {
        assert_eq!(
            receiver
                .store
                .marker_base(&pa.group.id())
                .await
                .unwrap()
                .unwrap()
                .0,
            pa.marker.id()
        );
        assert_eq!(
            receiver
                .store
                .marker(&pa.group.id())
                .await
                .unwrap()
                .unwrap()
                .0,
            pb.marker.id()
        );
    }

    assert!(a.w[1].certify(&pa.group.id()).await.unwrap());
    let base_cert = a
        .store
        .certs(&pa.group.id())
        .await
        .unwrap()
        .into_iter()
        .find(|cert| cert.body.writer == a.w[1].id)
        .expect("second A writer certified the base group");
    assert_eq!(base_cert.body.marker, pa.marker.id());
    assert_eq!(
        a.store.marker(&pa.group.id()).await.unwrap().unwrap().0,
        pb.marker.id()
    );

    let tombstone = fixture::tombstone_of(&pa.marker, 2);
    assert!(a.w[0].tombstone(&tombstone).await.unwrap());
    for _ in 0..20 {
        c_from_a.round().await.unwrap();
        if published_set(&c.store)
            .await
            .unwrap()
            .tombstones
            .contains(&tombstone.id())
        {
            break;
        }
    }
    assert!(published_set(&c.store)
        .await
        .unwrap()
        .tombstones
        .contains(&tombstone.id()));
    assert_eq!(
        c.store
            .marker_base(&pa.group.id())
            .await
            .unwrap()
            .unwrap()
            .0,
        pa.marker.id()
    );
    assert_eq!(
        c.store.marker(&pa.group.id()).await.unwrap().unwrap().0,
        pb.marker.id()
    );
    let source_tomb_cert = a
        .store
        .tcerts(&tombstone.id())
        .await
        .unwrap()
        .into_iter()
        .find(|cert| cert.body.writer == a.w[0].id)
        .unwrap();
    assert_eq!(
        c.store
            .meta
            .get(
                c.store
                    .meta
                    .keys
                    .xcertv("tcert", &tombstone.id(), &source_tomb_cert.id())
            )
            .await
            .unwrap(),
        Some(source_tomb_cert.to_bytes()),
        "relay must retain A's original tombstone certificate"
    );
    assert!(
        c.store
            .ae_terminal_page(&net.identities[0].deployment, None, 16)
            .await
            .unwrap()
            .entries
            .is_empty(),
        "T10 must not reject a tombstone because canonical differs from base"
    );
    a.audit_ok().await;
    c.audit_ok().await;
}

#[tokio::test]
async fn incompatible_marker_layout_reports_exact_ids_and_field_without_overwrite() {
    let net = Net::new("net-marker-layout", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let pa = a.plain_package(0, "Net.layoutConflict", "layout-conflict");
    let mut pb = pa.clone();
    pb.job = SignedJob::sign(pb.job.body.clone(), &b.authority());
    let mut receipt_body = pb.receipt.body.clone();
    receipt_body.request = Some(pb.job.id().0.to_vec());
    receipt_body.validator_key = b.validator.public();
    pb.receipt = Receipt::sign(receipt_body, &b.validator);
    pb.marker.receipt = pb.receipt.id();
    pb.marker.lamport = 2;
    pb.marker.author = AgentId::derive("different layout author");
    pb.marker.root_path = vec![(pb.group.id(), 2, pb.marker.author)];
    a.w[0].publish(&pa).await.unwrap();
    b.w[0].publish(&pb).await.unwrap();

    for (destination, source, expected_local, expected_remote) in [
        (0, 1, pa.marker.id(), pb.marker.id()),
        (1, 0, pb.marker.id(), pa.marker.id()),
    ] {
        let mut puller = net.puller(destination, source).await;
        for _ in 0..20 {
            puller.round().await.unwrap();
        }
        let repeated = puller.round().await.unwrap();
        assert!(
            repeated.terminal > 0,
            "an existing terminal conflict must remain visible to --once status"
        );
        let receiver = &net.envs[destination];
        let pending = receiver
            .store
            .ae_pending_page(&net.identities[source].deployment, None, 100)
            .await
            .unwrap();
        assert!(
            pending
                .entries
                .iter()
                .all(|p| !matches!(p.state, PendingState::Terminal(_))),
            "terminal diagnostics must leave the active replay queue: {pending:?}"
        );
        assert_eq!(
            receiver
                .store
                .ae_active_pending_count(&net.identities[source].deployment)
                .await
                .unwrap(),
            0,
            "archived conflict must release the active pending quota"
        );
        let terminal = receiver
            .store
            .ae_terminal_page(&net.identities[source].deployment, None, 100)
            .await
            .unwrap();
        let conflict = terminal
            .entries
            .iter()
            .find(|p| {
                matches!(&p.state, paralean_store::ae::PendingState::Terminal(reason)
                if reason.contains("MarkerConflict")
                    && reason.contains(&pa.group.id().hex())
                    && reason.contains(&expected_local.hex())
                    && reason.contains(&expected_remote.hex())
                    && reason.contains("lamport")
                    && reason.contains("root_path"))
            })
            .unwrap_or_else(|| {
                panic!("incompatible layout must have an exact archived diagnostic: {terminal:?}")
            });
        let staged_parts = receiver
            .store
            .meta
            .scan(
                &receiver
                    .store
                    .meta
                    .keys
                    .ae_parts(&net.identities[source].deployment, &conflict.event.key),
                16,
                |_| None,
            )
            .await
            .unwrap();
        assert!(
            staged_parts.is_empty(),
            "archived conflict must release staged event fragments"
        );
        assert_eq!(
            published_set(&receiver.store).await.unwrap().groups[&pa.group.id()],
            expected_local,
            "a different layout cannot replace the published marker"
        );
        receiver.audit_ok().await;

        // A persistent conflict must not consume queue quota or hold the
        // cursor before a later, unrelated publication from the same source.
        let later = net.envs[source].plain_package(
            0,
            if source == 0 {
                "Net.layoutLaterA"
            } else {
                "Net.layoutLaterB"
            },
            if source == 0 {
                "after-layout-conflict-A"
            } else {
                "after-layout-conflict-B"
            },
        );
        net.envs[source].w[0].publish(&later).await.unwrap();
        until_group(&mut puller, receiver, later.group.id()).await;
        assert!(puller.round().await.unwrap().terminal > 0);
    }
}

#[tokio::test]
async fn simultaneous_receipt_variants_retry_stale_t9_precheck_and_converge() {
    let net = Net::new("net-variant-race", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let c = &net.envs[2];
    let pa = a.plain_package(0, "Net.variantRace", "variant-race");
    let mut pb = pa.clone();
    pb.job = SignedJob::sign(pb.job.body.clone(), &b.authority());
    let mut receipt_body = pb.receipt.body.clone();
    receipt_body.request = Some(pb.job.id().0.to_vec());
    receipt_body.validator_key = b.validator.public();
    receipt_body.axioms = vec![Name::parse("Classical.choice")];
    pb.receipt = Receipt::sign(receipt_body, &b.validator);
    pb.marker.receipt = pb.receipt.id();
    a.w[0].publish(&pa).await.unwrap();
    b.w[0].publish(&pb).await.unwrap();

    // Both pulls use C's initially empty marker slot. A stale preliminary
    // no-base observation in one transaction must retry after the other T9
    // commits, then accept the receipt-only compatible variant.
    let mut from_a = net.puller(2, 0).await;
    let mut from_b = net.puller(2, 1).await;
    for _ in 0..20 {
        let (left, right) = tokio::join!(from_a.round(), from_b.round());
        left.unwrap();
        right.unwrap();
    }
    let canonical = published_set(&c.store).await.unwrap().groups[&pa.group.id()];
    assert!(canonical == pa.marker.id() || canonical == pb.marker.id());
    for source in [&net.identities[0].deployment, &net.identities[1].deployment] {
        let pending = c.store.ae_pending_page(source, None, 100).await.unwrap();
        assert!(
            pending
                .entries
                .iter()
                .all(|p| !matches!(p.state, paralean_store::ae::PendingState::Terminal(_))),
            "stale T9 precheck should retry, not leave a terminal variant: {pending:?}"
        );
    }
    c.audit_ok().await;
}

#[tokio::test]
async fn catalogue_relay_retains_the_original_source_and_commit_proof() {
    let net = Net::new("net-catalogue", None).await;
    let a = &net.envs[0];
    let token = a
        .ctl
        .rotate(a.w[0].id, b"catalogue source token")
        .await
        .unwrap();
    let checkpoint = common::one_snapshot(a, 0, "network-catalogue", token, None).await;
    let id = a.w[0].commit_checkpoint(&checkpoint).await.unwrap();
    let source_record = a.store.record(&id).await.unwrap().unwrap();
    let source_cert = a
        .store
        .valid_rcert(&id, &source_record.body)
        .await
        .unwrap()
        .unwrap();

    let mut b_from_a = net.puller(1, 0).await;
    let mut c_from_b = net.puller(2, 1).await;
    let origin = &net.identities[0].deployment;
    for _ in 0..30 {
        b_from_a.round().await.unwrap();
        c_from_b.round().await.unwrap();
        if net.envs[2]
            .store
            .meta
            .get(net.envs[2].store.meta.keys.xrcert(origin, &id))
            .await
            .unwrap()
            .is_some()
        {
            break;
        }
    }
    for receiver in [&net.envs[1], &net.envs[2]] {
        assert_eq!(
            receiver
                .store
                .meta
                .get(receiver.store.meta.keys.xcatalog(origin, &id))
                .await
                .unwrap(),
            Some(source_record.to_bytes()),
            "record must remain qualified by A's deployment"
        );
        assert_eq!(
            receiver
                .store
                .meta
                .get(receiver.store.meta.keys.xrcert(origin, &id))
                .await
                .unwrap(),
            Some(source_cert.to_bytes()),
            "commit certificate must retain A's exact signature"
        );
        assert!(receiver.store.record(&id).await.unwrap().is_none());
        receiver.audit_ok().await;
    }
    a.audit_ok().await;
}

#[tokio::test]
async fn malformed_source_receipt_cannot_be_imported_and_repair_allows_retry() {
    let net = Net::new("net-invalid-receipt", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let package = a.plain_package(0, "Net.invalidReceipt", "invalid-receipt");
    a.w[0].publish(&package).await.unwrap();
    let receipt_key = a.store.meta.keys.receipt(&package.receipt.id());
    let original = a
        .store
        .meta
        .get(receipt_key.clone())
        .await
        .unwrap()
        .unwrap();
    a.store
        .meta
        .raw_set(receipt_key.clone(), b"invalid signed receipt".to_vec())
        .await
        .unwrap();

    let mut puller = net.puller(1, 0).await;
    let mut rejected = false;
    for _ in 0..12 {
        puller.round().await.unwrap();
        let pending = b
            .store
            .ae_pending_page(&net.identities[0].deployment, None, 100)
            .await
            .unwrap();
        if pending.entries.iter().any(|p| p.last_error.is_some()) {
            rejected = true;
            break;
        }
    }
    assert!(rejected, "malformed signed receipt must stop import");
    assert!(!published_set(&b.store)
        .await
        .unwrap()
        .groups
        .contains_key(&package.group.id()));

    a.store.meta.raw_set(receipt_key, original).await.unwrap();
    let mut restarted = net.puller(1, 0).await;
    until_group(&mut restarted, b, package.group.id()).await;
    a.audit_ok().await;
    b.audit_ok().await;
}

#[tokio::test]
async fn bounded_pages_and_restart_replay_deferred_missing_object() {
    let net = Net::new("net-cursor", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let missing = a.plain_package(0, "Net.missing", "missing");
    a.w[0].publish(&missing).await.unwrap();
    let later = a.plain_package(1, "Net.later", "later");
    a.w[1].publish(&later).await.unwrap();

    // The network Changes RPC pages by commit order, even when a limit stops
    // partway through a transaction's several evidence events.
    let generation = a.store.ae_identity().await.unwrap().generation;
    let mut after = None;
    let mut seen = Vec::new();
    for _ in 0..20 {
        let request = Request::Changes {
            generation,
            after: after.clone(),
            max_items: 2,
            max_bytes: 128 * 1024,
        };
        let response = ae_wire::exchange(
            net.addresses[0],
            &net.identities[1],
            &Peer {
                deployment: net.identities[0].deployment.clone(),
                verifying_key: net.identities[0].signing_key.verifying_key(),
            },
            ae_wire::Payload {
                metadata: request.to_pce(),
                object: Vec::new(),
            },
            Limits::default(),
        )
        .await
        .unwrap();
        let Response::Changes(page) = Response::from_pce(&response.metadata).unwrap() else {
            panic!("expected Changes page");
        };
        assert!(response.object.is_empty());
        assert!(page.events.len() <= 2);
        assert_eq!(page.generation, generation);
        for event in &page.events {
            assert!(seen
                .last()
                .is_none_or(|previous: &Vec<u8>| previous < &event.key));
            seen.push(event.key.clone());
        }
        assert_eq!(page.next, seen.last().cloned());
        after = page.next;
        if !page.more {
            break;
        }
    }
    assert!(
        seen.len() >= 2,
        "source should expose more than one change descriptor"
    );

    // A missing source object leaves its event durable and pending, while the
    // independent later group still advances. A new Puller must replay it.
    a.store
        .s3
        .corrupt_at_rest(Kind::Group, &missing.group.id(), b"rot")
        .await
        .unwrap();
    let mut puller = net.puller(1, 0).await;
    for _ in 0..10 {
        puller.round().await.unwrap();
    }
    let published = published_set(&b.store).await.unwrap();
    assert!(!published.groups.contains_key(&missing.group.id()));
    assert!(
        published.groups.contains_key(&later.group.id()),
        "deferred item must not starve later events"
    );
    assert!(b
        .store
        .ae_progress(&net.identities[0].deployment)
        .await
        .unwrap()
        .is_some());
    assert!(!b
        .store
        .ae_pending_page(&net.identities[0].deployment, None, 100)
        .await
        .unwrap()
        .entries
        .is_empty());

    a.store.s3.put_opaque(&missing.group).await.unwrap();
    let mut restarted = net.puller(1, 0).await;
    until_group(&mut restarted, b, missing.group.id()).await;
    assert_eq!(
        published_set(&b.store).await.unwrap(),
        published_set(&a.store).await.unwrap()
    );
    b.audit_ok().await;

    // A new publication with a potentially lower content ID still follows the
    // durable versionstamp cursor and arrives after the receiver restarts.
    let newest = a.plain_package(0, "Net.after", "after");
    a.w[0].publish(&newest).await.unwrap();
    until_group(&mut restarted, b, newest.group.id()).await;
}

#[tokio::test]
async fn restarted_puller_resumes_a_persisted_metadata_fragment_cursor() {
    let net = Net::new("net-fragment-restart", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let mut package = a.plain_package(0, "Net.fragmentRestart", "fragment-restart");
    // This synthetic lineage key is carried only in the immutable marker value. It
    // stays below FDB's 100 KiB value limit while exceeding one 64 KiB metadata
    // fragment and the requested 70 KiB page. A long job request ID would
    // instead exceed FDB's 10 KiB key limit at the cancellation lookup. (The
    // marker's file path is capped at 1 KiB by the relative-path rule, W2 A-6.)
    let (_, lamport, author) = package.marker.lineage_keys[0].clone();
    package.marker.lineage_keys.push((Name(vec![NameComp::Str("x".repeat(80 * 1024))]), lamport, author));
    a.w[0].publish(&package).await.unwrap();

    let generation = a.store.ae_identity().await.unwrap().generation;
    let event = a
        .store
        .ae_page(None, 128, ae_wire::MAX_METADATA)
        .await
        .unwrap()
        .events
        .into_iter()
        .find(|event| matches!(event.kind, AeKind::GroupVariant { group, .. } if group == package.group.id()))
        .unwrap();
    let response = ae_wire::exchange(
        net.addresses[0],
        &net.identities[1],
        &Peer {
            deployment: net.identities[0].deployment.clone(),
            verifying_key: net.identities[0].signing_key.verifying_key(),
        },
        ae_wire::Payload {
            metadata: Request::Materialize {
                generation,
                event: event.clone(),
                after_part: None,
                max_bytes: 70 * 1024,
            }
            .to_pce(),
            object: Vec::new(),
        },
        Limits::default(),
    )
    .await
    .unwrap();
    let Response::Materialize(first) = Response::from_pce(&response.metadata).unwrap() else {
        panic!("expected materialized metadata page");
    };
    assert!(!first.complete, "80 KiB marker must require a continuation");
    assert_eq!(first.after_part, None);
    assert_eq!(first.event_key, event.key);
    assert!(first
        .parts
        .iter()
        .any(|(_, part)| matches!(part, AePart::MetaFragment { kind, .. } if kind == "marker")));
    let next_part = first.next_part.expect("first metadata continuation");
    let pending = AePending {
        source: net.identities[0].deployment.clone(),
        generation,
        event: event.clone(),
        next_part: Some(next_part),
        objects_after: None,
        missing_count: 0,
        state: PendingState::Collecting,
        last_error: None,
    };
    let parts: Vec<_> = first
        .parts
        .into_iter()
        .map(|(seq, part)| (event.key.clone(), seq, part))
        .collect();
    b.store
        .ae_save_progress(
            &net.identities[0].deployment,
            generation,
            Some(event.key.clone()),
            &[pending],
            &[],
            &parts,
        )
        .await
        .unwrap();
    assert_eq!(
        b.store
            .ae_pending_page(&net.identities[0].deployment, None, 100)
            .await
            .unwrap()
            .entries[0]
            .next_part,
        Some(next_part)
    );

    // A fresh Puller reads the durable page and skips its numbered fragments.
    let mut restarted = net.puller(1, 0).await;
    until_group(&mut restarted, b, package.group.id()).await;
    assert!(b
        .store
        .ae_pending_page(&net.identities[0].deployment, None, 100)
        .await
        .unwrap()
        .entries
        .is_empty());
    let before = b
        .store
        .ae_page(None, 128, ae_wire::MAX_METADATA)
        .await
        .unwrap()
        .events
        .len();
    for _ in 0..3 {
        restarted.round().await.unwrap();
    }
    let after = b
        .store
        .ae_page(None, 128, ae_wire::MAX_METADATA)
        .await
        .unwrap()
        .events
        .len();
    assert_eq!(
        before, after,
        "replayed fragment page must not duplicate publication"
    );
    b.audit_ok().await;
}

#[tokio::test]
async fn chunked_group_fetches_deduplicated_chunk_and_retries_missing_source() {
    use paralean_store::group_chunks::{chunked_group, ChunkRef};

    let net = Net::new("net-chunks", None).await;
    let a = &net.envs[0];
    let b = &net.envs[1];
    let mut package = a.plain_package(0, "Net.chunked", "chunked");
    let chunk = Opaque::new(Kind::Chunk, b"a chunk with binary \0\xff".to_vec());
    let reference = ChunkRef {
        id: chunk.id(),
        length: chunk.preimage().len() as u64,
    };
    let group = chunked_group(b"opaque Lean group core", &[reference.clone(), reference]).unwrap();
    package.group = group;
    package.chunks = vec![chunk.clone()];
    package.job = fixture::job_by(
        &a.authority(),
        "chunked",
        package.group.id(),
        package.capsule.id(),
        a.w[0].id,
        &[],
    );
    package.receipt = fixture::receipt_for(&package.job, &a.validator, Verdict::Accepted);
    package.revisions[0].group = package.group.id();
    package.marker.group = package.group.id();
    package.marker.revisions = vec![package.revisions[0].id()];
    package.marker.receipt = package.receipt.id();
    package.marker.root_path[0].0 = package.group.id();
    a.w[0].publish(&package).await.unwrap();

    // The published group names a chunk, so its source copy becoming corrupt
    // must keep the event pending rather than publish a group without the chunk.
    a.store
        .s3
        .corrupt_at_rest(Kind::Chunk, &chunk.id(), b"rot")
        .await
        .unwrap();
    let mut puller = net.puller(1, 0).await;
    for _ in 0..6 {
        puller.round().await.unwrap();
    }
    assert!(!published_set(&b.store)
        .await
        .unwrap()
        .groups
        .contains_key(&package.group.id()));
    assert!(b
        .store
        .s3
        .get(Kind::Chunk, &chunk.id())
        .await
        .unwrap()
        .is_none());

    a.store.s3.put_opaque(&chunk).await.unwrap();
    let mut restarted = net.puller(1, 0).await;
    until_group(&mut restarted, b, package.group.id()).await;
    let received = b
        .store
        .s3
        .get(Kind::Chunk, &chunk.id())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(received, chunk.preimage());
    b.audit_ok().await;

    let mut invalid = package.clone();
    invalid.group = chunked_group(
        b"bad length",
        &[ChunkRef {
            id: chunk.id(),
            length: chunk.preimage().len() as u64 + 1,
        }],
    )
    .unwrap();
    invalid.revisions[0].group = invalid.group.id();
    invalid.marker.group = invalid.group.id();
    invalid.marker.revisions = vec![invalid.revisions[0].id()];
    invalid.marker.root_path[0].0 = invalid.group.id();
    invalid.job = fixture::job_by(
        &a.authority(),
        "bad length",
        invalid.group.id(),
        invalid.capsule.id(),
        a.w[0].id,
        &[],
    );
    invalid.receipt = fixture::receipt_for(&invalid.job, &a.validator, Verdict::Accepted);
    invalid.marker.receipt = invalid.receipt.id();
    assert!(
        a.w[0].publish(&invalid).await.is_err(),
        "declared chunk length must be checked before T1"
    );
}

// ---------------------------------------------------------------------------------------
// W2 A-2 and A-12: a malicious but authenticated federation member.

/// W2 A-2, federated: the pinned local member's controller signed a job and then
/// cancelled its request. A group item hand-built from the worker's receipt and the
/// worker's own certificate on the local replica is rejected by T9 at that deployment.
#[tokio::test]
async fn federated_import_rejects_a_cancelled_local_request() {
    let net = Net::new("net-cancelled", None).await;
    let a = &net.envs[0];
    let p = a.plain_package(0, "Net.cancelled", "cancelled");
    assert!(a.store.meta.cancel_job(&p.job.body.request).await.unwrap());
    assert!(a.w[0].publish(&p).await.is_err(), "T1 reads the cancellation");
    let cert = Cert::sign(
        CertBody { replica: a.store.replica, marker: p.marker.id(), group: p.group.id(), writer: a.w[0].id },
        a.w[0].signer(),
    );
    let item = paralean_store::antientropy::Item::Group {
        marker: p.marker.preimage(),
        revisions: p.revisions.iter().map(|r| r.preimage()).collect(),
        receipt: p.receipt.to_bytes(),
        job: p.job.to_bytes(),
        certs: vec![cert.to_bytes()],
    };
    let o = paralean_store::antientropy::import(&a.w[SYNC], &item).await.unwrap();
    assert!(matches!(&o, Outcome::Rejected(why) if why.contains("cancelled")), "{o:?}");
    assert!(a.store.marker(&p.group.id()).await.unwrap().is_none());
}

#[derive(Clone, Copy)]
enum Hostile {
    /// One event whose materialization never completes.
    EndlessParts,
    /// One complete event listing `refs` ObjectRefs of 64 MiB each.
    HugeRefs { refs: u64 },
    /// `events` events of 64 such references each (4 GiB, within the per-event cap).
    ManyEvents { events: u8 },
}

const HUGE: u64 = 64 * 1024 * 1024;

fn hostile_event(i: u8) -> AeEvent {
    AeEvent {
        key: vec![0x42, i],
        kind: AeKind::GroupVariant { group: Id([i; 32]), marker: Id([i ^ 0x80; 32]), cert: Id([0x55; 32]) },
    }
}

/// Serve as deployment 0 (its pinned transport key and real Hello), but with fabricated
/// events. Returns the address and the number of object fetches it was asked for.
async fn hostile_peer(net: &Net, mode: Hostile) -> (SocketAddr, Arc<AtomicUsize>) {
    let hello = net.envs[0].store.ae_identity().await.unwrap();
    let fetches = Arc::new(AtomicUsize::new(0));
    let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
    let address = listener.local_addr().unwrap();
    let peers: std::collections::HashMap<_, _> = net
        .identities
        .iter()
        .map(|i| (i.deployment.clone(), i.signing_key.verifying_key()))
        .collect();
    let counter = fetches.clone();
    let events: Vec<AeEvent> = match mode {
        Hostile::ManyEvents { events } => (1..=events).map(hostile_event).collect(),
        _ => vec![hostile_event(1)],
    };
    tokio::spawn(ae_wire::serve(listener, net.identities[0].clone(), peers, Limits::default(), move |_, payload| {
        let (hello, counter, events) = (hello.clone(), counter.clone(), events.clone());
        async move {
            let response = match Request::from_pce(&payload.metadata).unwrap() {
                Request::Hello => Response::Hello(hello.clone()),
                Request::Changes { after, .. } => {
                    let fresh: Vec<_> = events.iter().filter(|e| after.as_ref().is_none_or(|a| e.key > *a)).cloned().collect();
                    let next = fresh.last().map(|e| e.key.clone()).or(after);
                    Response::Changes(paralean_store::ae::AePage { generation: hello.generation, events: fresh, next, more: false })
                }
                Request::Materialize { event, after_part, .. } => {
                    let first = after_part.map_or(0, |n| n + 1);
                    let (parts, complete): (Vec<(u64, AePart)>, bool) = match mode {
                        Hostile::EndlessParts => ((first..first + 127)
                            .map(|seq| (seq, AePart::MetaFragment { kind: "marker".into(), id: Id([1; 32]), offset: 0, total: 1 << 30, bytes: vec![7; 16] }))
                            .collect(), false),
                        Hostile::HugeRefs { refs } => ((0..refs)
                            .map(|seq| (seq, AePart::ObjectRef { kind: Kind::Capsule, id: Id(paralean_store::id::sha256(&seq.to_be_bytes())), length: HUGE }))
                            .collect(), true),
                        Hostile::ManyEvents { .. } => ((0..64u64)
                            .map(|seq| (seq, AePart::ObjectRef { kind: Kind::Capsule, id: Id(paralean_store::id::sha256(&[&event.key[..], &seq.to_be_bytes()].concat())), length: HUGE }))
                            .collect(), true),
                    };
                    let next_part = parts.last().map(|(seq, _)| *seq).or(after_part);
                    Response::Materialize(paralean_store::ae::AeBundlePage { event_key: event.key, after_part, parts, next_part, complete })
                }
                Request::Fetch { kind, id, .. } => {
                    counter.fetch_add(1, Ordering::SeqCst);
                    Response::Missing { kind, id }
                }
            };
            ae_wire::Payload { metadata: response.to_pce(), object: Vec::new() }
        }
    }));
    (address, fetches)
}

async fn hostile_puller(net: &Net, address: SocketAddr) -> Puller {
    Puller::new(
        net.envs[1].w[SYNC].clone(),
        net.identities[1].clone(),
        Endpoint {
            address,
            peer: Peer {
                deployment: net.identities[0].deployment.clone(),
                verifying_key: net.identities[0].signing_key.verifying_key(),
            },
        },
        Limits { timeout: Duration::from_secs(15), max_connections: 2 },
    )
    .await
    .unwrap()
}

async fn staged_parts(env: &Env, source: &str, event: &AeEvent) -> usize {
    let st = &env.store;
    st.meta.scan(&st.meta.keys.ae_parts(source, &event.key), 1000, |_| None).await.unwrap().len()
}

/// W2 A-12. A peer that never completes an event cannot grow the receiver's FDB past
/// the per-event part cap: the part that would pass it archives the event as terminal
/// and clears what was staged.
#[tokio::test]
async fn endless_event_parts_are_capped_and_archived() {
    let net = Net::new("net-endless-parts", None).await;
    let source = net.identities[0].deployment.clone();
    let (address, fetches) = hostile_peer(&net, Hostile::EndlessParts).await;
    let mut puller = hostile_puller(&net, address).await;
    let b = &net.envs[1];
    let event = hostile_event(1);
    // 8 pages of 127 parts per turn: 8192 parts are passed in the ninth turn.
    for _ in 0..12 {
        puller.round().await.unwrap();
        assert!(staged_parts(b, &source, &event).await as u64 <= paralean_store::ae::MAX_EVENT_PARTS);
    }
    let terminal = b.store.ae_terminal_page(&source, None, 10).await.unwrap().entries;
    assert!(
        terminal.len() == 1 && matches!(&terminal[0].state, PendingState::Terminal(why) if why.contains("8192 parts")),
        "{terminal:?}"
    );
    assert_eq!(staged_parts(b, &source, &event).await, 0, "terminal event's parts are cleared");
    assert!(b.store.ae_pending_page(&source, None, 10).await.unwrap().entries.is_empty());
    assert_eq!(b.store.ae_active_pending_count(&source).await.unwrap(), 0);
    assert_eq!(fetches.load(Ordering::SeqCst), 0);
}

/// W2 A-12. Object references are capped before anything is fetched: an event whose
/// references declare more than the per-event object cap is terminal on staging, and
/// the receiver never asks for (or stores) any of its objects.
#[tokio::test]
async fn oversized_declared_objects_are_terminal_before_fetch() {
    let net = Net::new("net-huge-refs", None).await;
    let source = net.identities[0].deployment.clone();
    let refs = paralean_store::ae::MAX_EVENT_OBJECT_BYTES / HUGE + 1;
    let (address, fetches) = hostile_peer(&net, Hostile::HugeRefs { refs }).await;
    let mut puller = hostile_puller(&net, address).await;
    let b = &net.envs[1];
    for _ in 0..3 {
        puller.round().await.unwrap();
    }
    assert_eq!(fetches.load(Ordering::SeqCst), 0, "no object of an over-cap event is fetched");
    let terminal = b.store.ae_terminal_page(&source, None, 10).await.unwrap().entries;
    assert!(
        terminal.len() == 1 && matches!(&terminal[0].state, PendingState::Terminal(why) if why.contains("GiB cap")),
        "{terminal:?}"
    );
    assert_eq!(staged_parts(b, &source, &hostile_event(1)).await, 0);
}

/// W2 A-12. Events within the per-event cap are bounded per source: once the active events
/// of one source declare `MAX_SOURCE_OBJECT_BYTES`, further references wait (retryable,
/// nothing staged) instead of being fetched.
#[tokio::test]
async fn declared_objects_are_bounded_per_source() {
    let net = Net::new("net-source-cap", None).await;
    let source = net.identities[0].deployment.clone();
    let per_event = 64 * HUGE;
    let admitted = paralean_store::ae::MAX_SOURCE_OBJECT_BYTES / per_event;
    let (address, _) = hostile_peer(&net, Hostile::ManyEvents { events: admitted as u8 + 1 }).await;
    let mut puller = hostile_puller(&net, address).await;
    let b = &net.envs[1];
    for _ in 0..2 {
        puller.round().await.unwrap();
    }
    let mut staged = 0u64;
    let mut waiting = Vec::new();
    for i in 1..=admitted as u8 + 1 {
        let n = staged_parts(b, &source, &hostile_event(i)).await as u64;
        staged += n * HUGE;
        if n == 0 { waiting.push(i); }
    }
    assert!(staged <= paralean_store::ae::MAX_SOURCE_OBJECT_BYTES, "{staged} bytes of references staged");
    assert_eq!(waiting.len(), 1, "exactly one event waits for the source budget: {waiting:?}");
    let pending = b.store.ae_pending_page(&source, None, 100).await.unwrap().entries;
    let blocked = pending.iter().find(|p| p.event.key == hostile_event(waiting[0]).key).unwrap();
    assert!(blocked.last_error.as_deref().is_some_and(|e| e.contains("pending objects")), "{blocked:?}");
    assert!(b.store.ae_terminal_page(&source, None, 10).await.unwrap().entries.is_empty());
}
