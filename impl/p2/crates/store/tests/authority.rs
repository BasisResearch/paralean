//! Signed agent registrations and controller deletion are checked by the FDB write
//! transaction, including receive transactions and key rotation.
mod common;

use common::*;
use paralean_store::antientropy::{export, import, Item, Outcome};
use paralean_store::*;
use paralean_store::pce::Pce;

#[test]
fn tombstone_item_without_grant_keeps_legacy_wire_bytes() {
    let item = Item::Tombstone { tombstone: vec![1, 2], certs: vec![vec![3]], controller_grant: None };
    assert_eq!(item.to_pce(), vec![2, 2, 1, 2, 1, 1, 3]);
    assert_eq!(Item::from_pce(&[2, 2, 1, 2, 1, 1, 3]).unwrap(), item);
}

#[tokio::test]
async fn forged_author_and_revoked_agent_key_fail_at_t1() {
    let e = Env::new("agent-author", 1);
    let mut forged = e.plain_package(0, "Agent.Forged", "forged-author");
    forged.marker.author = AgentId::derive("unregistered author");
    assert!(matches!(guard_of(e.w[0].publish(&forged).await), GuardFailure::AgentKeyNotRegistered(_)));
    let before = e.plain_package(0, "Agent.Before", "before-revocation");
    e.w[0].publish(&before).await.unwrap();
    let old_public = e.w[0].signer().public();
    e.ctl.revoke_agent_key(old_public).await.unwrap();
    let after = e.plain_package(0, "Agent.After", "after-revocation");
    assert_eq!(guard_of(e.w[0].publish(&after).await), GuardFailure::AgentKeyRevoked(old_public));
    e.audit_ok().await;
}

#[tokio::test]
async fn rotated_agent_key_writes_and_old_certificates_remain_verifiable() {
    let cfg = StoreConfig::from_env(&deployment("agent-rotate")).unwrap();
    let e = Env::open(cfg.clone(), 1, Faults::none());
    let first = e.plain_package(0, "Agent.First", "first");
    e.w[0].publish(&first).await.unwrap();
    let old_public = e.w[0].signer().public();
    e.ctl.revoke_agent_key(old_public).await.unwrap();
    let mut rotated_keys = e.kf.clone();
    let new_signer = Signer::derive("rotated-agent-key");
    assert_eq!(rotated_keys.rotate_workspace_key("w0", &new_signer), Some(old_public));
    let rotated = Env::open_keys(cfg, rotated_keys, 1, Faults::none(), None);
    let second = rotated.plain_package(0, "Agent.Second", "second");
    rotated.w[0].publish(&second).await.unwrap();
    assert!(rotated.store.certs(&first.group.id()).await.unwrap().iter().any(|c| c.body.group == first.group.id()));
    assert!(rotated.store.certs(&second.group.id()).await.unwrap().iter().any(|c| c.body.group == second.group.id()));
    rotated.audit_ok().await;
}

#[tokio::test]
async fn old_signer_cannot_make_fresh_tombstone_under_rotated_ring() {
    let cfg = StoreConfig::from_env(&deployment("agent-stale-delete")).unwrap();
    let original = Env::open(cfg.clone(), 1, Faults::none());
    let p = original.plain_package(0, "Agent.StaleDelete", "before-rotation");
    original.w[0].publish(&p).await.unwrap();
    let mut keys = original.kf.clone();
    keys.rotate_workspace_key("w0", &Signer::derive("stale-delete-rotated"));
    let rotated = Env::open_keys(cfg, keys, 1, Faults::none(), None);
    let stale = Writer::new(rotated.store.clone(), original.w[0].id, original.w[0].signer().clone());
    let t = fixture::tombstone_of(&p.marker, 2);
    assert!(matches!(guard_of(stale.tombstone(&t).await), GuardFailure::BadPackage(_)));
    rotated.w[0].tombstone(&t).await.unwrap();
    rotated.audit_ok().await;
}

#[tokio::test]
async fn controller_delete_requires_local_signature_and_current_fence() {
    let e = Env::new("controller-delete", 2);
    let p = e.plain_package(0, "Agent.Deleted", "controller-deleted");
    e.w[0].publish(&p).await.unwrap();
    let mut t = fixture::tombstone_of(&p.marker, 2);
    t.author = controller_agent_id(&e.store.ring.authority);
    assert_eq!(guard_of(e.w[1].tombstone(&t).await), GuardFailure::TombstoneNotAuthor);
    let outsider = Signer::derive("foreign controller");
    let foreign = ControllerDeleteGrant::sign(t.id(), e.store.meta.fence().await.unwrap(), &outsider);
    assert_eq!(guard_of(e.w[1].tombstone_authorized(&t, Some(foreign)).await), GuardFailure::ControllerDeleteDenied);
    let stale = e.ctl.deletion_grant(&t).await.unwrap();
    e.ctl.rotate(e.w[0].id, b"advance-delete-fence").await.unwrap();
    assert_eq!(guard_of(e.w[1].tombstone_authorized(&t, Some(stale)).await), GuardFailure::ControllerDeleteDenied);
    let fresh = e.ctl.deletion_grant(&t).await.unwrap();
    let revoked_writer_key = e.w[1].signer().public();
    e.ctl.revoke_agent_key(revoked_writer_key).await.unwrap();
    assert_eq!(guard_of(e.w[1].tombstone_authorized(&t, Some(fresh.clone())).await), GuardFailure::AgentKeyRevoked(revoked_writer_key));
    e.w[0].tombstone_authorized(&t, Some(fresh.clone())).await.unwrap();
    assert_eq!(e.store.meta.get(e.store.meta.keys.delete_grant(&t.id())).await.unwrap(), Some(fresh.encoded()));
    e.audit_ok().await;
}

#[tokio::test]
async fn controller_delete_relay_keeps_origin_authority() {
    let a = Env::open_keys(StoreConfig::from_env(&deployment("delete-origin")).unwrap(), KeyFile::demo_prefixed("a/", 2), 2, Faults::none(), None);
    let b = Env::open_keys(StoreConfig::from_env(&deployment("delete-relay")).unwrap(), KeyFile::demo_prefixed("b/", 1), 1, Faults::none(), Some(&a.store.ring));
    let c = Env::open_keys(StoreConfig::from_env(&deployment("delete-dest")).unwrap(), KeyFile::demo_prefixed("c/", 1), 1, Faults::none(), Some(&b.store.ring));
    let p = fixture::package_by(&a.authority(), "relay-group", a.w[0].id, &a.validator, &Name::parse("Relay.X"), vec![], None, 1);
    a.w[0].publish(&p).await.unwrap();
    let mut t = fixture::tombstone_of(&p.marker, 2);
    t.author = controller_agent_id(&a.store.ring.authority);
    let grant = a.ctl.deletion_grant(&t).await.unwrap();
    a.w[1].tombstone_authorized(&t, Some(grant)).await.unwrap();
    for item in export(&a.store).await.unwrap() {
        let outcome = import(&b.w[0], &item).await.unwrap();
        assert!(matches!(outcome, Outcome::Applied | Outcome::Present), "{outcome:?}");
    }
    for item in export(&b.store).await.unwrap() {
        let outcome = import(&c.w[0], &item).await.unwrap();
        assert!(matches!(outcome, Outcome::Applied | Outcome::Present), "{outcome:?}");
    }
    assert_eq!(c.store.tombstone(&t.id()).await.unwrap(), Some(t.clone()));
    c.audit_ok().await;
    let mut bad = export(&b.store).await.unwrap().into_iter().find(|item| matches!(item, Item::Tombstone { .. })).unwrap();
    if let Item::Tombstone { certs, .. } = &mut bad {
        // Keep only the relay's certificate. The valid A controller grant has no
        // certificate from its issuing deployment in this received item.
        certs.retain(|bytes| TombstoneCert::from_bytes(bytes).ok().is_some_and(|c| c.body.writer == b.w[0].id));
        assert_eq!(certs.len(), 1);
    }
    let d = Env::open_keys(StoreConfig::from_env(&deployment("delete-forgery")).unwrap(), KeyFile::demo_prefixed("d/", 1), 1, Faults::none(), Some(&b.store.ring));
    for item in export(&a.store).await.unwrap().into_iter().filter(|item| !matches!(item, Item::Tombstone { .. })) {
        let _ = import(&d.w[0], &item).await.unwrap();
    }
    assert!(matches!(import(&d.w[0], &bad).await.unwrap(), Outcome::Rejected(_)));
}

#[tokio::test]
async fn received_controller_delete_uses_source_fence_even_with_shared_controller_key() {
    let ka = KeyFile::demo_prefixed("shared-source/", 1);
    let mut kb = KeyFile::demo_prefixed("shared-receiver/", 1);
    kb.authority = ka.authority.clone();
    kb.authority_public = ka.authority_public.clone();
    kb.agent_keys.clear();
    kb.register_workspace_agents();
    let a = Env::open_keys(StoreConfig::from_env(&deployment("shared-source")).unwrap(), ka.clone(), 1, Faults::none(), Some(&kb.ring()));
    let b = Env::open_keys(StoreConfig::from_env(&deployment("shared-receiver")).unwrap(), kb, 1, Faults::none(), Some(&ka.ring()));
    let p = a.plain_package(0, "Shared.Delete", "source");
    a.w[0].publish(&p).await.unwrap();
    a.ctl.rotate(a.w[0].id, b"source-fence-1").await.unwrap();
    a.ctl.rotate(a.w[0].id, b"source-fence-2").await.unwrap();
    let mut t = fixture::tombstone_of(&p.marker, 2);
    t.author = controller_agent_id(&a.store.ring.authority);
    let grant = a.ctl.deletion_grant(&t).await.unwrap();
    a.w[0].tombstone_authorized(&t, Some(grant)).await.unwrap();
    b.ctl.rotate(b.w[0].id, b"advance-receiver-fence").await.unwrap();
    assert_ne!(a.store.meta.fence().await.unwrap(), b.store.meta.fence().await.unwrap());
    for item in export(&a.store).await.unwrap() {
        let outcome = import(&b.w[0], &item).await.unwrap();
        assert!(matches!(outcome, Outcome::Applied | Outcome::Present), "{outcome:?}");
    }
    assert_eq!(b.store.tombstone(&t.id()).await.unwrap(), Some(t));
    b.audit_ok().await;
}

#[tokio::test]
async fn foreign_controller_cannot_claim_another_origins_writer_certificate() {
    let ka = KeyFile::demo_prefixed("origin-claim-a/", 1);
    let mut kb = KeyFile::demo_prefixed("origin-claim-b/", 1);
    let (a_writer, a_signer) = ka.workspace("w0").unwrap();
    let b_authority = kb.authority_signer().unwrap();
    kb.agent_keys.insert(0, ka.agent_keys.iter().find(|entry| entry.parts().is_some_and(|(_, writer, key, _)|
        writer == a_writer && key == a_signer.public())).unwrap().clone());
    kb.agent_keys.push(AgentKeyGrant::sign(AgentId::derive("claimed author"), a_writer, a_signer.public(), &b_authority));
    let a = Env::open_keys(StoreConfig::from_env(&deployment("origin-claim-a")).unwrap(), ka.clone(), 1, Faults::none(), Some(&kb.ring()));
    let b = Env::open_keys(StoreConfig::from_env(&deployment("origin-claim-b")).unwrap(), kb, 1, Faults::none(), Some(&ka.ring()));
    let p = a.plain_package(0, "Origin.Claim", "source-group");
    a.w[0].publish(&p).await.unwrap();
    for item in export(&a.store).await.unwrap() {
        assert!(matches!(import(&b.w[0], &item).await.unwrap(), Outcome::Applied | Outcome::Present));
    }
    let mut t = fixture::tombstone_of(&p.marker, 2);
    t.author = controller_agent_id(&b.store.ring.authority);
    let cert = TombstoneCert::sign(TombstoneCertBody {
        replica: a.store.replica, tombstone: t.id(), target: t.target, writer: a_writer,
    }, &a_signer);
    let grant = b.ctl.deletion_grant(&t).await.unwrap();
    let forged = Item::Tombstone {
        tombstone: t.preimage(), certs: vec![cert.to_bytes()], controller_grant: Some(grant.encoded()),
    };
    b.store.s3.put(Kind::StagedTombstone, &t.preimage()).await.unwrap();
    let outcome = import(&b.w[0], &forged).await.unwrap();
    assert!(matches!(outcome, Outcome::Rejected(_)), "{outcome:?}");
    assert!(b.store.tombstone(&t.id()).await.unwrap().is_none());
}

#[tokio::test]
async fn rotated_writer_key_is_accepted_by_immutable_federation_roster_only_with_home_grant() {
    use std::collections::BTreeMap;
    let ca = StoreConfig::from_env(&deployment("rotation-home")).unwrap();
    let cb = StoreConfig::from_env(&deployment("rotation-peer")).unwrap();
    let ka = KeyFile::demo_prefixed("rotation-a/", 1);
    let kb = KeyFile::demo_prefixed("rotation-b/", 1);
    let a = Env::open_keys(ca.clone(), ka.clone(), 1, Faults::none(), Some(&kb.ring()));
    let b = Env::open_keys(cb.clone(), kb.clone(), 1, Faults::none(), Some(&ka.ring()));
    let mut members = BTreeMap::new();
    for e in [&a, &b] {
        members.insert(e.store.deployment.clone(), FederationMember {
            replica: e.store.replica, transport_public: [if e.store.deployment == a.store.deployment { 1 } else { 2 }; 32],
            authority: e.kf.ring().authority, writers: e.kf.ring().writers,
            job_issuers: e.kf.ring().job_issuers,
        });
    }
    let cfg_a = FederationConfig { deployment: a.store.deployment.clone(), members: members.clone(), target_homes: BTreeMap::new() };
    let cfg_b = FederationConfig { deployment: b.store.deployment.clone(), members, target_homes: BTreeMap::new() };
    a.store.ae_pin_config(&cfg_a).await.unwrap();
    b.store.ae_pin_config(&cfg_b).await.unwrap();
    let mut ka_new = ka.clone();
    let new_signer = Signer::derive("federated-rotated-key");
    ka_new.rotate_workspace_key("w0", &new_signer).unwrap();
    let a_new = Env::open_keys(ca, ka_new, 1, Faults::none(), Some(&kb.ring()));
    let p = a_new.plain_package(0, "Rotation.Federated", "federated-new");
    a_new.w[0].publish(&p).await.unwrap();
    let mut peer_ring = kb.ring();
    peer_ring.trust(&a_new.store.ring);
    let mut wrong_ring = peer_ring.clone();
    wrong_ring.agent_keys.retain(|grant| grant.public != hex::encode(new_signer.public()));
    wrong_ring.agent_keys.push(AgentKeyGrant::sign(p.marker.author, a_new.w[0].id, new_signer.public(), &b.authority()));
    let wrong_store = Store::open(&cb, wrong_ring, Faults::none()).unwrap();
    let wrong_writer = Writer::new(wrong_store, b.w[0].id, b.w[0].signer().clone());
    let items = export(&a_new.store).await.unwrap();
    for item in items.iter().filter(|item| matches!(item, Item::Object { .. })) {
        let _ = import(&wrong_writer, item).await.unwrap();
    }
    let group = items.iter().find(|item| matches!(item, Item::Group { .. })).unwrap();
    assert!(matches!(import(&wrong_writer, group).await.unwrap(), Outcome::Rejected(_)));
    let good_store = Store::open(&cb, peer_ring, Faults::none()).unwrap();
    let good_writer = Writer::new(good_store.clone(), b.w[0].id, b.w[0].signer().clone());
    for item in &items {
        assert!(matches!(import(&good_writer, item).await.unwrap(), Outcome::Applied | Outcome::Present));
    }
    assert!(good_store.marker(&p.group.id()).await.unwrap().is_some());
    audit::audit(&good_store).await.unwrap().assert_ok();
}
