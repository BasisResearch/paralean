//! Anti-entropy between two independent deployments, each with its own FoundationDB cluster
//! and Garage store (`PARALEAN_PEER_INSTANCE`, see scripts/test.sh): convergence of the
//! published set (groups with markers, tombstones, rendered files) under any delivery
//! order, with partial transfers, duplicates and corrupt bytes; receivers verify hashes and
//! signatures and certify only on their own replica.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::collections::BTreeSet;

use common::*;
use paralean_store::antientropy::{self, import, import_bytes, published_set, Item, Outcome, PublishedSet};
use paralean_store::pce::Pce;
use paralean_store::recovery::discover;
use paralean_store::*;
use proptest::prelude::*;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

const N: usize = 3; // writers w0, w1 author; w2 is the anti-entropy agent
const S: usize = 2;
const F: &str = "Shared.lean";

fn sync_of(e: &Env) -> (&Store, &Writer) {
    (&e.store, &e.w[S])
}

/// Publish a fresh group in `F`.
async fn insert(e: &Env, wi: usize, tag: &str, anchor: Option<&Marker>, lamport: u64) -> Package {
    let mut p = fixture::package_by(&e.authority(), tag, e.w[wi].id, &e.validator, &Name::parse(&format!("Sh.{tag}")), vec![], None, lamport);
    fixture::place(&mut p, F, anchor, None);
    e.w[wi].publish(&p).await.unwrap();
    p
}

async fn revise(e: &Env, wi: usize, tag: &str, of: &Package, lamport: u64) -> Package {
    let name = of.revisions[0].name.clone();
    let mut p = fixture::package_by(&e.authority(), tag, e.w[wi].id, &e.validator, &name, vec![rev_id(of)], None, lamport);
    fixture::place(&mut p, F, None, Some(&of.marker));
    e.w[wi].publish(&p).await.unwrap();
    p
}

/// Every certificate key of the deployment is its own: signed by one of its own workspaces
/// and naming its own replica. Received certificates exist only as `xcert/` evidence.
async fn certifies_only_for_itself(e: &Env) {
    let own: BTreeSet<WorkspaceId> = e.w.iter().map(|w| w.id).collect();
    let keys = &e.store.meta.keys;
    for (_, v) in e.store.meta.scan(&keys.sub("cert"), 1000, |_| None).await.unwrap() {
        let c = Cert::from_bytes(&v).unwrap();
        assert!(own.contains(&c.body.writer) && c.body.replica == e.store.replica, "foreign certificate {c:?}");
    }
    for (_, v) in e.store.meta.scan(&keys.sub("tcert"), 1000, |_| None).await.unwrap() {
        let c = TombstoneCert::from_bytes(&v).unwrap();
        assert!(own.contains(&c.body.writer) && c.body.replica == e.store.replica, "foreign certificate {c:?}");
    }
}

async fn audits_clean(a: &Env, b: &Env) {
    for e in [a, b] {
        let r = e.audit_ok().await;
        assert!(r.uncertified_markers.is_empty() && r.uncertified_tombstones.is_empty());
        certifies_only_for_itself(e).await;
    }
}

// ---------------------------------------------------------------------------------------
/// Two clusters publish independently (fresh insertions, a revision, tombstones, a target
/// name at A), then synchronise until neither side changes: both expose the union, render
/// the shared file identically and pass the audit, and a further sync changes nothing.
#[tokio::main(flavor = "current_thread")]
async fn sync_converges_between_two_clusters() {
    let (a, b) = pair("ae-conv", N, Faults::none(), Faults::none());
    let a1 = insert(&a, 0, "a1", None, 1).await;
    let a2 = insert(&a, 1, "a2", Some(&a1.marker), 2).await;
    let a3 = revise(&a, 0, "a3", &a1, 3).await;
    a.w[1].tombstone(&fixture::tombstone_of(&a2.marker, 4)).await.unwrap();
    let x = Name::parse("Target.x");
    a.ctl.reassign(&x, a.w[0].id, b"assign").await.unwrap();
    let (ax, _) = a.publish_target(0, &x, "ax").await.unwrap();
    let b1 = insert(&b, 0, "b1", None, 1).await;
    let b2 = insert(&b, 1, "b2", Some(&b1.marker), 5).await;
    let b3 = insert(&b, 0, "b3", Some(&b2.marker), 6).await;
    b.w[0].tombstone(&fixture::tombstone_of(&b3.marker, 7)).await.unwrap();
    assert_ne!(b.store.replica, a.store.replica);

    let (rounds, ab, _) = antientropy::sync(sync_of(&a), sync_of(&b), 10).await.unwrap();
    let (pa, pb) = (published_set(&a.store).await.unwrap(), published_set(&b.store).await.unwrap());
    // A's target group stays at A: its receipt binds A's target epoch, which only A's
    // controller can sign and only A's record fences (P3 receipt binding).
    assert_eq!(ab.rejected.len(), 1, "{ab:?}");
    assert!(ab.rejected[0].contains("target epochs"), "{:?}", ab.rejected);
    let pa_free = antientropy::exchangeable_set(&a.store).await.unwrap();
    assert_eq!(pa_free.groups.len() + 1, pa.groups.len());
    assert!(!pa_free.groups.contains_key(&ax.group.id()));
    assert_eq!(pa_free, pb);
    assert_eq!(antientropy::exchangeable_set(&b.store).await.unwrap(), pb);
    let want: BTreeSet<Id> = [&a1, &a2, &a3, &ax, &b1, &b2, &b3].iter().map(|p| p.group.id()).collect();
    assert_eq!(pa.groups.keys().copied().collect::<BTreeSet<_>>(), want);
    assert_eq!(pa.tombstones.len(), 2);
    // b1 (key (1, b)) and a1's lineage (root key (1, a)) are siblings at the file start;
    // the larger key renders first.
    let f = &pa.files[F];
    assert!(!f.contains(&a2.group.id()) && !f.contains(&b3.group.id()) && !f.contains(&a1.group.id()));
    assert_eq!(f.len(), 3, "{f:?}");
    eprintln!("converged after {rounds} rounds; file {F}: {f:?}");
    audits_clean(&a, &b).await;
    // The registry follows: B has no head for A's target name.
    let db = discover(&b.store).await.unwrap();
    assert!(!db.heads.contains_key(&x));
    // Idempotent: another sync applies nothing.
    let (rounds, ab, ba) = antientropy::sync(sync_of(&a), sync_of(&b), 3).await.unwrap();
    assert_eq!((rounds, ab.applied, ba.applied), (1, 0, 0));
    assert!(ab.rejected.len() == 1 && ba.rejected.is_empty() && ab.conflicts.is_empty());
}

// ---------------------------------------------------------------------------------------
/// The receiver trusts nothing in transit: corrupt or truncated bytes, a tampered marker or
/// revision, a forged certificate, a certificate by a writer it does not trust, a receipt
/// from an untrusted validator and a group with no certificate (a staged marker) are all
/// rejected and write no metadata.
#[tokio::main(flavor = "current_thread")]
async fn receiver_rejects_corrupt_forged_and_untrusted() {
    let (a, b) = pair("ae-reject", N, Faults::none(), Faults::none());
    let p = insert(&a, 0, "p", None, 1).await;
    let items = antientropy::export(&a.store).await.unwrap();
    let group_item = items.iter().find(|i| matches!(i, Item::Group { .. })).unwrap().clone();
    let objects: Vec<Item> = items.iter().filter(|i| matches!(i, Item::Object { .. })).cloned().collect();
    let keys = |e: &Env| {
        let st = e.store.clone();
        async move { st.meta.scan(&st.meta.keys.root, 10_000, |_| None).await.unwrap().len() }
    };
    let before = keys(&b).await;
    let rejected = |o: Outcome| assert!(matches!(o, Outcome::Rejected(_)), "{o:?}");
    // Corrupt object bytes and a wrong ID.
    if let Item::Object { kind, id, bytes } = &objects[0] {
        let mut bad = bytes.clone();
        bad[bytes.len() / 2] ^= 1;
        rejected(import(&b.w[S], &Item::Object { kind: *kind, id: *id, bytes: bad }).await.unwrap());
        assert!(b.store.s3.get(*kind, id).await.unwrap().is_none());
    }
    // Truncated and bit-flipped encodings of the whole group item.
    let enc = group_item.to_pce();
    rejected(import_bytes(&b.w[S], &enc[..enc.len() / 2]).await.unwrap());
    let Item::Group { marker, revisions, receipt, job, certs } = group_item.clone() else { unreachable!() };
    // A tampered marker: its certificate no longer names it.
    let mut m2 = p.marker.clone();
    m2.lamport = 99;
    rejected(import(&b.w[S], &Item::Group { marker: m2.preimage(), revisions: revisions.clone(), receipt: receipt.clone(), job: job.clone(), certs: certs.clone() }).await.unwrap());
    // A tampered revision: not the marker's.
    let mut r2 = p.revisions[0].clone();
    r2.parents = vec![Id([3; 32])];
    rejected(import(&b.w[S], &Item::Group { marker: marker.clone(), revisions: vec![r2.preimage()], receipt: receipt.clone(), job: job.clone(), certs: certs.clone() }).await.unwrap());
    // A forged certificate (right writer, wrong key) and one by an untrusted writer.
    let forged = Cert::sign(CertBody { replica: a.store.replica, marker: p.marker.id(), group: p.group.id(), writer: a.w[0].id }, &Signer::derive("mallory"));
    let stranger = Cert::sign(
        CertBody { replica: a.store.replica, marker: p.marker.id(), group: p.group.id(), writer: WorkspaceId::derive("mallory") },
        &Signer::derive("mallory"),
    );
    rejected(
        import(&b.w[S], &Item::Group { marker: marker.clone(), revisions: revisions.clone(), receipt: receipt.clone(), job: job.clone(), certs: vec![forged.to_bytes(), stranger.to_bytes()] })
            .await
            .unwrap(),
    );
    // No certificate at all: a staged marker is not a publication.
    rejected(import(&b.w[S], &Item::Group { marker: marker.clone(), revisions: revisions.clone(), receipt: receipt.clone(), job: job.clone(), certs: vec![] }).await.unwrap());
    // A receipt signed by a validator B does not trust.
    let mut rb = Receipt::from_bytes(&receipt).unwrap().body;
    let rogue = Signer::derive("rogue validator");
    rb.validator_key = rogue.public();
    let r3 = Receipt::sign(rb, &rogue);
    rejected(import(&b.w[S], &Item::Group { marker: marker.clone(), revisions: revisions.clone(), receipt: r3.to_bytes(), job: job.clone(), certs: certs.clone() }).await.unwrap());
    // The genuine receipt with its envelope re-signed by a key B does not trust, or missing.
    let mut sj = SignedJob::from_bytes(&job).unwrap();
    sj = SignedJob::sign(sj.body, &Signer::derive("mallory"));
    rejected(import(&b.w[S], &Item::Group { marker: marker.clone(), revisions: revisions.clone(), receipt: receipt.clone(), job: sj.to_bytes(), certs: certs.clone() }).await.unwrap());
    rejected(import(&b.w[S], &Item::Group { marker: marker.clone(), revisions: revisions.clone(), receipt: receipt.clone(), job: vec![], certs: certs.clone() }).await.unwrap());
    assert_eq!(keys(&b).await, before, "no metadata written by a rejected item");
    // A forged tombstone certificate.
    a.w[0].tombstone(&fixture::tombstone_of(&p.marker, 2)).await.unwrap();
    let t = fixture::tombstone_of(&p.marker, 2);
    let tforged = TombstoneCert::sign(
        TombstoneCertBody { replica: a.store.replica, tombstone: t.id(), target: t.target, writer: a.w[0].id },
        &Signer::derive("mallory"),
    );
    rejected(import(&b.w[S], &Item::Tombstone { tombstone: t.preimage(), certs: vec![tforged.to_bytes()] }).await.unwrap());
    // The genuine items still converge afterwards.
    antientropy::sync(sync_of(&a), sync_of(&b), 10).await.unwrap();
    assert_eq!(published_set(&a.store).await.unwrap(), published_set(&b.store).await.unwrap());
    audits_clean(&a, &b).await;
}

// ---------------------------------------------------------------------------------------
/// Out-of-order delivery: a group before its payloads, a revision before its parent group,
/// a tombstone before its target are deferred (nothing written), then applied when their
/// dependencies arrive. Duplicates are `Present`.
#[tokio::main(flavor = "current_thread")]
async fn deferred_until_dependencies_arrive() {
    let (a, b) = pair("ae-defer", N, Faults::none(), Faults::none());
    let p = insert(&a, 0, "p", None, 1).await;
    let q = revise(&a, 0, "q", &p, 2).await;
    a.w[0].tombstone(&fixture::tombstone_of(&q.marker, 3)).await.unwrap();
    let mut items = antientropy::export(&a.store).await.unwrap();
    items.reverse(); // tombstone first, objects last
    let mut outcomes = Vec::new();
    for i in &items {
        outcomes.push(import(&b.w[S], i).await.unwrap());
    }
    assert!(matches!(outcomes[0], Outcome::Deferred(_)), "tombstone before its target: {:?}", outcomes[0]);
    assert!(outcomes.iter().filter(|o| matches!(o, Outcome::Deferred(_))).count() >= 3, "{outcomes:?}");
    assert!(published_set(&b.store).await.unwrap().groups.is_empty());
    b.audit_ok().await;
    // Repeating the same worst-case order applies one level of the dependency chain per
    // round (p, then q, then the tombstone); after that every delivery is a duplicate.
    let mut rounds = 1;
    loop {
        let mut applied = 0;
        for i in &items {
            applied += (import(&b.w[S], i).await.unwrap() == Outcome::Applied) as usize;
        }
        rounds += 1;
        if applied == 0 {
            break;
        }
    }
    assert_eq!(rounds, 5, "objects, p, q, tombstone, then nothing");
    for i in &items {
        assert_eq!(import(&b.w[S], i).await.unwrap(), Outcome::Present);
    }
    let pb = published_set(&b.store).await.unwrap();
    assert_eq!(pb, published_set(&a.store).await.unwrap());
    assert_eq!(pb.files.get(F).cloned().unwrap_or_default(), Vec::<Id>::new(), "p superseded by q, q deleted");
    audits_clean(&a, &b).await;
}

// ---------------------------------------------------------------------------------------
/// Receive transactions under faults: unknown commit results (landed or not) on T9/T10 are
/// resolved by the idempotent retry; a receiver crash before its transaction leaves nothing
/// but acknowledged payloads, and the next round finishes the job.
#[tokio::main(flavor = "current_thread")]
async fn receive_faults_resolve() {
    let fb = Faults::none();
    let (a, b) = pair("ae-faults", N, Faults::none(), fb.clone());
    let p = insert(&a, 0, "p", None, 1).await;
    let q = insert(&a, 0, "q", Some(&p.marker), 2).await;
    let r = insert(&a, 1, "r", Some(&q.marker), 3).await;
    a.w[0].tombstone(&fixture::tombstone_of(&q.marker, 4)).await.unwrap();
    fb.on_commit(Some(Txn::T9ReceiveGroup), 0, CommitFault::UnknownCommitted);
    fb.on_commit(Some(Txn::T9ReceiveGroup), 0, CommitFault::UnknownNotCommitted);
    fb.on_commit(Some(Txn::T10ReceiveTombstone), 0, CommitFault::UnknownCommitted);
    fb.crash_at("receive:before-group", 1);
    let items = antientropy::export(&a.store).await.unwrap();
    let mut crashed = 0;
    for i in &items {
        match import(&b.w[S], i).await {
            Ok(_) => {}
            Err(e) if e.is_crash() => crashed += 1,
            Err(e) => panic!("{e}"),
        }
    }
    assert_eq!(crashed, 1);
    b.audit_ok().await;
    antientropy::sync(sync_of(&a), sync_of(&b), 10).await.unwrap();
    assert_eq!(fb.stats().get("unknown-result-resolved").copied(), Some(3), "{:?}", fb.stats());
    let pb = published_set(&b.store).await.unwrap();
    assert_eq!(pb, published_set(&a.store).await.unwrap());
    assert_eq!(pb.files[F], vec![p.group.id(), r.group.id()]);
    audits_clean(&a, &b).await;
}

// ---------------------------------------------------------------------------------------
/// Corrupt bytes at rest: a payload rotten at the receiver is repaired by the next round
/// (content addressing fixes the bytes); one rotten at the sender is not exported, so the
/// group waits at the receiver until the sender's copy is repaired, and nothing corrupt is
/// ever acknowledged.
#[tokio::main(flavor = "current_thread")]
async fn corrupt_payloads_at_rest_are_repaired_or_wait() {
    let (a, b) = pair("ae-rot", N, Faults::none(), Faults::none());
    let p = insert(&a, 0, "p", None, 1).await;
    antientropy::sync(sync_of(&a), sync_of(&b), 10).await.unwrap();
    // Rot at B: B's audit sees it; one round from A repairs it.
    b.store.s3.corrupt_at_rest(Kind::Capsule, &p.capsule.id(), b"rot").await.unwrap();
    assert!(!audit::audit(&b.store).await.unwrap().ok());
    let s = antientropy::push(&a.store, &b.w[S]).await.unwrap();
    assert_eq!(s.applied, 1, "exactly the rotten capsule is re-PUT");
    b.audit_ok().await;
    // Rot at A before B ever saw the group: A exports the group without that payload.
    let q = insert(&a, 0, "q", Some(&p.marker), 2).await;
    a.store.s3.corrupt_at_rest(Kind::Group, &q.group.id(), b"rot").await.unwrap();
    let s = antientropy::push(&a.store, &b.w[S]).await.unwrap();
    assert_eq!(s.deferred, 1, "{s:?}");
    assert!(!published_set(&b.store).await.unwrap().groups.contains_key(&q.group.id()));
    b.audit_ok().await;
    // A's copy is repaired (re-PUT of the verified bytes); the next round delivers q.
    a.store.s3.put_opaque(&q.group).await.unwrap();
    antientropy::sync(sync_of(&a), sync_of(&b), 10).await.unwrap();
    assert_eq!(published_set(&b.store).await.unwrap(), published_set(&a.store).await.unwrap());
    audits_clean(&a, &b).await;
}

// ---------------------------------------------------------------------------------------
/// The same group published at both deployments with different markers (different
/// positions): the store keeps one marker per group and the Workspaces model gives a group
/// one position, so neither side's marker is replaced. Both sides report the conflict; the
/// group set converges, the marker map does not (docs/p2-log.md, "Anti-entropy").
#[tokio::main(flavor = "current_thread")]
async fn marker_conflict_is_reported_not_overwritten() {
    let (a, b) = pair("ae-conflict", N, Faults::none(), Faults::none());
    let pa = fixture::package_by(&a.authority(), "same", a.w[0].id, &a.validator, &Name::parse("Sh.same"), vec![], None, 1);
    let mut pb = pa.clone();
    pb.marker.lamport = 2;
    pb.marker.author = AgentId::derive("someone at b");
    pb.marker.root_path = vec![(pb.group.id(), 2, pb.marker.author)];
    a.w[0].publish(&pa).await.unwrap();
    // B's writer publishes the same group, revision and receipt under its own marker (B
    // trusts A's controller as an issuer of target-free envelopes).
    b.w[0].publish(&Package { revisions: pa.revisions.clone(), ..pb.clone() }).await.unwrap();
    let ab = antientropy::push(&a.store, &b.w[S]).await.unwrap();
    let ba = antientropy::push(&b.store, &a.w[S]).await.unwrap();
    let g = pa.group.id();
    assert_eq!(ab.conflicts, BTreeSet::from([(g, pb.marker.id(), pa.marker.id())]));
    assert_eq!(ba.conflicts, BTreeSet::from([(g, pa.marker.id(), pb.marker.id())]));
    let (sa, sb) = (published_set(&a.store).await.unwrap(), published_set(&b.store).await.unwrap());
    assert_eq!(sa.groups.keys().collect::<Vec<_>>(), sb.groups.keys().collect::<Vec<_>>());
    assert_ne!(sa.groups[&g], sb.groups[&g]);
    audits_clean(&a, &b).await;
}

// ---------------------------------------------------------------------------------------
/// TargetNames keeps one record per name in one store. A group declaring a name that the
/// receiver homes as a target name is refused (only the owner publishes it, through T1);
/// at a deployment without that record it is an ordinary name. T7 cannot copy the sender's
/// certificate either (another replica).
#[tokio::main(flavor = "current_thread")]
async fn foreign_target_names_and_certificate_copies_refused() {
    let (a, b) = pair("ae-target", N, Faults::none(), Faults::none());
    let x = Name::parse("Target.x");
    a.ctl.reassign(&x, a.w[0].id, b"assign").await.unwrap();
    b.ctl.reassign(&x, b.w[0].id, b"assign").await.unwrap();
    let (ax, _) = a.publish_target(0, &x, "ax").await.unwrap();
    // A name A has no record of, homed at B: A publishes it as a free name.
    let y = Name::parse("Target.y");
    b.ctl.reassign(&y, b.w[0].id, b"assign").await.unwrap();
    let ay = fixture::package_by(&a.authority(), "ay", a.w[0].id, &a.validator, &y, vec![], None, 1);
    a.w[0].publish(&ay).await.unwrap();
    let s = antientropy::push(&a.store, &b.w[S]).await.unwrap();
    assert_eq!(s.rejected.len(), 2, "{s:?}");
    assert!(s.rejected.iter().any(|r| r.contains("target epochs")), "{:?}", s.rejected);
    assert!(s.rejected.iter().any(|r| r.contains("target name homed")), "{:?}", s.rejected);
    let pb = published_set(&b.store).await.unwrap();
    assert!(!pb.groups.contains_key(&ax.group.id()) && !pb.groups.contains_key(&ay.group.id()));
    // T7 from A to B: B is not a replacement of A's replica.
    let mv = a.store.meta.get(a.store.meta.keys.marker(&ax.group.id())).await.unwrap().unwrap();
    b.store.meta.raw_set(b.store.meta.keys.marker(&ax.group.id()), mv).await.unwrap();
    let r = b.w[S].repair_cert(&a.store, CertKey::Publication { group: ax.group.id(), writer: a.w[0].id }).await;
    assert_eq!(guard_of(r), GuardFailure::RepairInvalid("certificate names another replica".into()));
}

// ---------------------------------------------------------------------------------------
/// P3 receipt binding across deployments. A received group needs a receipt that passes the
/// staging rule under the *receiver's* key ring (pinned policy and checker, trusted issuer),
/// and a receiver's revocation of the validator, read inside T9, stops the receive. A sender
/// does not export groups whose validator it revoked. Rejected items write nothing.
#[tokio::main(flavor = "current_thread")]
async fn received_groups_need_a_receipt_valid_here() {
    let (a, b) = pair("ae-receipt", N, Faults::none(), Faults::none());
    let p = insert(&a, 0, "p", None, 1).await;
    let g = p.group.id();
    let keys = |e: &Env| {
        let st = e.store.clone();
        async move { st.meta.scan(&st.meta.keys.root, 10_000, |_| None).await.unwrap().len() }
    };
    // A receiver that pins no checker refuses the receipt.
    let mut ring = b.store.ring.as_ref().clone();
    ring.pins.checkers.clear();
    let strict = Store::open(&b.cfg, ring, Faults::none()).unwrap();
    let (sid, ss) = b.kf.workspace(&format!("w{S}")).unwrap();
    let sw = Writer::new(strict, sid, ss);
    let o = antientropy::push(&a.store, &sw).await.unwrap();
    assert!(o.rejected.iter().any(|r| r.contains("CheckerNotPinned")), "{o:?}");
    assert!(published_set(&b.store).await.unwrap().groups.is_empty());
    // B revokes the validator: T9 refuses, nothing of the group is written.
    b.revoke(a.validator.public()).await;
    let before = keys(&b).await;
    let o = antientropy::push(&a.store, &b.w[S]).await.unwrap();
    assert!(o.rejected.iter().any(|r| r.contains("revoked")), "{o:?}");
    assert_eq!(keys(&b).await, before);
    assert!(b.store.marker(&g).await.unwrap().is_none());
    // A revokes it too: A stops exporting the group (it is suspect at A).
    let (c, d) = pair("ae-receipt2", N, Faults::none(), Faults::none());
    let q = insert(&c, 0, "q", None, 1).await;
    c.revoke(c.validator.public()).await;
    let items = antientropy::export(&c.store).await.unwrap();
    assert!(!items.iter().any(|i| matches!(i, Item::Group { .. })), "{items:?}");
    antientropy::sync(sync_of(&c), sync_of(&d), 3).await.unwrap();
    assert!(published_set(&d.store).await.unwrap().groups.is_empty());
    assert_eq!(audit::audit(&c.store).await.unwrap().suspect_receipts, vec![q.group.id()]);
    // Without revocations the group arrives with its envelope, and B's audit re-checks the
    // binding against the stored `job/` (as for its own publications).
    let (e, f) = pair("ae-receipt3", N, Faults::none(), Faults::none());
    let r = insert(&e, 0, "r", None, 1).await;
    antientropy::sync(sync_of(&e), sync_of(&f), 5).await.unwrap();
    assert!(f.store.meta.get(f.store.meta.keys.job(&r.job.id())).await.unwrap().is_some());
    audits_clean(&e, &f).await;
}

// ---------------------------------------------------------------------------------------
/// W2 A-2. A's controller cancels a request after its receipt was issued. T1 refuses it,
/// and so does T9 at A: neither an item hand-built from the worker's receipt with the
/// worker's own certificate, nor the same group relayed by a peer that published it
/// (`sync`), publishes the cancelled request at A.
#[tokio::main(flavor = "current_thread")]
async fn cancelled_request_is_not_received_by_its_issuer() {
    let (a, b) = pair("ae-cancel", N, Faults::none(), Faults::none());
    let mut p = a.plain_package(0, "Sh.cancelled", "cancelled");
    fixture::place(&mut p, F, None, None);
    assert!(a.store.meta.cancel_job(&p.job.body.worker, &p.job.body.request).await.unwrap());
    assert!(matches!(guard_of(a.w[0].publish(&p).await), GuardFailure::JobCancelled(_)));
    // T1 put the payloads before it aborted; the worker signs its own certificate.
    let cert = Cert::sign(CertBody { replica: a.store.replica, marker: p.marker.id(), group: p.group.id(), writer: a.w[0].id }, a.w[0].signer());
    let item = Item::Group {
        marker: p.marker.preimage(),
        revisions: p.revisions.iter().map(|r| r.preimage()).collect(),
        receipt: p.receipt.to_bytes(),
        job: p.job.to_bytes(),
        certs: vec![cert.to_bytes()],
    };
    let o = import(&a.w[S], &item).await.unwrap();
    assert!(matches!(&o, Outcome::Rejected(why) if why.contains("cancelled")), "{o:?}");
    assert!(a.store.marker(&p.group.id()).await.unwrap().is_none());
    // The relay: B trusts A's controller as a job issuer and publishes the worker's
    // package (it cannot read A's cancellation); anti-entropy then offers it to A.
    let relay = Writer::new(b.store.clone(), a.w[0].id, a.w[0].signer().clone());
    relay.publish(&p).await.unwrap();
    let (_, _, to_a) = antientropy::sync(sync_of(&a), sync_of(&b), 5).await.unwrap();
    assert!(to_a.rejected.iter().any(|r| r.contains("cancelled")), "{to_a:?}");
    assert!(a.store.marker(&p.group.id()).await.unwrap().is_none());
    assert!(!published_set(&a.store).await.unwrap().groups.contains_key(&p.group.id()));
    a.audit_ok().await;
    // A request A did not cancel still arrives through the same relay.
    let mut q = a.plain_package(0, "Sh.kept", "kept");
    fixture::place(&mut q, F, None, None);
    relay.publish(&q).await.unwrap();
    antientropy::sync(sync_of(&a), sync_of(&b), 5).await.unwrap();
    assert!(published_set(&a.store).await.unwrap().groups.contains_key(&q.group.id()));
}

/// W2 A-2. T1's dependency guard applies to a received group: a group whose job names a
/// dependency capsule waits at the receiver until that dependency is published and
/// certified there, then arrives.
#[tokio::main(flavor = "current_thread")]
async fn received_group_waits_for_job_dependencies_here() {
    let (a, b) = pair("ae-jobdeps", N, Faults::none(), Faults::none());
    let p = insert(&a, 0, "dep", None, 1).await;
    // A P1-style dependency capsule naming p's group (only `declId` is read).
    let cap = Opaque::new(Kind::Capsule, format!("{{\"declId\":\"{}\"}}", p.group.id().hex()).into_bytes());
    for e in [&a, &b] {
        e.store.s3.put_opaque(&cap).await.unwrap();
    }
    let mut q = fixture::package_by(&a.authority(), "dependent", a.w[1].id, &a.validator, &Name::parse("Sh.dependent"), vec![], None, 2);
    fixture::place(&mut q, F, Some(&p.marker), None);
    let mut body = q.job.body.clone();
    body.deps = vec![cap.id()];
    q.job = SignedJob::sign(body, &a.authority());
    q.receipt = fixture::receipt_for(&q.job, &a.validator, Verdict::Accepted);
    q.marker.receipt = q.receipt.id();
    a.w[1].publish(&q).await.unwrap();
    let items = antientropy::export(&a.store).await.unwrap();
    for i in items.iter().filter(|i| matches!(i, Item::Object { .. })) {
        import(&b.w[S], i).await.unwrap();
    }
    let group_of = |m: &Marker| items.iter().find(|i| matches!(i, Item::Group { marker, .. } if *marker == m.preimage())).unwrap().clone();
    let o = import(&b.w[S], &group_of(&q.marker)).await.unwrap();
    assert!(matches!(&o, Outcome::Deferred(why) if why.contains(&format!("{:?}", p.group.id()))), "{o:?}");
    assert!(b.store.marker(&q.group.id()).await.unwrap().is_none());
    assert_eq!(import(&b.w[S], &group_of(&p.marker)).await.unwrap(), Outcome::Applied);
    assert_eq!(import(&b.w[S], &group_of(&q.marker)).await.unwrap(), Outcome::Applied);
    assert_eq!(published_set(&a.store).await.unwrap(), published_set(&b.store).await.unwrap());
    audits_clean(&a, &b).await;
}

// ---------------------------------------------------------------------------------------
// Property: any exchange order converges to the same published set.

#[derive(Clone, Debug)]
enum Act {
    /// A fresh insertion after the side's `k`-th group (none: the file start).
    Insert(Option<usize>),
    /// A revision of the side's `k`-th group.
    Revise(usize),
    /// A tombstone of the side's `k`-th group.
    Delete(usize),
}

#[derive(Clone, Copy, Debug)]
enum Delivery {
    Deliver,
    Drop,
    Duplicate,
    Corrupt,
    Truncate,
}

fn act() -> impl Strategy<Value = Act> {
    prop_oneof![
        4 => proptest::option::of(0..6usize).prop_map(Act::Insert),
        1 => (0..6usize).prop_map(Act::Revise),
        1 => (0..6usize).prop_map(Act::Delete),
    ]
}

fn delivery() -> impl Strategy<Value = Delivery> {
    prop_oneof![
        5 => Just(Delivery::Deliver),
        2 => Just(Delivery::Drop),
        1 => Just(Delivery::Duplicate),
        1 => Just(Delivery::Corrupt),
        1 => Just(Delivery::Truncate),
    ]
}

/// Run one side's acts; returns the groups and tombstones it published.
async fn play(e: &Env, side: &str, acts: &[Act], lamport: &mut u64) -> (BTreeSet<Id>, BTreeSet<Id>) {
    let mut mine: Vec<Package> = Vec::new();
    let mut deleted = BTreeSet::new();
    let mut tombs = BTreeSet::new();
    for (i, a) in acts.iter().enumerate() {
        *lamport += 1;
        let tag = format!("{side}{i}");
        match a {
            Act::Insert(k) => {
                let anchor = k.and_then(|k| mine.get(k % mine.len().max(1))).filter(|p| p.revisions[0].parents.is_empty());
                let p = insert(e, i % 2, &tag, anchor.map(|p| &p.marker), *lamport).await;
                mine.push(p);
            }
            Act::Revise(k) if !mine.is_empty() => {
                let of = mine[k % mine.len()].clone();
                let p = revise(e, 0, &tag, &of, *lamport).await;
                mine.push(p);
            }
            Act::Delete(k) if !mine.is_empty() => {
                let of = &mine[k % mine.len()];
                let author = e.w.iter().position(|w| w.id == of.revisions[0].workspace).unwrap();
                if deleted.insert(of.group.id()) {
                    let t = fixture::tombstone_of(&of.marker, *lamport);
                    e.w[author].tombstone(&t).await.unwrap();
                    tombs.insert(t.id());
                }
            }
            _ => {}
        }
    }
    (mine.iter().map(|p| p.group.id()).collect(), tombs)
}

/// Deliver `from`'s export to `to` in a random order with per-item faults.
async fn chaotic_push(from: &Env, to: &Env, seed: u64, faults: &[Delivery]) {
    let mut rng = StdRng::seed_from_u64(seed);
    let mut items: Vec<Vec<u8>> = antientropy::export(&from.store).await.unwrap().iter().map(|i| i.to_pce()).collect();
    for i in (1..items.len()).rev() {
        items.swap(i, rng.gen_range(0..=i));
    }
    for (i, bytes) in items.iter().enumerate() {
        let f = if faults.is_empty() { Delivery::Deliver } else { faults[i % faults.len()] };
        let sends: Vec<Vec<u8>> = match f {
            Delivery::Deliver => vec![bytes.clone()],
            Delivery::Drop => vec![],
            Delivery::Duplicate => vec![bytes.clone(), bytes.clone()],
            Delivery::Corrupt => {
                let mut b = bytes.clone();
                let k = rng.gen_range(0..b.len());
                b[k] ^= 1 << rng.gen_range(0..8);
                vec![b]
            }
            Delivery::Truncate => vec![bytes[..rng.gen_range(0..bytes.len())].to_vec()],
        };
        for s in sends {
            import_bytes(&to.w[S], &s).await.unwrap();
        }
    }
}

async fn convergence_case(a_acts: Vec<Act>, b_acts: Vec<Act>, schedule: Vec<(bool, u64, Vec<Delivery>)>) -> std::result::Result<(), String> {
    let (a, b) = pair("ae-prop", N, Faults::none(), Faults::none());
    let mut lamport = 0;
    let (ga, ta) = play(&a, "a", &a_acts, &mut lamport).await;
    let (gb, tb) = play(&b, "b", &b_acts, &mut lamport).await;
    for (dir, seed, faults) in &schedule {
        if *dir {
            chaotic_push(&a, &b, *seed, faults).await;
        } else {
            chaotic_push(&b, &a, *seed, faults).await;
        }
        for e in [&a, &b] {
            let r = audit::audit(&e.store).await.map_err(|e| e.to_string())?;
            if !r.ok() || !r.uncertified_markers.is_empty() || !r.uncertified_tombstones.is_empty() {
                return Err(format!("audit during the exchange: {:?}", r.violations));
            }
        }
    }
    // Eventually every item is delivered intact (fairness): synchronise to a fixpoint.
    let (rounds, ..) = antientropy::sync(sync_of(&a), sync_of(&b), 12).await.map_err(|e| e.to_string())?;
    let (pa, pb): (PublishedSet, PublishedSet) = (published_set(&a.store).await.unwrap(), published_set(&b.store).await.unwrap());
    if pa != pb {
        return Err(format!("diverged after {rounds} rounds:\n{pa:?}\n{pb:?}"));
    }
    let groups: BTreeSet<Id> = ga.union(&gb).copied().collect();
    let tombs: BTreeSet<Id> = ta.union(&tb).copied().collect();
    if pa.groups.keys().copied().collect::<BTreeSet<_>>() != groups || pa.tombstones != tombs {
        return Err(format!("converged set is not the union: {pa:?}"));
    }
    audits_clean(&a, &b).await;
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(12),
        max_shrink_iters: 16,
        .. ProptestConfig::default()
    })]
    fn any_exchange_order_converges_to_the_union(
        a_acts in proptest::collection::vec(act(), 1..6),
        b_acts in proptest::collection::vec(act(), 1..6),
        schedule in proptest::collection::vec((any::<bool>(), any::<u64>(), proptest::collection::vec(delivery(), 0..6)), 0..5),
    ) {
        let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().unwrap();
        let r = rt.block_on(convergence_case(a_acts, b_acts, schedule));
        prop_assert!(r.is_ok(), "{}", r.unwrap_err());
    }
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("sync_converges_between_two_clusters", || { sync_converges_between_two_clusters(); Ok(()) }),
        libtest_mimic::Trial::test("receiver_rejects_corrupt_forged_and_untrusted", || { receiver_rejects_corrupt_forged_and_untrusted(); Ok(()) }),
        libtest_mimic::Trial::test("deferred_until_dependencies_arrive", || { deferred_until_dependencies_arrive(); Ok(()) }),
        libtest_mimic::Trial::test("receive_faults_resolve", || { receive_faults_resolve(); Ok(()) }),
        libtest_mimic::Trial::test("corrupt_payloads_at_rest_are_repaired_or_wait", || { corrupt_payloads_at_rest_are_repaired_or_wait(); Ok(()) }),
        libtest_mimic::Trial::test("marker_conflict_is_reported_not_overwritten", || { marker_conflict_is_reported_not_overwritten(); Ok(()) }),
        libtest_mimic::Trial::test("foreign_target_names_and_certificate_copies_refused", || { foreign_target_names_and_certificate_copies_refused(); Ok(()) }),
        libtest_mimic::Trial::test("received_groups_need_a_receipt_valid_here", || { received_groups_need_a_receipt_valid_here(); Ok(()) }),
        libtest_mimic::Trial::test("cancelled_request_is_not_received_by_its_issuer", || { cancelled_request_is_not_received_by_its_issuer(); Ok(()) }),
        libtest_mimic::Trial::test("received_group_waits_for_job_dependencies_here", || { received_group_waits_for_job_dependencies_here(); Ok(()) }),
        libtest_mimic::Trial::test("any_exchange_order_converges_to_the_union", || { any_exchange_order_converges_to_the_union(); Ok(()) }),
    ]);
}
