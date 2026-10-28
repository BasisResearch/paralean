//! Atomic multi-group publication (T12/T13; docs/atomic-pub-log.md), against the real
//! FoundationDB and Garage services: dependent members across two workspaces, whole-batch
//! rejection, crashes and unknown outcomes, discovery closure and anti-entropy.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::sync::Arc;

use common::*;
use paralean_store::antientropy::{self, Item, Outcome};
use paralean_store::recovery::{discover, discover_with};
use paralean_store::*;
use paralean_store::pce::Pce;

fn x() -> Name {
    Name::parse("Target.x")
}

fn group_of(tag: &str) -> Opaque {
    Opaque::new(Kind::Group, fixture::group_bytes(tag))
}

/// A package whose capsule is P1 group metadata (`declId`), so another job can name it as a
/// dependency, with the given job dependencies and batch binding.
#[allow(clippy::too_many_arguments)]
fn member(e: &Env, wi: usize, tag: &str, name: &str, parents: Vec<Id>, target: Option<PreparedTarget>,
    deps: Vec<Id>, batch: Option<Id>, lamport: u64) -> Package {
    let w = e.w[wi].id;
    let group = group_of(tag);
    let g = group.id();
    let capsule = Opaque::new(Kind::Capsule, serde_json::to_vec(&serde_json::json!({"declId": g.hex(), "tag": tag})).unwrap());
    let mut body = fixture::job_by(&e.authority(), tag, g, capsule.id(), w, target.as_slice()).body;
    body.deps = deps;
    body.batch = batch;
    let job = SignedJob::sign(body, &e.authority());
    let receipt = fixture::receipt_for(&job, &e.validator, Verdict::Accepted);
    let mut parents = parents;
    parents.sort();
    parents.dedup();
    let fresh = parents.is_empty();
    let rev = Revision { group: g, name: Name::parse(name), parents, capsule: capsule.id(), workspace: w };
    let author = AgentId::derive(&format!("agent/{}", w.hex()));
    let marker = Marker {
        group: g, revisions: vec![rev.id()], receipt: receipt.id(), file_path: "Test/File.lean".into(),
        anchor: Anchor::FileStart, lamport, author,
        root_path: if fresh { vec![(g, lamport, author)] } else { vec![] },
        lineage_keys: vec![(Name::parse(name), lamport, author)],
    };
    let chunks = vec![Opaque::new(Kind::Chunk, format!("chunk of {tag}").into_bytes())];
    Package { group, chunks, capsule, receipt, job, revisions: vec![rev], marker, targets: target.into_iter().collect() }
}

/// The pre-rename state: foo (workspace 0) and use (workspace 1, using foo), published
/// one at a time, plus g2 (workspace 1), which the renamed use also needs.
struct Before {
    foo: Package,
    use0: Package,
    g2: Package,
}

async fn before(e: &Env, publish_g2: bool) -> Before {
    let foo = member(e, 0, "foo", "Alice.foo", vec![], None, vec![], None, 1);
    e.w[0].publish(&foo).await.unwrap();
    let mut use0 = member(e, 1, "use", "Bob.use", vec![], None, vec![foo.capsule.id()], None, 2);
    fixture::place(&mut use0, "Test/File.lean", Some(&foo.marker), None);
    e.w[1].publish(&use0).await.unwrap();
    let g2 = member(e, 1, "g2", "Bob.g2", vec![], None, vec![], None, 3);
    if publish_g2 {
        e.w[1].publish(&g2).await.unwrap();
    } else {
        // Its payloads exist (the job names its capsule), its publication does not.
        for o in g2.chunks.iter().chain([&g2.group, &g2.capsule]) {
            e.store.s3.put_opaque(o).await.unwrap();
        }
    }
    Before { foo, use0, g2 }
}

/// The rename: bar replaces foo (workspace 0), foo's position is deleted, and use' revises
/// use to call bar (workspace 1). With `proof`, workspace 0 also publishes a proof of x.
struct Rename {
    pkg: BatchPackage,
    bar: Package,
    use2: Package,
    tomb: Tombstone,
    proof: Option<Package>,
}

async fn rename(e: &Env, b: &Before, proof: bool, request: &str) -> Rename {
    let (w0, w1) = (e.w[0].id, e.w[1].id);
    let pt = if proof { Some(e.w[0].prepare_target(&x()).await.unwrap()) } else { None };
    let mut members = Vec::new();
    if proof {
        members.push(BatchMember::Publish { group: group_of(&format!("proof-{request}")).id(), writer: w0 });
    }
    members.push(BatchMember::Publish { group: group_of(&format!("bar-{request}")).id(), writer: w0 });
    members.push(BatchMember::Tombstone { target: b.foo.group.id(), position: Some(b.foo.marker.id()), writer: w0 });
    members.push(BatchMember::Publish { group: group_of(&format!("use2-{request}")).id(), writer: w1 });
    let intent = SignedBatch::sign(BatchIntent { request: request.as_bytes().to_vec(), members }, &e.authority());
    let id = intent.id();
    let proof = pt.map(|pt| member(e, 0, &format!("proof-{request}"), "Target.x", pt.head.into_iter().collect(), Some(pt), vec![], Some(id), 4));
    let mut bar = member(e, 0, &format!("bar-{request}"), "Alice.bar", vec![], None, vec![], Some(id), 5);
    fixture::place(&mut bar, "Test/File.lean", Some(&b.foo.marker), None);
    let tomb = Tombstone {
        file_path: b.foo.marker.file_path.clone(), target: b.foo.group.id(), lamport: 6, author: b.foo.marker.author,
        receipt: None, position: Some(b.foo.marker.id()), batch: Some(id),
    };
    let mut use2 = member(e, 1, &format!("use2-{request}"), "Bob.use", vec![rev_id(&b.use0)], None,
        vec![bar.capsule.id(), b.g2.capsule.id()], Some(id), 7);
    fixture::place(&mut use2, "Test/File.lean", None, Some(&b.use0.marker));
    let mut items = Vec::new();
    if let Some(p) = &proof {
        items.push(BatchItem::Publish { package: p.clone(), writer: w0, cert: e.w[0].sign_batch_publication(p) });
    }
    items.push(BatchItem::Publish { package: bar.clone(), writer: w0, cert: e.w[0].sign_batch_publication(&bar) });
    items.push(BatchItem::Tombstone { tombstone: tomb.clone(), writer: w0, cert: e.w[0].sign_batch_tombstone(&tomb), grant: None });
    items.push(BatchItem::Publish { package: use2.clone(), writer: w1, cert: e.w[1].sign_batch_publication(&use2) });
    Rename { pkg: BatchPackage { intent, items }, bar, use2, tomb, proof }
}

/// What a reader can see of the rename: published groups and tombstones.
async fn visible(e: &Env, r: &Rename) -> (usize, usize) {
    let d = discover(&e.store).await.unwrap();
    let mut groups: Vec<Id> = vec![r.bar.group.id(), r.use2.group.id()];
    groups.extend(r.proof.iter().map(|p| p.group.id()));
    let g = groups.iter().filter(|g| d.groups.contains_key(g)).count();
    let t = usize::from(d.tombstones.contains_key(&r.tomb.id()));
    (g + t, groups.len() + 1)
}

/// The deployment's anti-entropy event log, in commit order.
async fn ae_events(st: &Store) -> Vec<AeKind> {
    st.meta.scan(&st.meta.keys.ae_log(), 500, |_| None).await.unwrap().into_iter()
        .map(|(_, v)| AeKind::from_pce(&v).unwrap()).collect()
}

async fn assert_none(e: &Env, r: &Rename) {
    let (seen, _) = visible(e, r).await;
    assert_eq!(seen, 0, "a rejected or uncommitted batch exposes none of its members");
    for p in [&r.bar, &r.use2].into_iter().chain(r.proof.iter()) {
        assert!(e.store.marker(&p.group.id()).await.unwrap().is_none(), "no member marker");
        assert!(e.store.certs(&p.group.id()).await.unwrap().is_empty(), "no member certificate");
    }
    assert!(e.store.tombstone(&r.tomb.id()).await.unwrap().is_none(), "no member tombstone");
    assert!(e.store.batch(&r.pkg.intent.id()).await.unwrap().is_none(), "no batch record");
}

async fn assert_all(e: &Env, r: &Rename) {
    let (seen, total) = visible(e, r).await;
    assert_eq!(seen, total, "a committed batch exposes every member");
    let rec = e.store.batch(&r.pkg.intent.id()).await.unwrap().expect("batch record");
    assert_eq!(rec.entries.len(), total);
}

// ------------------------------------------------------------------ T12

#[tokio::main(flavor = "current_thread")]
async fn batch_publishes_dependent_members_across_workspaces() {
    let e = Env::new("bdeps", 2);
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let b = before(&e, true).await;
    let r = rename(&e, &b, true, "r1").await;
    let out = e.store.publish_batch(&r.pkg).await.unwrap();
    assert!(out.fresh);
    assert_all(&e, &r).await;
    // Each member carries its own writer's certificate.
    for (g, w) in [(r.bar.group.id(), e.w[0].id), (r.use2.group.id(), e.w[1].id)] {
        let writers: Vec<WorkspaceId> = e.store.certs(&g).await.unwrap().iter().map(|c| c.body.writer).collect();
        assert_eq!(writers, vec![w]);
    }
    assert_eq!(e.store.tcerts(&r.tomb.id()).await.unwrap().len(), 1);
    // The proof advanced the target head under the owner's epoch.
    let proof = r.proof.as_ref().unwrap();
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(proof)));
    // Readers see the rename: foo is deleted, use is superseded by use', bar renders.
    let d = discover(&e.store).await.unwrap();
    assert!(d.batches.contains_key(&r.pkg.intent.id()));
    let file = &d.files["Test/File.lean"];
    assert!(file.contains(&r.bar.group.id()) && file.contains(&r.use2.group.id()));
    assert!(!file.contains(&b.foo.group.id()) && !file.contains(&b.use0.group.id()), "{file:?}");
    // One anti-entropy event carries the whole batch.
    let events = ae_events(&e.store).await;
    let kinds: Vec<&AeKind> = events.iter().collect();
    assert!(kinds.contains(&&AeKind::Batch { id: r.pkg.intent.id() }));
    assert!(!kinds.iter().any(|k| matches!(k, AeKind::GroupVariant { group, .. } if *group == r.bar.group.id() || *group == r.use2.group.id())));
    assert!(!kinds.iter().any(|k| matches!(k, AeKind::Tombstone { id, .. } if *id == r.tomb.id())));
    // Idempotent as a whole.
    let again = e.store.publish_batch(&r.pkg).await.unwrap();
    assert!(!again.fresh);
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn stale_owner_on_one_member_rejects_the_whole_batch() {
    let e = Env::new("bstale", 2);
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let b = before(&e, true).await;
    // The owner changes after the coordinator read the record: the proof is stale.
    let r = rename(&e, &b, true, "r1").await;
    e.ctl.reassign(&x(), e.w[1].id, b"assign-1").await.unwrap();
    let g = guard_of(e.store.publish_batch(&r.pkg).await);
    assert!(matches!(g, GuardFailure::NotOwner { .. }), "{g:?}");
    assert_none(&e, &r).await;
    // The same owner at a newer epoch: the epoch fence alone rejects it.
    let r2 = {
        e.ctl.reassign(&x(), e.w[0].id, b"assign-2").await.unwrap();
        rename(&e, &b, true, "r2").await
    };
    e.ctl.reassign(&x(), e.w[0].id, b"assign-3").await.unwrap();
    let g = guard_of(e.store.publish_batch(&r2.pkg).await);
    assert!(matches!(g, GuardFailure::StaleEpoch { .. }), "{g:?}");
    assert_none(&e, &r2).await;
    // A head published meanwhile fails the compare-and-swap.
    let r3 = rename(&e, &b, true, "r3").await;
    e.publish_target(0, &x(), "competing").await.unwrap();
    let g = guard_of(e.store.publish_batch(&r3.pkg).await);
    assert!(matches!(g, GuardFailure::HeadMoved { .. }), "{g:?}");
    assert_none(&e, &r3).await;
    // foo and use are untouched.
    let d = discover(&e.store).await.unwrap();
    let file = &d.files["Test/File.lean"];
    assert!(file.contains(&b.foo.group.id()) && file.contains(&b.use0.group.id()));
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn any_failing_member_rejects_the_whole_batch() {
    let e = Env::new("bfail", 2);
    // use' needs g2, which is not published: the last member fails after two passed.
    let b = before(&e, false).await;
    let r = rename(&e, &b, false, "r1").await;
    let g = guard_of(e.store.publish_batch(&r.pkg).await);
    assert!(matches!(g, GuardFailure::NotPublished(_) | GuardFailure::Uncertified(_)), "{g:?}");
    assert_none(&e, &r).await;
    // Once g2 is published the same batch commits.
    e.w[1].publish(&b.g2).await.unwrap();
    assert!(e.store.publish_batch(&r.pkg).await.unwrap().fresh);
    assert_all(&e, &r).await;
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn members_are_bound_to_their_batch() {
    let e = Env::new("bbound", 2);
    let b = before(&e, true).await;
    let r = rename(&e, &b, false, "r1").await;
    // No member publishes alone: T1 and T8 refuse batch-bound envelopes and tombstones.
    assert!(matches!(guard_of(e.w[0].publish(&r.bar).await), GuardFailure::BatchBinding(_)));
    assert!(matches!(guard_of(e.w[1].publish(&r.use2).await), GuardFailure::BatchBinding(_)));
    assert!(matches!(guard_of(e.w[0].tombstone(&r.tomb).await), GuardFailure::BatchBinding(_)));
    assert_none(&e, &r).await;
    // Another batch cannot take them either.
    let mut other = r.pkg.clone();
    other.intent = SignedBatch::sign(BatchIntent { request: b"other".to_vec(), members: r.pkg.intent.body.members.clone() }, &e.authority());
    assert!(matches!(guard_of(e.store.publish_batch(&other).await), GuardFailure::BatchBinding(_)));
    // The intent must be signed by the controller or a job issuer.
    let mut forged = r.pkg.clone();
    forged.intent = SignedBatch::sign(r.pkg.intent.body.clone(), &Signer::derive("rogue-controller"));
    assert!(matches!(guard_of(e.store.publish_batch(&forged).await), GuardFailure::BatchIntent(_)));
    // Members must be exactly the signed ones, in order.
    let mut reordered = r.pkg.clone();
    reordered.items.swap(0, 2);
    assert!(guard_of(e.store.publish_batch(&reordered).await) != GuardFailure::BatchConflict(r.pkg.intent.id()));
    let mut dropped = r.pkg.clone();
    dropped.items.pop();
    assert!(matches!(guard_of(e.store.publish_batch(&dropped).await), GuardFailure::BatchIntent(_)));
    // Each member's certificate is its own writer's: the coordinator cannot sign for one.
    let mut forged_cert = r.pkg.clone();
    if let BatchItem::Publish { cert, package, .. } = &mut forged_cert.items[2] {
        *cert = Cert::sign(CertBody { replica: e.store.replica, marker: package.marker.id(), group: package.group.id(), writer: e.w[1].id },
            &Signer::derive("coordinator"));
    }
    assert!(matches!(guard_of(e.store.publish_batch(&forged_cert).await), GuardFailure::BadPackage(_)));
    assert_none(&e, &r).await;
    // The genuine batch still commits.
    e.store.publish_batch(&r.pkg).await.unwrap();
    assert_all(&e, &r).await;
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn crash_mid_batch_exposes_nothing_and_retries() {
    for (label, at, skip) in [("member", "batch:after-member", 1), ("payload", "batch:after-payload", 0), ("commit", "batch:before-commit", 0)] {
        let faults = Faults::none();
        let e = Env::with_faults(&format!("bcrash-{label}"), 2, faults.clone());
        let b = before(&e, true).await;
        let r = rename(&e, &b, false, "r1").await;
        faults.crash_at(at, skip);
        assert!(e.store.publish_batch(&r.pkg).await.unwrap_err().is_crash(), "{label}");
        assert_none(&e, &r).await;
        faults.clear_rules();
        assert!(e.store.publish_batch(&r.pkg).await.unwrap().fresh, "{label}");
        assert_all(&e, &r).await;
        e.audit_ok().await;
    }
    // The coordinator dies around the commit itself.
    for (label, fault, committed) in [("before", CommitFault::CrashBeforeCommit, false), ("after", CommitFault::CrashAfterCommit, true)] {
        let faults = Faults::none();
        let e = Env::with_faults(&format!("bcommit-{label}"), 2, faults.clone());
        let b = before(&e, true).await;
        let r = rename(&e, &b, false, "r1").await;
        faults.on_commit(Some(Txn::T12PublishBatch), 0, fault);
        assert!(e.store.publish_batch(&r.pkg).await.unwrap_err().is_crash());
        if committed { assert_all(&e, &r).await } else { assert_none(&e, &r).await }
        faults.clear_rules();
        let again = e.store.publish_batch(&r.pkg).await.unwrap();
        assert_eq!(again.fresh, !committed, "{label}: the retry finds the batch record");
        assert_all(&e, &r).await;
        e.audit_ok().await;
    }
}

#[tokio::main(flavor = "current_thread")]
async fn unknown_commit_outcome_resolves_to_the_truth() {
    // Lost reply: the retry reads the record and reports the batch as already committed.
    let faults = Faults::none();
    let e = Env::with_faults("bunk-c", 2, faults.clone());
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let b = before(&e, true).await;
    let r = rename(&e, &b, true, "r1").await;
    faults.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownCommitted);
    let out = e.store.publish_batch(&r.pkg).await.unwrap();
    assert!(!out.fresh, "resolved by reading the committed record");
    assert_all(&e, &r).await;
    assert_eq!(e.store.target(&x()).await.unwrap().unwrap().head, Some(rev_id(r.proof.as_ref().unwrap())));
    // Not committed: the retry re-checks every guard and commits.
    let faults = Faults::none();
    let e = Env::with_faults("bunk-n", 2, faults.clone());
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let b = before(&e, true).await;
    let r = rename(&e, &b, true, "r1").await;
    faults.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownNotCommitted);
    assert!(e.store.publish_batch(&r.pkg).await.unwrap().fresh);
    assert_all(&e, &r).await;
    // Not committed, then the owner changes before the retry: the retry is rejected whole.
    let faults = Faults::none();
    let e = Env::with_faults("bunk-r", 2, faults.clone());
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let b = before(&e, true).await;
    let r = rename(&e, &b, true, "r1").await;
    faults.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownThen {
        committed: false, hook: reassign_hook(&e.ctl, x(), e.w[1].id, "assign-1") });
    let g = guard_of(e.store.publish_batch(&r.pkg).await);
    assert!(matches!(g, GuardFailure::NotOwner { .. }), "{g:?}");
    assert_none(&e, &r).await;
    // Committed, then the owner changes: the retry finds the record, not the new owner.
    let faults = Faults::none();
    let e = Env::with_faults("bunk-cr", 2, faults.clone());
    e.ctl.reassign(&x(), e.w[0].id, b"assign-0").await.unwrap();
    let b = before(&e, true).await;
    let r = rename(&e, &b, true, "r1").await;
    faults.on_commit(Some(Txn::T12PublishBatch), 0, CommitFault::UnknownThen {
        committed: true, hook: reassign_hook(&e.ctl, x(), e.w[1].id, "assign-1") });
    assert!(!e.store.publish_batch(&r.pkg).await.unwrap().fresh);
    assert_all(&e, &r).await;
    let rec = e.store.target(&x()).await.unwrap().unwrap();
    assert_eq!((rec.owner, rec.head), (e.w[1].id, Some(rev_id(r.proof.as_ref().unwrap()))));
    e.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn paginated_discovery_never_sees_part_of_a_batch() {
    let e = Env::new("bscan", 2);
    let b = before(&e, true).await;
    for i in 0..24 {
        e.w[i % 2].publish(&e.plain_package(i % 2, &format!("N.filler{i}"), &format!("filler{i}"))).await.unwrap();
    }
    let r = rename(&e, &b, false, "r1").await;
    // Commit after the certificate scan has passed all but the last existing key: at least
    // one member's certificate falls before the resume point (else add fillers), and the
    // tombstone scan, which runs later, sees the deletion.
    let cert_keys = |g: Id, w: WorkspaceId| e.store.meta.keys.cert(&g, &w);
    let existing: Vec<Vec<u8>> = {
        let mut v: Vec<Vec<u8>> = e.store.meta.scan(&e.store.meta.keys.sub("cert"), 500, |_| None).await.unwrap().into_iter().map(|(k, _)| k).collect();
        v.sort();
        v
    };
    let members = [cert_keys(r.bar.group.id(), e.w[0].id), cert_keys(r.use2.group.id(), e.w[1].id)];
    let fire = existing.len() - 1;
    assert!(members.iter().any(|k| *k < existing[fire - 1]), "fixture: a member key must precede the resume point");
    let mut paged = e.store.clone();
    paged.page = 1;
    let (store, pkg) = (e.store.clone(), r.pkg.clone());
    let d = discover_with(&paged, move |n| {
        (n == fire).then(|| {
            let (store, pkg) = (store.clone(), pkg.clone());
            Box::pin(async move { store.publish_batch(&pkg).await.unwrap(); }) as futures::future::BoxFuture<'static, ()>
        })
    }).await.unwrap();
    let seen = usize::from(d.groups.contains_key(&r.bar.group.id())) + usize::from(d.groups.contains_key(&r.use2.group.id()))
        + usize::from(d.tombstones.contains_key(&r.tomb.id()));
    assert_eq!(seen, 3, "discovery closes its view under batches");
    assert!(d.batches.contains_key(&r.pkg.intent.id()));
    e.audit_ok().await;
}

/// Rebuild one publication member after changing it, with its writer's fresh certificate.
fn replace_member(e: &Env, r: &mut Rename, at: usize, wi: usize, p: Package) {
    r.pkg.items[at] = BatchItem::Publish { cert: e.w[wi].sign_batch_publication(&p), package: p, writer: e.w[wi].id };
}

#[tokio::main(flavor = "current_thread")]
async fn every_member_guard_applies_inside_a_batch() {
    // A revoked validator: T1's in-transaction revocation read.
    let e = Env::new("bguard-revoke", 2);
    let b = before(&e, true).await;
    let r = rename(&e, &b, false, "r1").await;
    e.revoke(e.validator.public()).await;
    assert!(matches!(guard_of(e.store.publish_batch(&r.pkg).await), GuardFailure::ValidatorRevoked(_)));
    assert_none(&e, &r).await;
    // A cancelled request of the last member.
    let e = Env::new("bguard-cancel", 2);
    let b = before(&e, true).await;
    let r = rename(&e, &b, false, "r1").await;
    e.store.meta.cancel_job(&e.w[1].id, &r.use2.job.body.request).await.unwrap();
    assert!(matches!(guard_of(e.store.publish_batch(&r.pkg).await), GuardFailure::JobCancelled(_)));
    assert_none(&e, &r).await;
    // A revoked agent key of the second workspace.
    let e = Env::new("bguard-agent", 2);
    let b = before(&e, true).await;
    let r = rename(&e, &b, false, "r1").await;
    e.ctl.revoke_agent_key(e.w[1].signer().public()).await.unwrap();
    assert!(matches!(guard_of(e.store.publish_batch(&r.pkg).await), GuardFailure::AgentKeyRevoked(_)));
    assert_none(&e, &r).await;
    // W3: only foo's author deletes its position, even inside a batch.
    let e = Env::new("bguard-author", 2);
    let b = before(&e, true).await;
    let mut r = rename(&e, &b, false, "r1").await;
    let (w1, id) = (e.w[1].id, r.pkg.intent.id());
    let mut members = r.pkg.intent.body.members.clone();
    members[1] = BatchMember::Tombstone { target: b.foo.group.id(), position: Some(b.foo.marker.id()), writer: w1 };
    r.pkg.intent = SignedBatch::sign(BatchIntent { request: b"r1".to_vec(), members }, &e.authority());
    assert_eq!(r.pkg.intent.id() == id, false);
    let id = r.pkg.intent.id();
    let rebind = |e: &Env, p: &Package, wi: usize, tag: &str, name: &str, parents: Vec<Id>, deps: Vec<Id>, lamport: u64| {
        let mut q = member(e, wi, tag, name, parents, None, deps, Some(id), lamport);
        q.marker = Marker { receipt: q.receipt.id(), revisions: q.marker.revisions.clone(), ..p.marker.clone() };
        q
    };
    let bar = rebind(&e, &r.bar, 0, "bar-r1", "Alice.bar", vec![], vec![], 5);
    let use2 = rebind(&e, &r.use2, 1, "use2-r1", "Bob.use", vec![rev_id(&b.use0)], vec![bar.capsule.id(), b.g2.capsule.id()], 7);
    replace_member(&e, &mut r, 0, 0, bar.clone());
    replace_member(&e, &mut r, 2, 1, use2.clone());
    let tomb = Tombstone { author: AgentId::derive(&format!("agent/{}", w1.hex())), batch: Some(id), ..r.tomb.clone() };
    r.pkg.items[1] = BatchItem::Tombstone { cert: e.w[1].sign_batch_tombstone(&tomb), tombstone: tomb.clone(), writer: w1, grant: None };
    (r.bar, r.use2, r.tomb) = (bar, use2, tomb);
    assert_eq!(guard_of(e.store.publish_batch(&r.pkg).await), GuardFailure::TombstoneNotAuthor);
    assert_none(&e, &r).await;
}

#[tokio::main(flavor = "current_thread")]
async fn checkpoints_never_mix_a_batch_with_what_it_replaces() {
    let e = Env::new("bckpt", 2);
    let b = before(&e, true).await;
    let r = rename(&e, &b, false, "r1").await;
    let token = e.ctl.rotate(e.w[1].id, b"bckpt-fence").await.unwrap();
    // Before the rename, use and foo form a current checkpoint.
    let old = fixture::checkpoint(e.w[1].id, vec![rev_id(&b.use0), rev_id(&b.foo)], None, token, "old");
    e.w[1].commit_checkpoint(&old).await.unwrap();
    e.store.publish_batch(&r.pkg).await.unwrap();
    // After it, use is superseded: a checkpoint of it is stale (W3's currentness, read in
    // T5's own transaction, so it sees all of the batch or none).
    let stale = fixture::checkpoint(e.w[1].id, vec![rev_id(&b.use0), rev_id(&b.foo)], None, token, "stale");
    assert!(matches!(guard_of(e.w[1].commit_checkpoint(&stale).await), GuardFailure::CheckpointNotCurrent { .. }));
    let mixed = fixture::checkpoint(e.w[1].id, vec![rev_id(&b.use0), rev_id(&b.foo), rev_id(&r.bar)], None, token, "mixed");
    let g = guard_of(e.w[1].commit_checkpoint(&mixed).await);
    assert!(matches!(g, GuardFailure::CheckpointNotCurrent { .. }), "{g:?}");
    // The renamed state commits.
    let new = fixture::checkpoint(e.w[1].id, vec![rev_id(&r.use2), rev_id(&r.bar), rev_id(&b.g2)], None, token, "new");
    e.w[1].commit_checkpoint(&new).await.unwrap();
    e.audit_ok().await;
}

// ------------------------------------------------------------------ T13

#[tokio::main(flavor = "current_thread")]
async fn anti_entropy_transfers_a_batch_atomically() {
    let (a, b) = pair("bae", 2, Faults::none(), Faults::none());
    let pre = before(&a, true).await;
    let r = rename(&a, &pre, false, "r1").await;
    a.store.publish_batch(&r.pkg).await.unwrap();
    let items = antientropy::export(&a.store).await.unwrap();
    let batch = items.iter().find(|i| matches!(i, Item::Batch { .. })).expect("the batch is one export item").clone();
    assert!(!items.iter().any(|i| matches!(i, Item::Group { marker, .. }
        if Marker::from_preimage(marker).unwrap().group == r.bar.group.id())), "members travel only inside the batch");
    let sync = b.w[1].clone();
    // Payloads and foo/use first, but not g2: use' cannot be applied, so nothing is.
    let g2_marker = pre.g2.marker.id();
    for item in &items {
        match item {
            Item::Object { .. } => { antientropy::import(&sync, item).await.unwrap(); }
            Item::Group { marker, .. } if Marker::from_preimage(marker).unwrap().id() != g2_marker => {
                assert_eq!(antientropy::import(&sync, item).await.unwrap(), Outcome::Applied);
            }
            _ => {}
        }
    }
    assert!(matches!(antientropy::import(&sync, &batch).await.unwrap(), Outcome::Deferred(_)));
    let db = discover(&b.store).await.unwrap();
    assert!(!db.groups.contains_key(&r.bar.group.id()) && !db.tombstones.contains_key(&r.tomb.id()),
        "a deferred batch exposes none of its members at the receiver");
    assert!(b.store.batch(&r.pkg.intent.id()).await.unwrap().is_none());
    // A member offered alone is refused: T9 admits it only inside its batch.
    let Item::Batch { members, .. } = &batch else { unreachable!() };
    let outcome = antientropy::import(&sync, &members[0]).await.unwrap();
    assert!(matches!(outcome, Outcome::Rejected(_)), "{outcome:?}");
    assert!(b.store.marker(&r.bar.group.id()).await.unwrap().is_none());
    // A full round applies the whole batch in one transaction.
    let (_, ab, _) = antientropy::sync((&a.store, &a.w[1]), (&b.store, &sync), 4).await.unwrap();
    assert!(ab.rejected.is_empty(), "{:?}", ab.rejected);
    let db = discover(&b.store).await.unwrap();
    assert!(db.groups.contains_key(&r.bar.group.id()) && db.groups.contains_key(&r.use2.group.id()) && db.tombstones.contains_key(&r.tomb.id()));
    assert!(db.batches.contains_key(&r.pkg.intent.id()));
    assert_eq!(antientropy::published_set(&a.store).await.unwrap(), antientropy::published_set(&b.store).await.unwrap());
    // The receiver relays it as one event too, and a second copy is present.
    assert!(ae_events(&b.store).await.contains(&AeKind::Batch { id: r.pkg.intent.id() }));
    assert_eq!(antientropy::import(&sync, &batch).await.unwrap(), Outcome::Present);
    a.audit_ok().await;
    b.audit_ok().await;
}

#[tokio::main(flavor = "current_thread")]
async fn anti_entropy_batch_unknown_outcome_and_crash() {
    for (label, fault, crash) in [
        ("unknown-committed", CommitFault::UnknownCommitted, false),
        ("unknown-lost", CommitFault::UnknownNotCommitted, false),
        ("crash-before", CommitFault::CrashBeforeCommit, true),
    ] {
        let fb = Faults::none();
        let (a, b) = pair(&format!("baef-{label}"), 2, Faults::none(), fb.clone());
        let pre = before(&a, true).await;
        let r = rename(&a, &pre, false, "r1").await;
        a.store.publish_batch(&r.pkg).await.unwrap();
        let items = antientropy::export(&a.store).await.unwrap();
        let sync = b.w[1].clone();
        fb.on_commit(Some(Txn::T13ReceiveBatch), 0, fault);
        let mut crashed = false;
        for item in &items {
            match antientropy::import(&sync, item).await {
                Ok(_) => {}
                Err(e) if crash && e.is_crash() => crashed = true,
                Err(e) => panic!("{label}: {e:?}"),
            }
        }
        let db = discover(&b.store).await.unwrap();
        let seen = usize::from(db.groups.contains_key(&r.bar.group.id())) + usize::from(db.groups.contains_key(&r.use2.group.id()))
            + usize::from(db.tombstones.contains_key(&r.tomb.id()));
        assert!(seen == 0 || seen == 3, "{label}: partial batch at the receiver");
        assert_eq!(crashed, crash, "{label}");
        fb.clear_rules();
        antientropy::sync((&a.store, &a.w[1]), (&b.store, &sync), 4).await.unwrap();
        assert_eq!(antientropy::published_set(&a.store).await.unwrap(), antientropy::published_set(&b.store).await.unwrap(), "{label}");
        b.audit_ok().await;
    }
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    let _ = Arc::new(());
    common::run_tests(vec![
        libtest_mimic::Trial::test("batch_publishes_dependent_members_across_workspaces", || { batch_publishes_dependent_members_across_workspaces(); Ok(()) }),
        libtest_mimic::Trial::test("stale_owner_on_one_member_rejects_the_whole_batch", || { stale_owner_on_one_member_rejects_the_whole_batch(); Ok(()) }),
        libtest_mimic::Trial::test("any_failing_member_rejects_the_whole_batch", || { any_failing_member_rejects_the_whole_batch(); Ok(()) }),
        libtest_mimic::Trial::test("members_are_bound_to_their_batch", || { members_are_bound_to_their_batch(); Ok(()) }),
        libtest_mimic::Trial::test("crash_mid_batch_exposes_nothing_and_retries", || { crash_mid_batch_exposes_nothing_and_retries(); Ok(()) }),
        libtest_mimic::Trial::test("unknown_commit_outcome_resolves_to_the_truth", || { unknown_commit_outcome_resolves_to_the_truth(); Ok(()) }),
        libtest_mimic::Trial::test("paginated_discovery_never_sees_part_of_a_batch", || { paginated_discovery_never_sees_part_of_a_batch(); Ok(()) }),
        libtest_mimic::Trial::test("every_member_guard_applies_inside_a_batch", || { every_member_guard_applies_inside_a_batch(); Ok(()) }),
        libtest_mimic::Trial::test("checkpoints_never_mix_a_batch_with_what_it_replaces", || { checkpoints_never_mix_a_batch_with_what_it_replaces(); Ok(()) }),
        libtest_mimic::Trial::test("anti_entropy_transfers_a_batch_atomically", || { anti_entropy_transfers_a_batch_atomically(); Ok(()) }),
        libtest_mimic::Trial::test("anti_entropy_batch_unknown_outcome_and_crash", || { anti_entropy_batch_unknown_outcome_and_crash(); Ok(()) }),
    ]);
}
