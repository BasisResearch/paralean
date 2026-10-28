// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;

use std::sync::Arc;

use common::*;
use paralean_store::recovery::{discover, live};
use paralean_store::*;

const F: &str = "Test/Positions.lean";

#[tokio::main(flavor = "current_thread")]
async fn certified_move_preserves_registry_and_converges_with_tombstone() {
    let e = Env::new("position-move", 1);
    let mut p = fixture::package("move", e.w[0].id, &e.validator,
        &Name::parse("Pos.move"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.anchor = Anchor::FileStart;
    moved.root_path = vec![(moved.group, moved.lamport, moved.author)];
    assert!(e.w[0].move_position(&moved, &old).await.unwrap());
    assert!(!e.w[0].move_position(&moved, &old).await.unwrap());
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.positions.len(), 2);
    assert_eq!(d.files[F], vec![p.group.id()]);
    assert!(live(&d, &p.group.id()));
    assert_eq!(d.heads[&Name::parse("Pos.move")], vec![p.revisions[0].id()]);
    assert_eq!(d.groups.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn tombstone_position_preimage_preserves_legacy_bytes() {
    let m = fixture::package("legacy", WorkspaceId::derive("legacy"),
        &paralean_store::sign::Signer::derive("legacy-validator"),
        &Name::parse("Pos.legacy"), vec![], None, 1).marker;
    let mut old = fixture::tombstone_of(&m, 2);
    old.position = None;
    let encoded = old.preimage();
    assert_eq!(Tombstone::from_preimage(&encoded).unwrap(), old);
    let positioned = fixture::tombstone_of(&m, 2);
    assert_eq!(Tombstone::from_preimage(&positioned.preimage()).unwrap(), positioned);
    assert_ne!(old.id(), positioned.id());
}

#[tokio::main(flavor = "current_thread")]
async fn move_rejects_uncertified_tombstone() {
    let e = Env::new("position-uncertified", 1);
    let mut p = fixture::package("uncertified", e.w[0].id, &e.validator,
        &Name::parse("Pos.uncertified"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    let value = e.store.stage_value(old.id(), old.preimage()).await.unwrap();
    e.store.meta.raw_set(e.store.meta.keys.tombstone(&old.id()), value).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, moved.lamport, moved.author)];
    assert!(e.w[0].move_position(&moved, &old).await.is_err());
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.positions.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn rendered_name_uses_lineage_winner_and_moves_derived_namespace() {
    let e = Env::new("position-names", 2);
    let mut winner = fixture::package("name-a", e.w[0].id, &e.validator,
        &Name::parse("Pos.T"), vec![], None, 1);
    fixture::place(&mut winner, F, None, None);
    e.w[0].publish(&winner).await.unwrap();
    let mut loser = fixture::package("name-b", e.w[1].id, &e.validator,
        &Name::parse("Pos.T"), vec![], None, 2);
    fixture::place(&mut loser, F, None, None);
    let mut derived = loser.revisions[0].clone();
    derived.name = Name::parse("Pos.T.mk");
    loser.marker.revisions.push(derived.id());
    loser.marker.revisions.sort();
    loser.marker.lineage_keys.push((derived.name.clone(), 2, loser.marker.author));
    loser.revisions.push(derived);
    e.w[1].publish(&loser).await.unwrap();
    let d = discover(&e.store).await.unwrap();
    let g = loser.group.id();
    assert_eq!(d.rendered_names[&(winner.group.id(), Name::parse("Pos.T"))], Name::parse("Pos.T"));
    assert_eq!(d.rendered_names[&(g, Name::parse("Pos.T"))], Name::parse(&format!("Pos.T✝pl{}", g.hex())));
    assert_eq!(d.rendered_names[&(g, Name::parse("Pos.T.mk"))],
        Name::parse(&format!("Pos.T✝pl{}.mk", g.hex())));
    // Deleting the winner changes the projection only; the registry still
    // records both revisions as conflicting heads.
    e.w[0].tombstone(&fixture::tombstone_of(&winner.marker, 3)).await.unwrap();
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.rendered_names[&(g, Name::parse("Pos.T"))], Name::parse("Pos.T"));
    assert_eq!(d.conflicts, vec![Name::parse("Pos.T")]);
}

#[tokio::main(flavor = "current_thread")]
async fn move_rejects_forged_root_path() {
    let e = Env::new("position-root", 1);
    let mut p = fixture::package("root", e.w[0].id, &e.validator,
        &Name::parse("Pos.root"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, 999, moved.author)];
    assert!(e.w[0].move_position(&moved, &old).await.is_err());
    assert_eq!(discover(&e.store).await.unwrap().positions.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn move_rejects_uncertified_anchor() {
    let e = Env::new("position-anchor", 1);
    let mut p = fixture::package("anchor", e.w[0].id, &e.validator,
        &Name::parse("Pos.anchor"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.anchor = Anchor::After(Id([9; 32]));
    moved.root_path = vec![(Id([9; 32]), 1, moved.author), (moved.group, 3, moved.author)];
    assert!(e.w[0].move_position(&moved, &old).await.is_err());
    assert_eq!(discover(&e.store).await.unwrap().positions.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn move_rejects_changed_lineage() {
    let e = Env::new("position-lineage", 1);
    let mut p = fixture::package("lineage", e.w[0].id, &e.validator,
        &Name::parse("Pos.lineage"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, moved.lamport, moved.author)];
    moved.lineage_keys[0].1 += 1;
    assert!(e.w[0].move_position(&moved, &old).await.is_err());
    assert_eq!(discover(&e.store).await.unwrap().positions.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn move_rejects_cross_file_placement() {
    let e = Env::new("position-cross-file", 1);
    let mut p = fixture::package("cross-file", e.w[0].id, &e.validator,
        &Name::parse("Pos.crossFile"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.file_path = "Test/Elsewhere.lean".into();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, moved.lamport, moved.author)];
    assert!(e.w[0].move_position(&moved, &old).await.is_err());
    assert_eq!(discover(&e.store).await.unwrap().positions.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn controller_deleted_position_cannot_be_reinserted_by_author() {
    let e = Env::new("position-controller-author", 1);
    let mut p = fixture::package("controller-author", e.w[0].id, &e.validator,
        &Name::parse("Pos.controllerDeleted"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let mut old = fixture::tombstone_of(&p.marker, 2);
    old.author = controller_agent_id(&e.store.ring.authority);
    let grant = e.ctl.deletion_grant(&old).await.unwrap();
    e.w[0].tombstone_authorized(&old, Some(grant)).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, moved.lamport, moved.author)];
    assert!(e.w[0].move_position(&moved, &old).await.is_err());
    assert_eq!(discover(&e.store).await.unwrap().positions.len(), 1);
}

#[tokio::main(flavor = "current_thread")]
async fn unknown_committed_move_retries_after_agent_revocation() {
    let e = Env::new("position-unknown-revoked", 1);
    let mut p = fixture::package("unknown-revoked", e.w[0].id, &e.validator,
        &Name::parse("Pos.unknownRevoked"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.root_path = vec![(moved.group, moved.lamport, moved.author)];
    let faults = Faults::none();
    let ctl = e.ctl.clone();
    let public = e.w[0].signer().public();
    faults.on_commit(Some(Txn::T11MovePosition), 0, CommitFault::UnknownThen {
        committed: true,
        hook: Arc::new(move || {
            let ctl = ctl.clone();
            Box::pin(async move { ctl.revoke_agent_key(public).await.unwrap(); })
        }),
    });
    let interrupted = e.writer_with(0, faults.clone());
    assert!(!interrupted.move_position(&moved, &old).await.unwrap());
    assert_eq!(e.store.marker_variant(&p.group.id(), &moved.id()).await.unwrap(), Some(moved.clone()));
    assert!(!e.w[0].move_position(&moved, &old).await.unwrap());
    let mut fresh = moved;
    fresh.lamport = 4;
    fresh.root_path = vec![(fresh.group, fresh.lamport, fresh.author)];
    assert_eq!(guard_of(e.w[0].move_position(&fresh, &old).await), GuardFailure::AgentKeyRevoked(public));
}

#[tokio::main(flavor = "current_thread")]
async fn committed_anchored_move_retries_after_anchor_tombstone() {
    let e = Env::new("position-anchor-retry", 1);
    let mut anchor = fixture::package("anchor-retry-anchor", e.w[0].id, &e.validator,
        &Name::parse("Pos.anchorRetryAnchor"), vec![], None, 1);
    fixture::place(&mut anchor, F, None, None);
    e.w[0].publish(&anchor).await.unwrap();
    let mut p = fixture::package("anchor-retry-move", e.w[0].id, &e.validator,
        &Name::parse("Pos.anchorRetryMove"), vec![], None, 1);
    fixture::place(&mut p, F, None, None);
    e.w[0].publish(&p).await.unwrap();
    let old = fixture::tombstone_of(&p.marker, 2);
    e.w[0].tombstone(&old).await.unwrap();
    let mut moved = p.marker.clone();
    moved.lamport = 3;
    moved.anchor = Anchor::After(anchor.group.id());
    moved.root_path = anchor.marker.root_path.clone();
    moved.root_path.push((moved.group, moved.lamport, moved.author));
    assert!(e.w[0].move_position(&moved, &old).await.unwrap());
    e.w[0].tombstone(&fixture::tombstone_of(&anchor.marker, 4)).await.unwrap();
    assert!(!e.w[0].move_position(&moved, &old).await.unwrap());
    let d = discover(&e.store).await.unwrap();
    assert_eq!(d.files[F], vec![p.group.id()]);
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("certified_move_preserves_registry_and_converges_with_tombstone", || { certified_move_preserves_registry_and_converges_with_tombstone(); Ok(()) }),
        libtest_mimic::Trial::test("tombstone_position_preimage_preserves_legacy_bytes", || { tombstone_position_preimage_preserves_legacy_bytes(); Ok(()) }),
        libtest_mimic::Trial::test("move_rejects_uncertified_tombstone", || { move_rejects_uncertified_tombstone(); Ok(()) }),
        libtest_mimic::Trial::test("rendered_name_uses_lineage_winner_and_moves_derived_namespace", || { rendered_name_uses_lineage_winner_and_moves_derived_namespace(); Ok(()) }),
        libtest_mimic::Trial::test("move_rejects_forged_root_path", || { move_rejects_forged_root_path(); Ok(()) }),
        libtest_mimic::Trial::test("move_rejects_uncertified_anchor", || { move_rejects_uncertified_anchor(); Ok(()) }),
        libtest_mimic::Trial::test("move_rejects_changed_lineage", || { move_rejects_changed_lineage(); Ok(()) }),
        libtest_mimic::Trial::test("move_rejects_cross_file_placement", || { move_rejects_cross_file_placement(); Ok(()) }),
        libtest_mimic::Trial::test("controller_deleted_position_cannot_be_reinserted_by_author", || { controller_deleted_position_cannot_be_reinserted_by_author(); Ok(()) }),
        libtest_mimic::Trial::test("unknown_committed_move_retries_after_agent_revocation", || { unknown_committed_move_retries_after_agent_revocation(); Ok(()) }),
        libtest_mimic::Trial::test("committed_anchored_move_retries_after_anchor_tombstone", || { committed_anchored_move_retries_after_anchor_tombstone(); Ok(()) }),
    ]);
}
