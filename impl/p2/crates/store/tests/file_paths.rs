//! W2 A-6: a marker's or tombstone's `filePath` becomes a file every syncing working copy
//! writes. T1 (the publishing writer), T8 and T9 (anti-entropy import) refuse a path that
//! breaks the relative-path rule (`objects::check_file_path`).
mod common;

use paralean_store::antientropy::{export, import, Item, Outcome};
use paralean_store::*;

const HOSTILE: [&str; 5] = ["../../.bashrc", ".git/config", "/etc/x.lean", "A\\B.lean", "a/../../x.lean"];

#[tokio::test]
async fn t1_refuses_a_marker_with_an_unsafe_file_path() {
    use common::*;
    let e = Env::new("w2-path-t1", 1);
    for (i, bad) in HOSTILE.iter().enumerate() {
        let mut p = e.plain_package(0, &format!("Path.t1.c{i}"), &format!("path-t1-{i}"));
        p.marker.file_path = bad.to_string();
        let r = e.w[0].publish(&p).await;
        assert!(matches!(&r, Err(StoreError::Guard(GuardFailure::BadPackage(m))) if m.contains("file path")),
            "{bad:?}: {r:?}");
        assert!(e.store.marker(&p.group.id()).await.unwrap().is_none(), "{bad:?} was published");
    }
    // The control: a conforming path publishes.
    let p = e.plain_package(0, "Path.t1.ok", "path-t1-ok");
    e.w[0].publish(&p).await.unwrap();
}

#[tokio::test]
async fn t8_refuses_a_tombstone_with_an_unsafe_file_path() {
    use common::*;
    let e = Env::new("w2-path-t8", 1);
    let p = e.plain_package(0, "Path.t8", "path-t8");
    e.w[0].publish(&p).await.unwrap();
    let mut t = fixture::tombstone_of(&p.marker, 9);
    t.file_path = "../../.bashrc".into();
    let r = e.w[0].tombstone(&t).await;
    assert!(matches!(&r, Err(StoreError::Guard(GuardFailure::BadPackage(m))) if m.contains("file path")), "{r:?}");
}

#[tokio::test]
async fn t9_refuses_to_import_a_marker_with_an_unsafe_file_path() {
    use common::*;
    let (a, b) = pair("w2-path-t9", 1, Faults::none(), Faults::none());
    let p = a.plain_package(0, "Path.t9", "path-t9");
    a.w[0].publish(&p).await.unwrap();
    let item = export(&a.store).await.unwrap().into_iter().find(|i| matches!(i, Item::Group { .. })).unwrap();
    let Item::Group { revisions, receipt, job, certs, .. } = item else { unreachable!() };
    // The origin's own bytes with only the path replaced: the receiver must refuse them
    // before staging anything, whatever the certificates say.
    let mut m = p.marker.clone();
    m.file_path = "../../.bashrc".into();
    let forged = Item::Group { marker: m.preimage(), revisions, receipt, job, certs };
    let outcome = import(&b.w[0], &forged).await.unwrap();
    assert!(matches!(&outcome, Outcome::Rejected(r) if r.contains("marker does not decode")), "{outcome:?}");
    assert!(b.store.marker(&p.group.id()).await.unwrap().is_none());
}
