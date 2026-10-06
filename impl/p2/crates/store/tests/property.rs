//! Property-based test: proptest generates random interleavings of store operations by
//! three logical writers and the controller, each operation optionally hit by a fault (an
//! unknown commit result with or without the commit landing, or another actor's rotation
//! or reassignment between the operation's reads and its commit, or a writer crash that
//! loses its local state). After every operation the store must satisfy store.md's
//! invariants (checked by `audit` plus recovery):
//!
//! - published ⇒ certified, and every certificate names a published marker;
//! - at most one head per target, equal to the record's head, topping every proof;
//! - the selected catalogue record is fenced (its commit certificate carries an issued
//!   token) and is ready; no orphan commits;
//! - no metadata key names an object absent from S3.
//!
//! Cases: `PROPTEST_CASES` (default 12), each up to 24 operations.

mod common;

use std::collections::BTreeMap;

use common::*;
use paralean_store::recovery::recover_catalog;
use paralean_store::*;
use proptest::prelude::*;

const W: usize = 3;
const T: usize = 2;

#[derive(Clone, Debug)]
enum Op {
    Prepare { w: usize, t: usize },
    Publish { w: usize, t: usize },
    PublishFree { w: usize },
    Reassign { t: usize, to: usize },
    Rotate { to: usize },
    Stage { w: usize },
    Commit { w: usize },
    Crash { w: usize },
}

#[derive(Clone, Debug)]
enum Fault {
    None,
    UnknownCommitted,
    UnknownNotCommitted,
    InterleaveRotate(usize),
    InterleaveReassign(usize, usize),
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        3 => (0..W, 0..T).prop_map(|(w, t)| Op::Prepare { w, t }),
        3 => (0..W, 0..T).prop_map(|(w, t)| Op::Publish { w, t }),
        2 => (0..W).prop_map(|w| Op::PublishFree { w }),
        2 => (0..T, 0..W).prop_map(|(t, to)| Op::Reassign { t, to }),
        2 => (0..W).prop_map(|to| Op::Rotate { to }),
        1 => (0..W).prop_map(|w| Op::Stage { w }),
        3 => (0..W).prop_map(|w| Op::Commit { w }),
        1 => (0..W).prop_map(|w| Op::Crash { w }),
    ]
}

fn fault() -> impl Strategy<Value = Fault> {
    prop_oneof![
        6 => Just(Fault::None),
        1 => Just(Fault::UnknownCommitted),
        1 => Just(Fault::UnknownNotCommitted),
        1 => (0..W).prop_map(Fault::InterleaveRotate),
        1 => (0..T, 0..W).prop_map(|(t, w)| Fault::InterleaveReassign(t, w)),
    ]
}

fn tname(t: usize) -> Name {
    Name::parse(&format!("Prop.t{t}"))
}

#[derive(Default, Clone)]
struct Local {
    pending: BTreeMap<usize, Package>,
    published: Vec<Id>,
    last_commit: Option<Id>,
    token: Option<TokenRef>,
}

async fn run_case(ops: Vec<(Op, Fault)>) -> std::result::Result<(), String> {
    let faults = Faults::none();
    let e = Env::with_faults("prop", W, faults.clone());
    for t in 0..T {
        e.ctl.reassign(&tname(t), e.w[0].id, format!("init{t}").as_bytes()).await.unwrap();
    }
    let mut local: Vec<Local> = vec![Local::default(); W];
    for (step, (op, f)) in ops.iter().enumerate() {
        let cf = match f {
            Fault::None => CommitFault::None,
            Fault::UnknownCommitted => CommitFault::UnknownCommitted,
            Fault::UnknownNotCommitted => CommitFault::UnknownNotCommitted,
            Fault::InterleaveRotate(w) => CommitFault::Interleave(rotate_hook(&e.ctl, e.w[*w].id, &format!("irot{step}"))),
            Fault::InterleaveReassign(t, w) => {
                CommitFault::Interleave(reassign_hook(&e.ctl, tname(*t), e.w[*w].id, &format!("iras{step}")))
            }
        };
        if !matches!(cf, CommitFault::None) {
            faults.on_commit(None, 0, cf);
        }
        let tag = format!("s{step}");
        let r: Result<()> = async {
            match op {
                Op::Prepare { w, t } => {
                    let p = e.prepare(*w, &tname(*t), &tag, step as u64).await?;
                    local[*w].pending.insert(*t, p); // at most one pending proof per name
                }
                Op::Publish { w, t } => {
                    if let Some(p) = local[*w].pending.remove(t) {
                        e.w[*w].publish(&p).await?;
                        local[*w].published.push(rev_id(&p));
                    }
                }
                Op::PublishFree { w } => {
                    let p = e.plain_package(*w, &format!("Prop.free.{tag}"), &tag);
                    e.w[*w].publish(&p).await?;
                    local[*w].published.push(rev_id(&p));
                }
                Op::Reassign { t, to } => {
                    e.ctl.reassign(&tname(*t), e.w[*to].id, format!("ras{step}").as_bytes()).await?;
                }
                Op::Rotate { to } => {
                    let tok = e.ctl.rotate(e.w[*to].id, format!("rot{step}").as_bytes()).await?;
                    local[*to].token = Some(tok);
                }
                Op::Stage { w } | Op::Commit { w } => {
                    let l = &local[*w];
                    let (Some(tok), false) = (l.token, l.published.is_empty()) else { return Ok(()) };
                    let contents: Vec<Id> = l.published.iter().rev().take(2).copied().collect();
                    let cp = fixture::checkpoint(e.w[*w].id, contents, l.last_commit, tok, &tag);
                    if matches!(op, Op::Commit { .. }) {
                        let c = e.w[*w].commit_checkpoint(&cp).await?;
                        local[*w].last_commit = Some(c);
                        // Ghost check of the fence history: operations run one at a time, so a
                        // successful commit leaves the fence at the record's rank.
                        let fence = e.store.fence().await?;
                        if fence != tok.rank {
                            return Err(StoreError::Invalid(format!("UNFENCED commit: rank {} under fence {fence}", tok.rank)));
                        }
                    } else {
                        let snap = prepare_snapshot(&e, *w, &cp).await;
                        e.w[*w].stage_record(&e.w[*w].sign_record(snap, l.last_commit, tok)).await?;
                    }
                }
                Op::Crash { w } => local[*w] = Local::default(),
            }
            Ok(())
        }
        .await;
        match r {
            Ok(()) | Err(StoreError::Guard(_)) => {}
            Err(err) => return Err(format!("step {step} {op:?} {f:?}: unexpected error {err}")),
        }
        // Drop a rule the operation did not consume (it aborted before committing).
        faults.clear_rules();
        let a = paralean_store::audit::audit(&e.store).await.map_err(|x| x.to_string())?;
        if !a.ok() || !a.uncertified_markers.is_empty() {
            return Err(format!("step {step} {op:?} {f:?}: {:?} uncertified {:?}", a.violations, a.uncertified_markers));
        }
        for w in 0..W {
            let rec = recover_catalog(&e.store, e.w[w].id).await.map_err(|x| x.to_string())?;
            if let Some(c) = rec.selected {
                let r = e.store.record(&c).await.unwrap().unwrap();
                let tok = e.store.token(r.body.token.rank).await.unwrap();
                if e.store.valid_rcert(&c, &r.body).await.unwrap().is_none() || tok.map(|t| t.token.body.token) != Some(r.body.token) {
                    return Err(format!("step {step}: selected record {c:?} is not fenced"));
                }
            }
            // A writer that lost its local state starts a new chain: recovery then reports
            // the conflict and must not pick a winner silently.
            if rec.conflict && rec.selected.is_some() {
                return Err(format!("step {step}: writer {w}: a conflict with an automatic selection"));
            }
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: std::env::var("PROPTEST_CASES").ok().and_then(|s| s.parse().ok()).unwrap_or(12),
        max_shrink_iters: 64,
        .. ProptestConfig::default()
    })]
    #[test]
    fn random_interleavings_keep_store_invariants(ops in proptest::collection::vec((op(), fault()), 4..24)) {
        let rt = tokio::runtime::Builder::new_current_thread().enable_all().build().unwrap();
        let r = rt.block_on(run_case(ops));
        prop_assert!(r.is_ok(), "{}", r.unwrap_err());
    }
}
