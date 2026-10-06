//! Client-side fault injection.
//!
//! Faults are injected at the client boundary of each store operation:
//! - before an FDB commit: an injected `commit_unknown_result` with or without the commit
//!   landing, a crash before or after the commit, or an interleaved action (a fence
//!   rotation or reassignment between the transaction's reads and its commit);
//! - around an S3 PUT: a timeout with or without the object landing, a crash after it lands;
//! - on an S3 GET: corrupted bytes (the reader must treat a hash mismatch as missing);
//! - at named crash points in the writer workflows (e.g. between payload and metadata).
//!
//! One-shot rules are consumed in order; a seeded random mode drives property tests and
//! the multi-process stress workers. A crash returns `StoreError::Crashed` (in-process
//! tests treat the writer as dead from then on) or, in `CrashMode::Abort`, aborts the
//! process, which is a real crash.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use futures::future::BoxFuture;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::error::{Result, StoreError};
use crate::id::Kind;

/// The store transactions of store.md, plus the staging write of a catalogue record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Txn {
    T1Publish,
    T2Certify,
    T3Rotate,
    T4Reassign,
    T5Commit,
    T5Stage,
    T6ObjectCert,
    T7Repair,
}

pub type Hook = Arc<dyn Fn() -> BoxFuture<'static, ()> + Send + Sync>;

#[derive(Clone)]
pub enum CommitFault {
    None,
    /// Report `commit_unknown_result` without committing.
    UnknownNotCommitted,
    /// Commit, then report `commit_unknown_result` (the reply was lost).
    UnknownCommitted,
    /// Run an action after the transaction's reads and before its commit.
    Interleave(Hook),
    CrashBeforeCommit,
    CrashAfterCommit,
}

impl std::fmt::Debug for CommitFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            CommitFault::None => "None",
            CommitFault::UnknownNotCommitted => "UnknownNotCommitted",
            CommitFault::UnknownCommitted => "UnknownCommitted",
            CommitFault::Interleave(_) => "Interleave",
            CommitFault::CrashBeforeCommit => "CrashBeforeCommit",
            CommitFault::CrashAfterCommit => "CrashAfterCommit",
        };
        f.write_str(s)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PutFault {
    None,
    /// The PUT never reaches the store; the client sees a timeout.
    TimeoutNotLanded,
    /// The PUT lands; the client sees a timeout (lost response).
    TimeoutLanded,
    /// The PUT lands and the process dies before observing the reply.
    CrashAfterLanded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GetFault {
    None,
    /// Flip a byte of the fetched body before verification.
    Corrupt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CrashMode {
    Return,
    Abort,
}

#[derive(Clone, Debug)]
pub struct RandomFaults {
    pub p_unknown_committed: f64,
    pub p_unknown_not_committed: f64,
    pub p_put_timeout_landed: f64,
    pub p_put_timeout_not_landed: f64,
    pub p_corrupt_read: f64,
    pub p_crash_point: f64,
    pub p_crash_commit: f64,
}

impl RandomFaults {
    /// Unknown outcomes, timeouts and corrupt reads, but no crashes.
    pub fn no_crash(p: f64) -> Self {
        RandomFaults {
            p_unknown_committed: p,
            p_unknown_not_committed: p,
            p_put_timeout_landed: p,
            p_put_timeout_not_landed: p,
            p_corrupt_read: p,
            p_crash_point: 0.0,
            p_crash_commit: 0.0,
        }
    }
}

struct Rule<T> {
    txn: Option<Txn>,
    kind: Option<Kind>,
    skip: usize,
    fault: T,
}

#[derive(Default)]
struct State {
    commit: Vec<Rule<CommitFault>>,
    put: Vec<Rule<PutFault>>,
    get: Vec<Rule<GetFault>>,
    crash_points: Vec<(String, usize)>,
    random: Option<(StdRng, RandomFaults)>,
    stats: BTreeMap<String, u64>,
}

pub struct Faults {
    state: Mutex<State>,
    pub crash_mode: CrashMode,
}

impl Default for Faults {
    fn default() -> Self {
        Faults { state: Mutex::new(State::default()), crash_mode: CrashMode::Return }
    }
}

impl Faults {
    pub fn none() -> Arc<Faults> {
        Arc::new(Faults::default())
    }
    pub fn random(seed: u64, cfg: RandomFaults, crash_mode: CrashMode) -> Arc<Faults> {
        let f = Faults { state: Mutex::new(State::default()), crash_mode };
        f.state.lock().unwrap().random = Some((StdRng::seed_from_u64(seed), cfg));
        Arc::new(f)
    }

    /// Inject `fault` at the `skip`-th next commit of `txn` (any transaction if `None`).
    pub fn on_commit(&self, txn: Option<Txn>, skip: usize, fault: CommitFault) {
        self.state.lock().unwrap().commit.push(Rule { txn, kind: None, skip, fault });
    }
    pub fn on_put(&self, kind: Option<Kind>, skip: usize, fault: PutFault) {
        self.state.lock().unwrap().put.push(Rule { txn: None, kind, skip, fault });
    }
    pub fn on_get(&self, kind: Option<Kind>, skip: usize, fault: GetFault) {
        self.state.lock().unwrap().get.push(Rule { txn: None, kind, skip, fault });
    }
    /// Crash at the `skip`-th next pass through the named point.
    pub fn crash_at(&self, label: &str, skip: usize) {
        self.state.lock().unwrap().crash_points.push((label.to_string(), skip));
    }

    pub fn stats(&self) -> BTreeMap<String, u64> {
        self.state.lock().unwrap().stats.clone()
    }
    pub fn count(&self, what: &str) {
        *self.state.lock().unwrap().stats.entry(what.to_string()).or_default() += 1;
    }

    fn take<T: Clone>(rules: &mut Vec<Rule<T>>, txn: Option<Txn>, kind: Option<Kind>) -> Option<T> {
        let pos = rules.iter().position(|r| {
            (r.txn.is_none() || r.txn == txn) && (r.kind.is_none() || r.kind == kind)
        })?;
        if rules[pos].skip > 0 {
            rules[pos].skip -= 1;
            return None;
        }
        Some(rules.remove(pos).fault)
    }

    pub(crate) fn commit_fault(&self, txn: Txn) -> CommitFault {
        let mut s = self.state.lock().unwrap();
        let f = Self::take(&mut s.commit, Some(txn), None).or_else(|| {
            let (rng, cfg) = s.random.as_mut()?;
            let x: f64 = rng.gen();
            let c = cfg.clone();
            if x < c.p_unknown_committed {
                Some(CommitFault::UnknownCommitted)
            } else if x < c.p_unknown_committed + c.p_unknown_not_committed {
                Some(CommitFault::UnknownNotCommitted)
            } else if x < c.p_unknown_committed + c.p_unknown_not_committed + c.p_crash_commit {
                Some(if rng.gen::<bool>() { CommitFault::CrashBeforeCommit } else { CommitFault::CrashAfterCommit })
            } else {
                None
            }
        });
        let f = f.unwrap_or(CommitFault::None);
        if !matches!(f, CommitFault::None) {
            *s.stats.entry(format!("commit:{:?}:{:?}", txn, f)).or_default() += 1;
        }
        f
    }

    pub(crate) fn put_fault(&self, kind: Kind) -> PutFault {
        let mut s = self.state.lock().unwrap();
        let f = Self::take(&mut s.put, None, Some(kind)).or_else(|| {
            let (rng, cfg) = s.random.as_mut()?;
            let x: f64 = rng.gen();
            if x < cfg.p_put_timeout_landed {
                Some(PutFault::TimeoutLanded)
            } else if x < cfg.p_put_timeout_landed + cfg.p_put_timeout_not_landed {
                Some(PutFault::TimeoutNotLanded)
            } else {
                None
            }
        });
        let f = f.unwrap_or(PutFault::None);
        if f != PutFault::None {
            *s.stats.entry(format!("put:{:?}", f)).or_default() += 1;
        }
        f
    }

    pub(crate) fn get_fault(&self, kind: Kind) -> GetFault {
        let mut s = self.state.lock().unwrap();
        let f = Self::take(&mut s.get, None, Some(kind)).or_else(|| {
            let (rng, cfg) = s.random.as_mut()?;
            (rng.gen::<f64>() < cfg.p_corrupt_read).then_some(GetFault::Corrupt)
        });
        let f = f.unwrap_or(GetFault::None);
        if f != GetFault::None {
            *s.stats.entry("get:Corrupt".to_string()).or_default() += 1;
        }
        f
    }

    /// A named crash point in a writer workflow.
    pub fn point(&self, label: &str) -> Result<()> {
        let crash = {
            let mut s = self.state.lock().unwrap();
            let mut hit = false;
            if let Some(pos) = s.crash_points.iter().position(|(l, _)| l == label) {
                if s.crash_points[pos].1 > 0 {
                    s.crash_points[pos].1 -= 1;
                } else {
                    s.crash_points.remove(pos);
                    hit = true;
                }
            }
            if !hit {
                if let Some((rng, cfg)) = s.random.as_mut() {
                    let p = cfg.p_crash_point;
                    hit = rng.gen::<f64>() < p;
                }
            }
            if hit {
                *s.stats.entry(format!("crash:{label}")).or_default() += 1;
            }
            hit
        };
        if crash {
            return Err(self.crash(label));
        }
        Ok(())
    }

    pub(crate) fn crash(&self, label: &str) -> StoreError {
        if self.crash_mode == CrashMode::Abort {
            eprintln!("paralean: injected crash at {label}; aborting process");
            std::process::abort();
        }
        StoreError::Crashed(label.to_string())
    }
}
