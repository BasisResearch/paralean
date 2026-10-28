//! Replay horizons (docs/w4-rest-log.md, design 3).
//!
//! W4 keeps every replay row forever, because a delayed retry of a forgotten request ID
//! would execute again. A shard's replay generation `G` bounds that. Every client-chosen
//! ID (a work request, a group request, a validation request, a poll token) names a
//! generation; the request's identity is the pair `(g, id)`. The shard accepts new
//! submissions only in `G` and `G - 1`, and refuses anything older with a definite
//! answer, never executing it. The leader advances `G` once the shard clock passes
//! `started_tick + H`, under its lease and term. Once a generation has been refused for
//! the grace period, the collector deletes its replay rows.
//!
//! Generation 0 is the legacy namespace: its identity is the ID itself, its rows keep
//! their W4 keys, and it is never retired (`--require-replay-generation` refuses it).
//!
//! **Identity encoding.** A generation-`g > 0` identity is the string
//! `"\u{1e}" + g + "/" + id`, used wherever the controller keys by request ID (the
//! snapshot, work and validation routes, J1-J3, group descriptors). A request ID that is
//! already in this form names its own generation (a worker passes back the work ID it
//! was given), so a legacy client cannot alias a scoped identity under generation 0.
//! Replay rows of generation `g > 0` live under `replay-rows/<g>/...`, so retiring a
//! generation is a range of keys.
//!
//! **Retained.** Routing records keyed by request ID (work-shard routes, group-request
//! descriptors, validation routes and the shard-local validation index), P2's J1/J2/J3
//! and the recovery counters are not retired: see docs/w4-rest-log.md.

use foundationdb::options::StreamingMode;
use foundationdb::{KeySelector, RangeOption};
use paralean_store::id::sha256;
use serde::{Deserialize, Serialize};

use crate::durable::Durable;
use crate::gc::GcConfig;

/// First character of a generation-scoped identity (ASCII record separator).
pub const SCOPE_MARK: char = '\u{1e}';

/// Replay-horizon policy of a controller shard. Off by default: no generation is ever
/// started, every request is legacy generation 0, and nothing is retired.
#[derive(Clone, Debug)]
pub struct ReplayConfig {
    /// Advance the generation every `H` ticks of the shard clock (None: never).
    pub horizon_ticks: Option<u64>,
    /// Ticks a generation must have been refused before its rows are deleted.
    pub grace_ticks: u64,
    /// Refuse generation-0 (legacy) submissions.
    pub require_generation: bool,
}

impl Default for ReplayConfig {
    fn default() -> Self {
        ReplayConfig { horizon_ticks: None, grace_ticks: 8, require_generation: false }
    }
}

/// `controller/shard/<n>/replay-gen`. Generation 0 (no record) means no generation started.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayGen {
    pub generation: u64,
    pub started_tick: u64,
    /// Dynamic topology: the shard whose clock `started_tick` is on (the lowest active
    /// member advances the deployment-wide generation).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub clock_shard: Option<u32>,
}

/// Cumulative retirement counters, `controller/shard/<n>/replay-stats`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReplayStats {
    pub deleted_rows: u64,
    pub deleted_bytes: u64,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct ReplayReport {
    pub generation: u64,
    pub examined: usize,
    pub deleted_rows: usize,
    pub deleted_bytes: usize,
}

/// The identity of `id` in generation `g`.
pub fn scoped_id(generation: u64, id: &str) -> String {
    if generation == 0 || cfg!(feature = "mutate-replay-dedupe-ignores-generation") {
        id.to_string()
    } else {
        format!("{SCOPE_MARK}{generation}/{id}")
    }
}

/// `Some(Ok((g, id)))` for a canonical scoped identity, `Some(Err(()))` for a string that
/// starts with the mark but is not one, None for an unscoped (generation-0) ID.
pub fn parse_scoped(s: &str) -> Option<Result<(u64, &str), ()>> {
    let rest = s.strip_prefix(SCOPE_MARK)?;
    let Some((digits, id)) = rest.split_once('/') else { return Some(Err(())) };
    let canonical = !digits.is_empty() && digits.len() <= 20 && digits.bytes().all(|b| b.is_ascii_digit())
        && !digits.starts_with('0');
    match digits.parse::<u64>() {
        Ok(g) if canonical && g > 0 => Some(Ok((g, id))),
        _ => Some(Err(())),
    }
}

/// The generation of a well-formed scoped identity (None for generation 0).
pub fn identity_generation(identity: &str) -> Option<u64> {
    match parse_scoped(identity) {
        Some(Ok((g, _))) => Some(g),
        _ => None,
    }
}

/// The identity and generation a request names: `raw` in generation `field` (absent: 0),
/// or, if `raw` is already a scoped identity, that identity and its own generation.
pub fn resolve_id(field: Option<u64>, raw: &str) -> Result<(u64, String), String> {
    match parse_scoped(raw) {
        Some(Ok((g, _))) => {
            if field.unwrap_or(0) == 0 || field == Some(g) {
                Ok((g, raw.to_string()))
            } else {
                Err("request ID names another replay generation".into())
            }
        }
        Some(Err(())) => Err("malformed replay-scoped request ID".into()),
        None => {
            let g = field.unwrap_or(0);
            Ok((g, scoped_id(g, raw)))
        }
    }
}

/// Whether the shard, at generation `current`, accepts a new submission in generation `g`.
/// Every refusal ends with `(current replay generation N)`; see [`generation_hint`].
pub fn check(g: u64, current: u64, require: bool) -> Result<(), String> {
    let hint = format!("(current replay generation {current})");
    if g == 0 {
        if require && !cfg!(feature = "mutate-replay-accept-legacy") {
            return Err(format!("replay generation required {hint}"));
        }
        return Ok(());
    }
    if g > current {
        return Err(format!("replay generation {g} is ahead of this shard {hint}"));
    }
    let window = if cfg!(feature = "mutate-replay-accept-g-minus-2") { 2 } else { 1 };
    if g + window >= current {
        return Ok(());
    }
    Err(format!("expired replay generation {g} {hint}"))
}

/// The current generation a refusal reports.
pub fn generation_hint(reason: &str) -> Option<u64> {
    let rest = reason.rsplit_once("(current replay generation ")?.1;
    rest.strip_suffix(')')?.parse().ok()
}

fn be_u64(v: &[u8]) -> Result<u64, String> {
    Ok(u64::from_be_bytes(v.try_into().map_err(|_| "invalid replay record")?))
}

/// Shard `shard`'s replay row of a generation-`g > 0` identity (any shard's, for the
/// cross-shard lookups of a dynamic topology).
pub(crate) fn replay_row_key_of(store: &paralean_store::Store, shard: u32, generation: u64, kind: &str, identity: &str) -> Vec<u8> {
    store.meta.keys.root.subspace(&("controller", "shard", shard as u64, "replay-rows"))
        .pack(&(generation, kind, foundationdb::tuple::Bytes::from(&sha256(identity.as_bytes())[..])))
}

impl Durable {
    /// A fixed shard has its own generation. In a dynamic topology a request's bucket,
    /// and so the shard that sees its retries, can move, so the generation (and when
    /// each one stopped being accepted) is deployment-wide: a retry is judged by the
    /// same window wherever it lands.
    pub(crate) fn replay_gen_key(&self) -> Vec<u8> {
        if self.dynamic && !cfg!(feature = "mutate-replay-per-shard-generation") {
            return self.store.meta.keys.root.pack(&("controller", "replay-gen"));
        }
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "replay-gen"))
    }
    fn replay_refused_key(&self, generation: u64) -> Vec<u8> {
        if self.dynamic && !cfg!(feature = "mutate-replay-per-shard-generation") {
            return self.store.meta.keys.root.pack(&("controller", "replay-refused", generation));
        }
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "replay-refused", generation))
    }
    /// Dynamic topology: the tick of this shard's clock at which it first saw
    /// `generation` refused. Its grace runs on its own clock from there.
    fn replay_seen_refused_key(&self, generation: u64) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "replay-seen-refused", generation))
    }

    /// Inside a save: the request generation `g` must still be accepted at the commit
    /// version. An advance that stops accepting `g` conflicts with this read, so a
    /// request that passed the gate commits only while its rows cannot have been retired.
    pub(crate) async fn require_replay_generation_in(&self, trx: &foundationdb::Transaction, g: u64) -> Result<(), String> {
        if g == 0 || cfg!(feature = "mutate-replay-no-commit-check") { return Ok(()) }
        let current = Self::read_replay_gen(trx, &self.replay_gen_key()).await?;
        check(g, current.generation, false)
    }
    fn replay_stats_key(&self) -> Vec<u8> {
        self.store.meta.keys.root.pack(&("controller", "shard", self.shard as u64, "replay-stats"))
    }
    pub fn replay_rows_subspace(&self) -> foundationdb::tuple::Subspace {
        self.store.meta.keys.root.subspace(&("controller", "shard", self.shard as u64, "replay-rows"))
    }
    /// The replay row of a generation-`g > 0` identity: `replay-rows/<g>/<kind>/<sha256>`.
    pub(crate) fn replay_row_key(&self, generation: u64, kind: &str, identity: &str) -> Vec<u8> {
        replay_row_key_of(&self.store, self.shard, generation, kind, identity)
    }

    async fn read_replay_gen(trx: &foundationdb::Transaction, key: &[u8]) -> Result<ReplayGen, String> {
        trx.get(key, false).await.map_err(|e| e.to_string())?
            .map(|v| serde_json::from_slice(&v).map_err(|e| e.to_string())).transpose().map(Option::unwrap_or_default)
    }

    pub async fn replay_generation(&self) -> Result<ReplayGen, String> {
        let trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        Self::read_replay_gen(&trx, &self.replay_gen_key()).await
    }

    pub async fn replay_stats(&self) -> Result<ReplayStats, String> {
        self.store.meta.get(self.replay_stats_key()).await.map_err(|e| e.to_string())?
            .map(|v| serde_json::from_slice(&v).map_err(|e| e.to_string())).transpose().map(Option::unwrap_or_default)
    }

    /// The tick at which generation `g` stopped being accepted, if it has.
    pub async fn replay_refused_tick(&self, generation: u64) -> Result<Option<u64>, String> {
        self.store.meta.get(self.replay_refused_key(generation)).await.map_err(|e| e.to_string())?
            .map(|v| be_u64(&v)).transpose()
    }

    /// Start generation 1, or advance `G` by one once the shard clock reached
    /// `started_tick + horizon`, in one transaction under this replica's lease and term.
    /// Advancing to `G + 1` stops accepting `G - 1` and records that tick. Returns the
    /// generation after the call.
    pub async fn advance_replay_generation(&self, term: u64, horizon: u64) -> Result<ReplayGen, String> {
        if horizon == 0 { return Err("replay horizon must be positive".into()) }
        let key = self.replay_gen_key();
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let tick = if cfg!(feature = "mutate-replay-advance-no-fence") {
                Self::read_tick(&trx, &self.clock_key()).await?
            } else {
                self.require_lease(&trx, term).await?
            };
            let current = Self::read_replay_gen(&trx, &key).await?;
            let me = self.dynamic.then_some(self.shard);
            if self.dynamic && !cfg!(feature = "mutate-replay-per-shard-generation") {
                // Only the lowest active member advances the deployment-wide generation,
                // on its own clock; a new designee restarts the horizon on its clock.
                let topology = crate::topology::topology_in(&trx, &self.store).await?;
                let designee = topology.members.iter()
                    .find(|(_, s)| **s == crate::topology::MemberState::Active).map(|(n, _)| *n);
                if designee != Some(self.shard) { return Ok(current) }
                if current.generation != 0 && current.clock_shard != me {
                    let next = ReplayGen { started_tick: tick, clock_shard: me, ..current };
                    trx.set(&key, &serde_json::to_vec(&next).map_err(|e| e.to_string())?);
                    match trx.commit().await {
                        Ok(_) => return Ok(next),
                        Err(e) => { trx = e.on_error().await.map_err(|e| e.to_string())?; continue }
                    }
                }
            }
            let next = if current.generation == 0 {
                ReplayGen { generation: 1, started_tick: tick, clock_shard: me }
            } else if tick >= current.started_tick.saturating_add(horizon) {
                let generation = current.generation.checked_add(1).ok_or("replay generation exhausted")?;
                // `G + 1` accepts `G + 1` and `G`: `G - 1` stops being accepted now.
                let stopped = if cfg!(feature = "mutate-replay-retire-g-minus-1") { current.generation } else { current.generation - 1 };
                if stopped >= 1 {
                    trx.set(&self.replay_refused_key(stopped), &tick.to_be_bytes());
                }
                ReplayGen { generation, started_tick: tick, clock_shard: me }
            } else {
                return Ok(current);
            };
            trx.set(&key, &serde_json::to_vec(&next).map_err(|e| e.to_string())?);
            match trx.commit().await {
                Ok(_) => return Ok(next),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("replay generation outcome unresolved".into())
    }

    /// Delete one bounded page of replay rows of retired generations (at most `G - 2`)
    /// that have been refused for at least `replay.grace_ticks`. The page is read, checked
    /// and cleared in one transaction with the lease, term, clock, generation and
    /// refusal records, so a concurrent advance, takeover or row write conflicts with it.
    /// Generation-0 rows (W4's `history-work`/`history-poll`) are outside the scanned range.
    pub async fn collect_replay_rows(&self, term: u64, replay: &ReplayConfig, gc: &GcConfig) -> Result<ReplayReport, String> {
        if !gc.enabled { return Err("controller GC is disabled".into()) }
        if replay.grace_ticks == 0 || gc.scan_limit == 0 || gc.scan_limit > 1024 {
            return Err("replay retirement requires positive grace and a scan limit of 1..=1024".into());
        }
        let rows = self.replay_rows_subspace();
        let stats_key = self.replay_stats_key();
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let tick = if cfg!(feature = "mutate-replay-retire-no-fence") {
                Self::read_tick(&trx, &self.clock_key()).await?
            } else {
                self.require_lease(&trx, term).await?
            };
            let current = Self::read_replay_gen(&trx, &self.replay_gen_key()).await?;
            let mut report = ReplayReport { generation: current.generation, ..ReplayReport::default() };
            // Generations at most `G - 2` are refused; `G - 1` and `G` are still accepted.
            let keep = if cfg!(feature = "mutate-replay-retire-g-minus-1") { 1 } else { 2 };
            let first = if cfg!(feature = "mutate-replay-retire-gen0") { 0 } else { 1 };
            let Some(last) = current.generation.checked_sub(keep).filter(|&g| g >= 1) else { return Ok(report) };
            let mut ranges = vec![(rows.pack(&(first,)), rows.pack(&(last + 1,)))];
            if cfg!(feature = "mutate-replay-retire-gen0") {
                for kind in ["history-work", "history-poll"] {
                    ranges.push(self.store.meta.keys.root.subspace(&("controller", "shard", self.shard as u64, kind)).range());
                }
            }
            let mut eligible: std::collections::BTreeMap<u64, bool> = std::collections::BTreeMap::new();
            let mut wrote_seen = false;
            let mut stop = false;
            for (begin, end) in ranges {
                if stop { break }
                let opt = RangeOption {
                    limit: Some(gc.scan_limit - report.examined),
                    mode: StreamingMode::WantAll,
                    ..RangeOption::from((KeySelector::first_greater_or_equal(begin), KeySelector::first_greater_or_equal(end)))
                };
                if opt.limit == Some(0) { break }
                let page: Vec<(Vec<u8>, usize)> = trx.get_range(&opt, 1, false).await.map_err(|e| e.to_string())?
                    .iter().map(|kv| (kv.key().to_vec(), kv.value().len())).collect();
                for (key, value_len) in page {
                    let generation = match rows.unpack::<(u64, String, Vec<u8>)>(&key) {
                        Ok((g, _, _)) => g,
                        Err(_) if cfg!(feature = "mutate-replay-retire-gen0") => 0,
                        Err(e) => return Err(format!("invalid replay row key: {e:?}")),
                    };
                    let ok = match eligible.get(&generation) {
                        Some(ok) => *ok,
                        None => {
                            let mut refused = trx.get(&self.replay_refused_key(generation), false).await.map_err(|e| e.to_string())?
                                .map(|v| be_u64(&v)).transpose()?;
                            if self.dynamic && refused.is_some() {
                                // The refusal tick is on the designee's clock; count this
                                // shard's grace on its own clock from when it first saw it.
                                let seen = self.replay_seen_refused_key(generation);
                                refused = trx.get(&seen, false).await.map_err(|e| e.to_string())?
                                    .map(|v| be_u64(&v)).transpose()?;
                                if refused.is_none() {
                                    trx.set(&seen, &tick.to_be_bytes());
                                    wrote_seen = true;
                                    refused = Some(tick);
                                }
                            }
                            let ok = generation == 0 || cfg!(feature = "mutate-replay-retire-no-grace")
                                || refused.is_some_and(|t| tick >= t && tick - t >= replay.grace_ticks);
                            eligible.insert(generation, ok);
                            ok
                        }
                    };
                    // Refusal ticks grow with the generation: no later row is eligible either.
                    if !ok { stop = true; break }
                    report.examined += 1;
                    report.deleted_rows += 1;
                    report.deleted_bytes += key.len() + value_len;
                    trx.clear(&key);
                }
            }
            if report.deleted_rows == 0 && !wrote_seen { return Ok(report) }
            let mut stats: ReplayStats = trx.get(&stats_key, false).await.map_err(|e| e.to_string())?
                .map(|v| serde_json::from_slice(&v).map_err(|e| e.to_string())).transpose()?.unwrap_or_default();
            stats.deleted_rows = stats.deleted_rows.saturating_add(report.deleted_rows as u64);
            stats.deleted_bytes = stats.deleted_bytes.saturating_add(report.deleted_bytes as u64);
            trx.set(&stats_key, &serde_json::to_vec(&stats).map_err(|e| e.to_string())?);
            match trx.commit().await {
                Ok(_) => return Ok(report),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("replay retirement outcome unresolved".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A request that passed the gate commits its effects only while its generation is
    /// still accepted: the save re-reads the generation in its own transaction.
    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn saves_recheck_the_request_generation() {
        use paralean_store::{Faults, KeyFile, Store, StoreConfig};
        let deployment = format!("replay-commit-{}", hex::encode(rand::random::<[u8; 8]>()));
        let store = Store::open(&StoreConfig::from_env(&deployment).unwrap(), KeyFile::demo(2).ring(), Faults::none()).unwrap();
        let d = Durable::new(store, std::time::Duration::from_millis(500));
        let term = d.acquire_or_renew().await.unwrap().unwrap().term;
        for _ in 0..3 {
            d.advance_replay_generation(term, 1).await.unwrap();
            d.tick().await.unwrap();
        }
        assert_eq!(d.replay_generation().await.unwrap().generation, 3);
        for (g, accepted) in [(1, false), (2, true), (3, true), (0, true)] {
            *d.replay_check.lock().unwrap() = Some(g);
            let saved = d.save(format!("state {g}").as_bytes(), term).await;
            assert_eq!(saved.is_ok(), accepted, "generation {g}: {saved:?}");
        }
        *d.replay_check.lock().unwrap() = None;
    }

    #[test]
    fn scoped_identities_are_injective_and_canonical() {
        assert_eq!(scoped_id(0, "a"), "a");
        assert_eq!(parse_scoped(&scoped_id(7, "a/b")), Some(Ok((7, "a/b"))));
        assert_eq!(parse_scoped("plain"), None);
        for bad in ["\u{1e}", "\u{1e}x/a", "\u{1e}0/a", "\u{1e}07/a", "\u{1e}7a", "\u{1e}99999999999999999999999/a"] {
            assert_eq!(parse_scoped(bad), Some(Err(())), "{bad:?}");
        }
        // A scoped raw ID names its own generation; a conflicting field is refused.
        let id = scoped_id(5, "w");
        assert_eq!(resolve_id(None, &id).unwrap(), (5, id.clone()));
        assert_eq!(resolve_id(Some(0), &id).unwrap(), (5, id.clone()));
        assert_eq!(resolve_id(Some(5), &id).unwrap(), (5, id.clone()));
        assert!(resolve_id(Some(6), &id).is_err());
        assert_eq!(resolve_id(Some(6), "w").unwrap(), (6, scoped_id(6, "w")));
        assert_eq!(resolve_id(None, "w").unwrap(), (0, "w".into()));
        assert!(resolve_id(None, "\u{1e}junk").is_err());
    }

    #[test]
    fn the_shard_accepts_exactly_its_two_newest_generations() {
        assert!(check(0, 0, false).is_ok() && check(0, 9, false).is_ok());
        assert_eq!(generation_hint(&check(0, 9, true).unwrap_err()), Some(9));
        assert_eq!(generation_hint(&check(1, 0, false).unwrap_err()), Some(0));
        assert!(check(5, 5, false).is_ok() && check(4, 5, false).is_ok());
        assert!(check(3, 5, false).unwrap_err().starts_with("expired replay generation 3"));
        assert_eq!(generation_hint(&check(6, 5, false).unwrap_err()), Some(5));
        assert_eq!(generation_hint(&check(1, 5, true).unwrap_err()), Some(5));
    }
}
