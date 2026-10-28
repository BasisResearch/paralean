//! Opt-in collection of controller-owned, superseded FoundationDB snapshot chunks.
//!
//! Protocol metadata and S3 objects are deliberately outside this collector: their
//! catalogue and anti-entropy key spaces are grow-only under docs/store.md.

use foundationdb::options::StreamingMode;
use foundationdb::KeySelector;
use foundationdb::RangeOption;
use serde::{Deserialize, Serialize};

use crate::durable::{Durable, RetiredSnapshot, SnapshotHead};

const MAX_CHUNKS: u32 = 137; // ceil(8 MiB / 60 KiB)
const CHUNK_SIZE: usize = 60 * 1024;

#[derive(Clone, Debug)]
pub struct GcConfig {
    /// Collection remains disabled until explicitly set to true.
    pub enabled: bool,
    /// Minimum advances of the shard's durable logical clock after retirement.
    pub grace_ticks: u64,
    /// Maximum candidates examined in one call.
    pub scan_limit: usize,
}

impl Default for GcConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            grace_ticks: 2,
            scan_limit: 128,
        }
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct GcReport {
    pub examined: usize,
    pub deleted_snapshots: usize,
    pub deleted_chunks: usize,
    pub reclaimed_bytes: usize,
    /// Pass this hash to the next call to continue past retained candidates.
    pub next_after: Option<String>,
}

fn valid_hash(hash: &str) -> bool {
    hash.len() == 64
        && hash
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

fn valid_retired(r: &RetiredSnapshot) -> bool {
    r.len <= 8 * 1024 * 1024
        && r.chunks <= MAX_CHUNKS
        && r.chunks as usize == r.len.div_ceil(CHUNK_SIZE)
        && r.generation > 0
}

impl Durable {
    /// Pin a controller snapshot for an explicit reader. Only a current or known
    /// retired snapshot may be pinned. The marker is checked by every GC clear.
    pub async fn retain_snapshot(&self, hash: &str, term: u64) -> Result<(), String> {
        if !valid_hash(hash) {
            return Err("invalid controller snapshot hash".into());
        }
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            let head = trx
                .get(&self.state_key(), false)
                .await
                .map_err(|e| e.to_string())?
                .map(|v| serde_json::from_slice::<SnapshotHead>(&v).map_err(|e| e.to_string()))
                .transpose()?;
            let retired = trx
                .get(&self.retired_key(hash), false)
                .await
                .map_err(|e| e.to_string())?
                .map(|v| serde_json::from_slice::<RetiredSnapshot>(&v).map_err(|e| e.to_string()))
                .transpose()?;
            let chunks = if let Some(h) = head.filter(|h| h.hash == hash) {
                h.chunks
            } else if let Some(r) = retired.filter(valid_retired) {
                r.chunks
            } else {
                return Err("controller snapshot is neither current nor retained candidate".into());
            };
            for index in 0..chunks {
                if trx
                    .get(&self.chunk_key(hash, index), false)
                    .await
                    .map_err(|e| e.to_string())?
                    .is_none()
                {
                    return Err("controller snapshot chunk missing; cannot retain".into());
                }
            }
            trx.set(&self.retained_key(hash), b"1");
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller snapshot retention outcome unresolved".into())
    }

    /// Remove an explicit pin. This is idempotent; the current head is still a root.
    pub async fn release_snapshot(&self, hash: &str, term: u64) -> Result<(), String> {
        if !valid_hash(hash) {
            return Err("invalid controller snapshot hash".into());
        }
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            self.require_lease(&trx, term).await?;
            trx.clear(&self.retained_key(hash));
            match trx.commit().await {
                Ok(_) => return Ok(()),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller snapshot release outcome unresolved".into())
    }

    /// Collect a bounded page. `after` is an exclusive hash cursor returned by the
    /// prior page; pass None to start a new sweep. Every candidate is revalidated
    /// inside its deletion transaction, including a lease, logical clock, current
    /// head, retention marker and the candidate's exact bytes.
    pub async fn collect_retired_snapshots(
        &self,
        term: u64,
        config: &GcConfig,
        after: Option<&str>,
    ) -> Result<GcReport, String> {
        if !cfg!(feature = "mutate-gc-no-opt-in-check") && !config.enabled {
            return Err("controller GC is disabled".into());
        }
        if config.grace_ticks == 0 || config.scan_limit == 0 || config.scan_limit > 1024 {
            return Err(
                "controller GC requires positive grace and a scan limit of 1..=1024".into(),
            );
        }
        if after.is_some_and(|h| !valid_hash(h)) {
            return Err("invalid controller GC cursor".into());
        }
        let sub = self.retired_subspace();
        let (begin, end) = sub.range();
        let start = after
            .map(|hash| KeySelector::first_greater_than(self.retired_key(hash)))
            .unwrap_or_else(|| KeySelector::first_greater_or_equal(begin));
        let opt = RangeOption {
            limit: Some(config.scan_limit),
            mode: StreamingMode::WantAll,
            ..RangeOption::from((start, KeySelector::first_greater_or_equal(end)))
        };
        let (candidates, more) = {
            let scan = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
            self.require_lease(&scan, term).await?;
            let page = scan
                .get_range(&opt, 1, false)
                .await
                .map_err(|e| e.to_string())?;
            let candidates: Vec<(String, Vec<u8>)> = page
                .iter()
                .map(|kv| {
                    let (hash,): (String,) = sub.unpack(kv.key()).map_err(|e| e.to_string())?;
                    Ok::<_, String>((hash, kv.value().to_vec()))
                })
                .collect::<Result<_, _>>()?;
            (candidates, page.more())
        };
        let mut report = GcReport::default();
        for (hash, listed) in candidates {
            if !valid_hash(&hash) {
                return Err("invalid retired controller snapshot key".into());
            }
            report.examined += 1;
            report.next_after = Some(hash.clone());
            if let Some((chunks, len)) = self
                .collect_one_snapshot(term, config.grace_ticks, &hash, &listed)
                .await?
            {
                report.deleted_snapshots += 1;
                report.deleted_chunks += chunks as usize;
                report.reclaimed_bytes += len;
            }
        }
        if !more {
            report.next_after = None
        }
        Ok(report)
    }

    async fn collect_one_snapshot(
        &self,
        term: u64,
        grace: u64,
        hash: &str,
        listed: &[u8],
    ) -> Result<Option<(u32, usize)>, String> {
        let candidate: RetiredSnapshot =
            serde_json::from_slice(listed).map_err(|e| e.to_string())?;
        if !valid_retired(&candidate) {
            return Err("invalid retired controller snapshot record".into());
        }
        let mut trx = self.store.meta.db.create_trx().map_err(|e| e.to_string())?;
        for _ in 0..60 {
            let tick = self.require_lease(&trx, term).await?;
            let current = trx
                .get(&self.retired_key(hash), false)
                .await
                .map_err(|e| e.to_string())?;
            if !cfg!(feature = "mutate-gc-no-candidate-check") && current.as_deref() != Some(listed)
            {
                return Ok(None);
            }
            if !cfg!(feature = "mutate-gc-no-grace-check")
                && (tick < candidate.retired_tick || tick - candidate.retired_tick < grace)
            {
                return Ok(None);
            }
            let head = trx
                .get(&self.state_key(), false)
                .await
                .map_err(|e| e.to_string())?
                .map(|v| serde_json::from_slice::<SnapshotHead>(&v).map_err(|e| e.to_string()))
                .transpose()?;
            let Some(head) = head else {
                return Err("controller head missing during GC".into());
            };
            if !valid_hash(&head.hash) || head.generation == 0 {
                return Err("invalid controller head during GC".into());
            }
            if !cfg!(feature = "mutate-gc-no-head-check") && head.hash == hash {
                return Ok(None);
            }
            if !cfg!(feature = "mutate-gc-no-retention-check")
                && trx
                    .get(&self.retained_key(hash), false)
                    .await
                    .map_err(|e| e.to_string())?
                    .is_some()
            {
                return Ok(None);
            }
            for index in 0..candidate.chunks {
                trx.clear(&self.chunk_key(hash, index));
            }
            trx.clear(&self.retired_key(hash));
            match trx.commit().await {
                Ok(_) => return Ok(Some((candidate.chunks, candidate.len))),
                Err(e) => trx = e.on_error().await.map_err(|e| e.to_string())?,
            }
        }
        Err("controller GC outcome unresolved".into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    use paralean_store::id::sha256;
    use paralean_store::{Faults, KeyFile, Store, StoreConfig};

    #[tokio::test(flavor = "multi_thread", worker_threads = 2)]
    async fn stale_scanned_candidate_cannot_collect_new_retirement() {
        let deployment = format!("gc-stale-{}", hex::encode(rand::random::<[u8; 8]>()));
        let cfg = StoreConfig::from_env(&deployment).unwrap();
        let store = Store::open(&cfg, KeyFile::demo(2).ring(), Faults::none()).unwrap();
        let d = Durable::new(store.clone(), Duration::from_millis(500));
        let term = d.acquire_or_renew().await.unwrap().unwrap().term;
        let hash = hex::encode(sha256(b"A"));

        d.save(b"A", term).await.unwrap();
        d.save(b"B", term).await.unwrap();
        let retired_key = d.retired_key(&hash);
        let stale = store.meta.get(retired_key.clone()).await.unwrap().unwrap();
        d.save(b"A", term).await.unwrap();
        d.tick().await.unwrap();
        d.save(b"C", term).await.unwrap();
        let newer = store.meta.get(retired_key.clone()).await.unwrap().unwrap();
        assert_ne!(stale, newer);

        // The old retirement has aged by two ticks, while the new one has aged
        // by only one. A collector paused after its scan must discard stale bytes.
        d.tick().await.unwrap();
        assert!(d
            .collect_one_snapshot(term, 2, &hash, &stale)
            .await
            .unwrap()
            .is_none());
        assert_eq!(store.meta.get(retired_key).await.unwrap(), Some(newer));
        assert!(store
            .meta
            .get(d.chunk_key(&hash, 0))
            .await
            .unwrap()
            .is_some());
        let policy = GcConfig {
            enabled: true,
            ..GcConfig::default()
        };
        // B's older retirement is eligible; A's newer one still needs a tick.
        assert_eq!(
            d.collect_retired_snapshots(term, &policy, None)
                .await
                .unwrap()
                .deleted_snapshots,
            1
        );
        d.tick().await.unwrap();
        // A's new incarnation becomes eligible only after its own grace.
        assert_eq!(
            d.collect_retired_snapshots(term, &policy, None)
                .await
                .unwrap()
                .deleted_snapshots,
            1
        );
    }
}
