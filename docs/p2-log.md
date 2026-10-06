# P2 log

Branch `p2`, implementation in [impl/p2](../impl/p2/README.md). Services on aws-dev in user
space under `/data/home/kirancodes/paralean-p2/`: FoundationDB 7.3.79 (single, ssd-2) and
Garage 2.4.1 (replication 1, consistent mode) behind `s3-guard`.

## Results (2026-10-06, live services)

- library unit tests 9/9 (PCE, IDs, objects, P1 golden vectors), s3-guard 1/1,
  guards 13/13, fixtures 9/9, faults 10/10, property test 150 cases / 0 failures,
  multi-process 1/1 (12 workers; 4 aborted at injected crash points, 2 SIGKILLed; audit clean,
  at most one head per target, selected records fenced).
- Garage checks: wrong `x-amz-checksum-sha256` is rejected (InvalidDigest), the checksum is
  echoed, 300 back-to-back PUT→GET read-after-write checks passed. No client-side fallback
  was needed; the client also re-hashes before PUT and after GET.
- Mutations (`scripts/check-mutations.sh`, the counterpart of TLA-GUARDS.md): all 11
  cases detected. Removing the owner check, the epoch fence, the head CAS, the atomic
  publisher certificate (lagging design), the T5 fence check or the T5 parent check each
  makes the named tests fail.
- FDB process kill (`scripts/fdb-kill-test.sh`): fdbserver SIGKILLed with 4 stress
  workers running, restarted after 4 s; every worker resolved its in-flight transactions
  (FDB errors retried, including real `commit_unknown_result`) and finished; audit clean.
- SHA-256 golden vectors computed by running P1's `Sha256.lean` with P1's toolchain
  (`scripts/p1-golden.sh`) match the Rust implementation, including a §1.2 preimage.

## Fault-injection findings

- **Paginated scans truncated silently (fixed).** The first FDB kill run reported
  certificates without markers and multiple target heads. The cause was the scan, not the
  kill: it stopped at a batch shorter than its page size, but FDB returns partial batches
  (byte limits) with `more = true`. Once a key space exceeded one batch, discovery,
  catalogue recovery and the audit saw a subset (268 of 445 markers), breaking
  `scan_between` / `certScanValue_covers`; recovery could have selected an older record.
  The scan now continues on `more()`; `paginated_scan_follows_partial_batches` is the
  regression test. The rule is now a refinement obligation in store.md, under
  "Physical scan and enumeration" (branch `store-doc`). Small test deployments never exceed a batch, which is why the unit
  tests missed it; the audit caught it at scale.

- A T3/T4 retry resolved only from "the state since my first attempt" misses a late,
  reordered duplicate and issues a second rank / reverts ownership. Fixed with grow-only
  request-index keys `treq/<request>` and `areq/<name>/<request>` written in the same
  transaction (and the `assign/<name>/<epoch>` log).
- A corrupt read of a payload during checkpoint commit aborts the commit
  (`NotAcknowledged`): safe, but a liveness cost; the writer could re-GET before giving up.
- FDB's default 5% operating-space reserve throttles all writes on a nearly full disk
  ("Log server running out of space"); `up.sh` lowers the knobs.

## Deviations from and gaps in store.md (exact places)

Items 1–9 are fixed in docs/store.md on branch `store-doc`. That branch also adds the
paginated-scan rule (continue while `more()`; never stop on a short batch) as a
refinement obligation under "Physical scan and enumeration". Item 10 is being fixed
in P1.

1. **Fixed in store.md (branch store-doc).** "Unfenced repair and acknowledgement" says an unknown-outcome T5 that committed before
   a rotation is retried, aborts, and leaves the record without a commit certificate. With
   T5 as in the Transactions table (record and `rcert` in one transaction) that is wrong:
   a committed T5 wrote the `rcert` too, the retry finds it and succeeds, and the record is
   (correctly) adopted. The late-ack case needs a staging write of the record before its
   commit. P2 implements that staging form (`stage_record`, fenced first write) and the
   fixture uses it; `fixture_put_before_rotation_acked_after` exercises both readings.
   Suggested sentence: "The late-acknowledgement case appears as a staging write of the
   record (fenced) whose outcome is resolved after a rotation; the commit T5 then aborts."
2. **Fixed in store.md (branch store-doc).** Layout: no domain for export manifests; P2 adds `v0/manifest` (sourceRoot, buildReceipt)
   and `v0/token`. T5's `ocert/manifest/<m>` is the record's snapshot, stored as
   `ocert/snapshot/<m>`.
3. **Fixed in store.md (branch store-doc).** Layout: ">64 kB values replaced in the marker by its ID" would change marker IDs. P2
   keeps IDs and uses a value envelope `0x01 ‖ objectID ‖ blobID`.
4. **Fixed in store.md (branch store-doc).** Layout additions: `treq/`, `areq/`, `assign/` (exact T3/T4 resolution, finding above).
5. **Fixed in store.md (branch store-doc).** §8.2 step 2 ("marker durably acknowledged") has no key; P2 PUTs the marker preimage to
   S3 `obj/marker/<id>` before T1.
6. **Fixed in store.md (branch store-doc).** T2 additionally requires an existing certificate (a raw marker key is not evidence),
   following §8.3 "receiving requires a live certificate".
7. **Fixed in store.md (branch store-doc).** Certificate bodies carry `replica`; a T7 copy to a *replacement* replica keeps σ, so
   the field cannot name the physical replica. Underspecified in §8.3/§9.
8. **Fixed in store.md (branch store-doc).** Signed objects (receipts, records, certificates) have ID = H(body); they cannot be stored
   as their preimage alone. P2 stores `bytes(preimage(body)) ‖ bytes(sig)`.
9. **Fixed in store.md (branch store-doc).** store.md calls Garage a way to avoid MinIO's AGPL; Garage is AGPL-3.0 too. MinIO
   community binaries are no longer distributed. Garage has no bucket policy or Object
   Lock, so deletes are refused by the `s3-guard` gateway; app credentials hitting Garage's
   port directly could still delete.
10. P1 deviates from §1.2: P1 group IDs are SHA-256 of the raw `paralean-group-v2` bytes
    (no `"paralean\0v0/group\0"` prefix), and `H("v0/insttype")` omits the prefix. P1 also
    encodes Lean `Nat` as LEB128, not §1.1 big-endian `nat`. P2 follows §1.2/§1.1; P2's
    group ID of a P1 group differs from P1's `declId` (`import-p1` prints both).

## Not done

- FDB kills *within* a redundancy mode: the P2 cluster is one process in `single` mode,
  so a kill is an outage and restart (tested), not a tolerated fault.
- Tombstone storage/discovery (§11.4); receipt binding (P3); buildability beyond the
  build-receipt verdict; anti-entropy between deployments beyond T7 and S3 repair copies.

## Sentences for plan.md / README.md

- plan.md P2: "Implemented on branch p2 (impl/p2): FoundationDB 7.3 + Garage, T1–T7,
  certificate-based discovery and catalogue recovery, fault injection; gate tests pass
  against the live services (docs/p2-log.md)."
