# W2 threat model and security findings

This audit is against `fee94d9` plus the W2 changes on branch `w2-security`,
recorded in [w2-log.md](w2-log.md). The finish pass merged `origin/main` `a5dfc5c`
(W1, W3, W4, W5) and audited the merged paths: findings W2-41 to W2-55. It is an implementation audit and a bounded
test campaign, not a proof that no vulnerabilities remain. Every High and Medium
finding below is fixed with a regression test and a guard-removal mutation,
except W2-12 (hostile P5 workers holding raw store access), which is outside the
threat model: P5's coding agents are trusted, which is the operating mode. W2-13
(package code sharing a process with the checker's verdict) has a fix, the split
check, which is off by default for the same reason (`PARALEAN_CHECKER_SPLIT=on`
enables it).

## Assets, actors and trust boundaries

Protected assets are accepted proof/group identity; exact policy, checker,
target and epoch binding; append-only payload and metadata history; recoverable
certificates and checkpoints; authority, issuer, validator and workspace
signing seeds; P5 recovery secrets; and service/host resources.

Attackers considered include unauthenticated network clients, authenticated
but buggy or malicious peers, stale owners replaying old receipts, workers
controlling workspace paths and source, and arbitrary native/package code
inside a validator child. Administrators, the host kernel, configured compiler
and trusted checker binaries, operator-selected import paths, FoundationDB's
transaction semantics and Garage's implementation are trusted. A compromised
administrator or host kernel is outside this audit.

There is a material distinction between holding a workspace signing key and
holding raw FoundationDB access. The latter bypasses application authorization:
the local FDB endpoint has no per-prefix application ACL. Current P5 workers
have this access. The protocol models assume guards execute in trusted
participants; they do not establish a boundary against arbitrary raw database
writers. This is an open high finding, not an assumed-away adversary.

RPC and anti-entropy signatures provide integrity/authentication, **not
confidentiality**. Deployment traffic containing private declarations needs a
private network or confidential transport. No seeds belong in those payloads.

## Coverage of the W2 audit items

| Audit item | Where it is covered |
| --- | --- |
| Receipt and signature verification on every path (T1, anti-entropy import, `remote%`, validator and controller RPC) | Path table below; W2-05, W2-08, W2-24 (strict Ed25519 per path, vectors, mutations), W2-28 (T9 cancellation and dependencies), W2-29 (pinned statement), W2-38 (RPC peer binding), W2-39 (`published_receipt`) |
| Key handling: authority, issuer, validator and workspace seeds; rotation and revocation; secrets in logs or environments | W2-02, W2-03, W2-07, W2-21, W2-22, W2-23, W2-26, W2-27, W2-37; "Keys, replay and fencing" |
| s3-guard delete denial and direct Garage port exposure | W2-10 (private socket, decoded queries), W2-25 (overwrite and copy denial), W2-26 (file modes), W2-40 |
| Replay and duplication | W2-32 (per-workspace request IDs), W2-38, W2-28; "Keys, replay and fencing" |
| Fence and epoch bypasses | W2-28, W2-29; "Keys, replay and fencing" (no bypass found in T1/T4/T5 or controller term fencing) |
| Path traversal in workspaces and exports | W2-01, W2-14, W2-15, W2-16, W2-20, W2-31 |
| Deserialisation of untrusted objects (PCE bounds, size limits, FDB value limits) | W2-09, W2-17, W2-30, W2-31; "Decoder, storage and availability bounds" |
| DoS through queue and backpressure abuse | W2-06, W2-30, W2-33, W2-34, W2-35, W2-36 |
| Controller and validator authentication | Path table; W2-36, W2-37, W2-38, W2-39 |
| P5 worker isolation | W2-12 (accepted: trusted workers), W2-01, W2-02, W2-20, W2-23 |

## Path-by-path review

| Path | Current enforcement and limitations |
| --- | --- |
| T1 publication | `receipt::check` checks validator signature, acceptance, group, signed envelope, pinned policy/checker and exact target bindings. T1 transactionally reads revocation, cancellation, every declared target's owner/epoch/head and certified dependencies. Existing guard mutations exercise these reads. |
| Anti-entropy T9/T10 | Authenticated deployment peers, signed certificate validation, receiver-local receipt pins and revocation checks, acknowledged/rehashed payloads, and pinned target homes. Peer authorities become target-free issuers, not local fence authorities. A transport signature alone is insufficient to import a group. |
| Lean `remote%` | Each closure receipt is checked locally and against live store consumer verification. W2 fixes authority-only target signing, exact target bytes, noncanonical/unbounded varints and cached-job replacement. Every capsule command passes the command gate (W2-18) before it elaborates; records, capsule modules/files and package IDs are checked (W2-14 to W2-16). Published-consumer verification reads revocation; cancellation prevents later publication but does not retroactively unpublish content. |
| Validator RPC | Fresh server challenge, signed request and signed response, each bound to the service and the server's key; authority/issuer authorization. Signed job binding/policy/checker/dependency checks precede a receipt. OS containment protects the signing parent from child file/network access. Checker verdict integrity remains open below. |
| Controller RPC | Worker operations bind the authenticated key to the claimed workspace; administrative operations require authority. Fresh nonces reject captured exchanges. Durable controller term/holder checks fence stale controller writes. W2 separates handshake and execution admission with per-source and per-principal caps and authority reservation (W2-36), scopes request IDs per workspace (W2-32), bounds the snapshot (W2-33) and recovery (W2-34), and gives each role a key file without others' seeds (W2-37). |
| P5 | Authenticated journals, separate recovery secret, target owner/epoch/head checks and stock export. W2 secures its own path operations and checks recorded export heads. CLI workers themselves remain outside a hostile-process boundary. |

## Findings

| ID | Severity | Finding and disposition |
| --- | --- | --- |
| W2-01 | High | P5 source/cache symlinks and unchecked IDs could escape workspace paths. Fixed with descriptor-relative `O_NOFOLLOW` traversal, regular-file checks, canonical relative names and 64-hex capsule IDs; source-path and snapshot regressions. |
| W2-02 | High | Runtime children inherited Garage admin/RPC secrets. Removed from all audited P5 runtime environment construction; child-environment regression and mutation. Raw S3/FDB client access remains W2-12. |
| W2-03 | Medium | Restored keys followed symlinks or accepted stale local bytes. Atomic private installation, symlink rejection and comparison with authenticated journal plaintext; restoration regressions/mutations. |
| W2-04 | Medium | Explicit export could checkpoint a newly replaced valid target instead of the recorded completed group. Checks before and after export now require exact recorded groups; replacement regression/mutation. |
| W2-05 | High | Lean receipt gate diverged from Rust for target issuers/bindings; cached admission could return a replacement job. Exact target-slot comparison, authority-only target signer and cached envelope ID guard added; real signed Lean fixtures and four mutation cases. |
| W2-06 | Medium | P3 accepted unlimited idle unauthenticated connections and partial frames. Maximum 32 active exchanges, 5-second handshake/write deadlines and a bounded execution wait. Oversized frames rejected before allocation/read; admission, slowloris and frame mutations. Existing work/validation queue limits remain. The single admission pool is superseded by W2-36. |
| W2-07 | Medium | CLI key writes used default permissions and followed destination symlinks; derived debug output exposed seeds. Atomic owner-only inode replacement and redacted debug implementations cover P2, P3 and remote key writers. Symlink/mode/redaction tests and mutations. |
| W2-08 | Medium | Relaxed Ed25519 verification accepted weak-key identity signatures if a weak key entered trust configuration. Strict verification rejects small-order keys/points; identity forgery regression and mutation. Correctly generated signatures still verify. Per-path coverage, vectors and mutations: W2-24. |
| W2-09 | Medium | PCE count checks bounded wire bytes but allowed much larger container allocation; S3 body collection was unbounded. Decoder container/string budget is 64 MiB; S3 reads are bounded to 65 MiB and 60 seconds per body. Lean varints have a ten-byte canonical u64 bound. Boundary regressions/mutations cover rejection. This does not bound total memory of arbitrary caller code. |
| W2-10 | High | Garage's loopback S3 port bypassed delete denial for other local clients with an S3 key; encoded query keys bypassed gateway classification. Instance/default/P3 launch configs use owner-private Unix sockets; startup checks reject the legacy TCP path. Decoded write-query allowlist denies deletion/configuration changes. Tests retain legitimate signed PUT/GET and checksum rejection. |
| W2-11 | High | Untrusted checker had host filesystem/network/process access. Now contained in a rootless Bubblewrap sandbox inside a transient systemd cgroup scope: no network, read-only host except a size-capped scratch tmpfs, x86_64 seccomp allowlist (io_uring and TIOCSTI/TIOCLINUX closed), hard cgroup memory/task limits plus rlimit/RSS second layers, fail-closed with no unsandboxed fallback, single-use processes. Evidence, mutation results and overhead in the section below and w2-sandbox-notes.md. This closes the host/key-containment part of W2-11; it does **not** close W2-13 (verdict provenance inside the checker process). |
| W2-12 | High if workers were hostile; **accepted** (trusted agents) | P5 CLI workers share the controller UID, can read outside workspaces and hold raw store access. A sentinel reproduction confirms filesystem reach. Needs narrowly mounted worker isolation plus authenticated brokered storage operations; current direct FDB access cannot be made safe by client-side guards. | **Disposition (finish pass):** P5's coding agents are trusted in the deployment's operating mode, so a worker that misuses the controller's Unix account or its store access is outside the threat model, and no worker sandbox is added. The path, symlink and size fixes for worker-controlled files (W2-01, W2-20, W2-49 to W2-53) stay as robustness against mistakes. If untrusted workers are ever admitted, this must be revisited: a narrowly mounted worker sandbox, the cluster file, S3 keys and signing seed withheld, and a broker limited to `plr fetch-pkg`/`fetch-group` for the worker's own cache. |
| W2-13 | High | Package source/native execution and trusted replay shared a checker address space, and the signer trusted that process's stdout. **Fix available, opt-in (`PARALEAN_CHECKER_SPLIT=on`); off by default**, because publishing agents are trusted in the usual operating mode and the split costs a second process per check. With the split on: `paralean source-check` (the old pipeline, sandboxed, single-use) now contributes only evidence: per group whether the capsule re-elaborates to its declaration ID, and the reserved constants it re-realized, encoded with the payload encoding. A fresh sandbox then runs `paralean kernel-check` (`Paralean/KernelCheck.lean`), which elaborates no capsule. It opens only the pinned imports, decodes every group's content-addressed stored terms under names it chooses itself, adds them and the evidence's reserved constants with the stock kernel, audits axioms from its own kernel environment, and re-derives each pinned target's statement hash from the stored bytes. Its `CHECK` line is the verdict; the evidence can only cause a rejection. The warm transport runs the frontend, and the kernel check is always cold. On all 97 core fixtures the split agrees with the old checker (83 accepted, with identical axioms and statement hashes, including 16 realized reserved constants). With forged "all source replays succeeded" evidence, every negative fixture is still rejected. Cost: one more process, about 0.6-0.8 s per check on core imports. When the split is on, the checker version (and so each receipt) records it. Test `forged_frontend_acceptance_cannot_pass_the_kernel_check` (a stand-in compromised frontend forges acceptance and evidence; the real kernel check rejects sorry, new-axiom, ill-typed and `native_decide` groups and still accepts a genuine one); `mutate-verdict-from-frontend`. **Residual:** the source-identity verdict (that a capsule's text produces its stored terms) still comes from the frontend; kernel validity, axioms and target statements do not. |
| W2-14 (A-6) | High | Working copies wrote files at another worker's `Marker.filePath` (`Copy.sync`) with no path rule anywhere, so `../../.bashrc` or `.git/config` reached every syncing copy. Fixed with one canonical relative-path rule (non-empty, at most 1024 bytes, relative, no `\`, NUL or ASCII control character, non-empty components that are not `.`, `..` or `.git` in any ASCII case, a `.lean` file with a non-empty stem): `objects::check_file_path` (Rust) and `Safety.checkRelPath` (Lean) are the same rule. Marker and tombstone decoding refuses it (T9 import, every store read), the writer refuses it before T1/T8 (`Writer::check_package`, `Writer::tombstone`), `plr` and the P5 store bridge refuse it where they construct markers or deliver records, Lean refuses it when records decode (`P3.Marker.ofJson`/`Tomb.ofJson`, together with 64-hex record IDs), and `Copy.sync` joins with `Safety.safeJoin`, which re-checks the rule and refuses symbolic links below the work tree. T1 itself (`meta.rs`) does not decode the staged marker value, so a raw FDB writer (W2-12) is still not stopped there; receivers and working copies are. Regressions: Rust unit, T1/T8/T9 cluster tests, `plr` cache tests, Lean unit tests; mutations `mutate-unchecked-file-path`, `mutate-unchecked-publish-path`, `rel_path_dot_component`, `marker_file_rule`, `safe_join_symlink`. |
| W2-15 (A-7) | High | Export module paths and the generated `lakefile.toml` came straight from capsule metadata: `«..».«..».victim` wrote outside the export directory, and a quote plus newline injected TOML; files were written before reject diagnostics were checked. Fixed: every module name component must be a plain ASCII identifier and map below the export root (`safeModulePath`), checked for all modules before anything is removed or written; TOML strings are escaped; the validator (`checkGroup`), the consumer's capsule loader (`P3.loadCapsule`) and `ws-export` require `capsule.module` to be exactly the module derived from `capsule.file` under the path rule. Lean unit tests and mutations `export_module_path`, `capsule_module_matches_file`. |
| W2-16 (A-8) | Medium | `plr` stored `meta/<gid>.json` under a capsule's self-declared `gid` (path traversal for new `.json` files) and first writer won, while Lean `Store.getMeta` trusted the record. Fixed: `plr` requires a 64-hex package ID and capsule bytes that hash to the capsule ID, and reports a different capsule already stored for that package; Lean `getMeta` requires a 64-hex ID and recomputes the package ID from the record (`GroupRec.packageIdOf`, P1's `H("v0/package", (declId, capsuleID))`) and refuses a mismatch, so a forged record can block but never shadow a package; object IDs are hex-checked too. The scheme allows recomputation only from the record itself (`declId` is checked by the validator's replay). Tests and mutations `mutate-unchecked-pid`, `mutate-unchecked-capsule-id`, `meta_package_id`, `meta_hex_id`. |
| W2-17 (A-11) | Low | The Lean payload decoder's `uvarint` recursed once per byte without a bound. It is now iterative, at most ten bytes (the tenth carrying one bit) and canonical, exactly as `pce.rs`; mutations `payload_varint_overflow`, `payload_varint_canonical`. |
| W2-18 (A-28) | High, partly OPEN | `remote%` elaborated another worker's capsule source in the consumer's own Lean process, and the validator replayed it; `#eval`, `run_cmd`, `initialize`, `elab`/`macro` bodies and similar ran in both (the validator only inside its sandbox), and the `debug.*` guard was a text search that `«debug».skipKernelTC` defeated. Fixed by a command gate on parsed syntax (`Paralean/Gate.lean`, below) applied to every command of a rendered capsule before it elaborates, in the validator (`check-group`) and in the consumer (`remote%`/`remote_decl%`, both for declarations and for effect-only groups). The validator also refuses groups with initializer effects before materialization. End-to-end tests publish receipted-looking capsules (`#eval` and `initialize` writing a sentinel, `«debug».skipKernelTC`) and show refusal with the sentinel absent on both sides; mutations `gate_command_allowlist`, `gate_option_name`, `consumer_gate_call`, `validator_gate_call`, `validator_initializer_refusal`. The residual trust is described in the next section. |
| W2-19 (A-29) | Low | `remote_value%` skipped its receipt check whenever any package was loading. It now skips it only for the package whose capsule is being elaborated at that moment (a stack of loading package IDs; each was receipt-checked immediately before), and the gate refuses `remote_value%` for any other package and `remote%`/`remote_decl%` inside capsules. |
| W2-20 (A-9) | Low | The P5 controller wrote the target receipt and plan into the worker folder through possible symlinks. They are now staged in a fresh owner-only directory under the state directory with `O_EXCL|O_NOFOLLOW`; worker log/prompt files are replaced rather than followed, and controller reads of worker files do not follow links. Tests plant symlinks/hard links to sentinels; three mutations. `impl/p3-remote/scripts/ws.py` wrote `receipt.json`/`plan.json` into the working copy on its publish path the same way; it now stages them in a fresh owner-only temporary directory outside the copy, created with `O_EXCL|O_NOFOLLOW` (`test-ws.py` plants links to sentinels on the plain and target paths; `ws_receipt_private_dir`, `ws_plan_private_dir` in `check-w2-security.sh`). |
| W2-21 (A-20) | Medium | `env.sh` defaulted the P5 recovery secret to the Garage admin token. It now creates a random 256-bit secret once in an owner-only file (`PARALEAN_P5_RECOVERY_SECRET_FILE`), and the controller fails closed if the secret is missing, short, equal to the Garage admin/RPC or S3 credentials, or its file is a symlink, not a regular file, not owned by the controller user or group/world-readable. Journals authenticated under the old admin-token-derived secret no longer verify; affected tasks must be rerun. Two mutations. |
| W2-22 (A-21) | Medium/High | P5 accepted legacy key bundles sealed under a key derived from the S3 secret every worker holds, and S3 keeps old blobs. The runtime now refuses any non-`v2:` bundle and never re-journals one; no in-place migration is offered. **Deployments that ever stored a legacy bundle must treat those seeds as exposed: rotate them (new keys and trust roots), rerun the affected tasks and expire the old journal blobs.** Two mutations. |
| W2-23 (A-23) | Low | P5 child environments used a short denylist. Children now receive no credential-shaped variable (names containing SECRET, TOKEN, PASSWORD, PASSWD, CREDENTIAL, PRIVATE, SEED, API_KEY, ACCESS_KEY, every `PARALEAN_PEER_*`, every `PARALEAN_*` containing KEY) except those each child needs (deployment S3 credentials and key-file path; a coding CLI's own login variables; operator-named passthroughs). A strict allowlist was impractical for arbitrary worker CLIs. Two mutations. |
| W2-24 | Medium | Strict Ed25519 was shared but untested per path: one mutation flipped every path at once, the S ≥ L vectors (S = L, L+1, 2²⁵⁶−1) failed with or without the range check, and nothing compared cofactored and cofactorless behaviour. `sign::verify_path` now lets a mutation restore non-strict acceptance at one call site. The receipt check that staging and T1 share, every anti-entropy import signature (group and tombstone certificates, the federated job issuer), the validator's envelope check and RPC authentication each have their own mutation, detected by a strict-vector regression on that path; the anti-entropy transport, the store verifier and point decoding already had theirs. 103 generated vectors (identity and all eight small-order points as A and as R, every noncanonical y with either sign, negative zero, S ≥ L, a malleated S + L of a valid signature, and mixed-order A and R) give identical verdicts in ed25519-dalek `verify_strict`, OpenSSL, `paralean_crypto::verify` and Lean `Ed25519.verify`. Lean also checks that noncanonical encodings do not decode. `scripts/check-ed25519.sh`: 8/8 Rust path mutations and 10/10 Lean mutations detected. After the merge, W3's registry and W4's shard endpoints add four paths (W2-46, W2-47): 12/12 Rust path mutations detected. |
| W2-25 (A-25) | High | The gateway denied deletes but allowed overwrites: a plain PUT of other bytes, a server-side copy (`x-amz-copy-source`) or a multipart upload replaced a content-addressed object, which destroys it as surely as a delete (readers re-hash and treat it as missing). The gateway now accepts only GET, HEAD and a whole PUT to `.../obj/<kind>/<64 hex>` whose body hashes to that key; an identical retry still succeeds. POST (DeleteObjects, multipart), copy, aws-chunked framing, sub-resource queries and every other key are refused. A live regression (`guards::s3_checksum_delete_and_corruption`) shows an overwrite and a copy refused and the object intact; unit test and `mutate-allow-overwrite`. Corruption-at-rest tests now write to Garage's private socket directly. |
| W2-26 (A-24, A-26) | High (operational) | Secret-bearing files kept an older script's group- and world-readable mode (`garage.toml` with the RPC secret and admin token; `fdb.cluster`), and FoundationDB's connection string, its only client credential, was printed by the cluster scripts and committed in 11 result logs. Every start now makes the instance, FDB and Garage directories 0700 and their files 0600; the boundary check refuses a group- or world-accessible `garage.toml`, `fdb.cluster` or directory (test plus mutation `private_secret_files`); the string is no longer printed; the committed copies are redacted and `check-w2-security.sh` fails on a new one. Git history still holds them: those development clusters are exposed and must be recreated before any real use. The shared `~/paralean-p3-control-cluster` predates this and was 0664; it was not otherwise changed by W2. FoundationDB itself has no client authentication: mutual TLS (or tenants with authorization tokens) is the remaining fix for a multi-user host, recorded under W2-12. |
| W2-27 (A-22) | Medium | `garage key import ID SECRET` put the S3 secret on a command line every local user can read in `/proc`. Keys are now imported through Garage's admin API, with the bearer token and request body read from owner-only files by `curl` (`impl/p2/scripts/private.sh`); checked on a fresh instance. |
| W2-28 (A-2) | Medium | Anti-entropy import (T9) skipped T1's cancellation read and dependency guard, so a request the authority cancelled after its receipt was issued could still be published through a peer serving the worker's receipt and self-signed certificate. T9 now reads the issuer's cancellation in its transaction for jobs this deployment signed, and applies T1's dependency-published-and-certified guard. Receipts model with RelayReceive/RemoteReceive and negative cases; tests `cancelled_request_is_not_received_by_its_issuer`, `received_group_waits_for_job_dependencies_here`, `federated_import_rejects_a_cancelled_local_request`; mutations `mutate-receive-no-cancel-check`, `mutate-receive-no-dep-check`. Cancellations do not propagate between deployments. |
| W2-29 (A-4) | Medium | A target's statement was chosen by the worker: the controller copied the worker's statement into the envelope, and an empty one disabled the validator's comparison, so a target head could move to a proof of another statement under the target's name (only P5 caught this, after the fact). The authority now pins a statement hash per name, write-once (`tstatement/<name>`): the P3 controller's `Assign`/`AssignGroup` take it, P5 always passes its frozen contract hash and fails closed without one, the controller stamps the pinned statement into every job, and T1 refuses a binding with any other. Targets model (TargetsStatement); tests `t1_requires_the_pinned_target_statement`, `assignment_pins_the_statement_the_controller_stamps`, P5 `test_assign_statement`; mutations `mutate-no-statement-pin-check`, `mutate-no-statement-stamp`, `assign_statement_pin`. An unpinned name keeps the old behaviour. |
| W2-30 (A-12) | Medium | Anti-entropy collection was unbounded: per-event caps applied only at import, and the puller fetched and stored every listed object first, so one authenticated peer could fill the receiver's FDB and append-only S3. Each event now has part, fragment, inline-byte and declared-object-byte caps enforced when parts persist (an over-cap event becomes terminal before anything it names is fetched), plus a per-source declared-byte cap. Ingress model event caps; three mock-peer tests and mutations. Objects of an event later rejected stay in S3. |
| W2-31 (A-5) | High | The validator wrote `meta/<gid>.json` with `gid` taken from capsule JSON, in the signing parent outside the sandbox: `../` or an absolute gid wrote attacker JSON anywhere (for instance over a key file), and a comma injected checker arguments. The gid must be 64 lowercase hex, duplicates are refused, and the scratch store is a fresh 0700 directory written with `create_new`. Tests in `adversarial.rs` and `p1.rs`; `mutate-unchecked-gid`. |
| W2-32 (A-1) | Medium | Request IDs were global, so one worker could pre-claim another's request (for instance the guessable `dep/<decl>`) and block its validation forever. J1/J2/J3 keys, the controller's in-flight map and validator slots are scoped by workspace (and issuer key). Tests `request_ids_are_scoped_per_workspace`, `validator_slots_are_scoped_by_issuer_and_workspace`; two mutations. Not modelled: the TLA models do not represent request keys. |
| W2-33 (A-13) | Medium | The controller snapshot grew without bound (worker-chosen poll tokens, finished work, never-cleared chunks) until saves failed and every operation became inconclusive. Request IDs and tokens are capped at 256 bytes, 16 poll tokens are kept per live worker, finished work beyond 1,024 is dropped oldest first, and the head swap clears superseded chunks in the same transaction. Two tests, three mutations. **Changed by the merge:** dropped entries now spill into W4 replay rows (W2-43), and superseded chunks are retired for W4's GC, now on by default (W2-41), instead of being cleared in the swap. |
| W2-34 (A-14) | Medium | Inconclusive envelopes were redispatched on every lease tick forever. Recovery runs once per takeover and each envelope at most `validator_attempts` times, counted durably and lease-fenced. Test `inconclusive_recovery_is_bounded`; `mutate-recover-every-tick`. |
| W2-35 (A-15) | Medium | When the RPC execution deadline dropped a validation future, the validator leaked its queued counter, slot and scratch directory, and later retries got "check abandoned". Checks now run in their own task, with RAII guards. Test `dropped_validation_still_finishes_and_releases_its_resources`; `mutate-attached-validation`. |
| W2-36 (A-16) | Medium | RPC admission was 32 global slots shared by unauthenticated handshakes and authenticated executions: 32 idle sockets, or one worker's long validations, locked out the authority. Handshakes now have 128 slots (32 per source IP), released at authentication; executions have 32 slots reserved for the authority and 64 shared slots (16 per principal). Two tests, two mutations. Supersedes W2-06's single pool. |
| W2-37 (A-19) | Medium | Every P3 role loaded the full key file, so a compromised validator held the authority seed. `paralean-p3 keys export --role validator|controller|worker` writes role files, and each process refuses a key file with seeds it does not need; P5 and p3-remote launch validators with role files. Tests and `mutate-role-keys-unchecked`. |
| W2-38 (A-18) | Low | RPC signatures bound domain, nonce and payload but not the server, so a validator could relay an authority-signed request to the controller. Every challenge, request and response now binds a service tag and the server's public key (v2 domains). Test and mutation. |
| W2-39 (A-10, A-17, A-30) | Low | The default validator workdir was a shared predictable `/tmp` path (now per-user, 0700, owner- and symlink-checked); issuer envelopes binding targets were checked although they can never stage (now refused first); `published_receipt` counted any key under `certs_of` (now one certificate that verifies). Each has a test and mutation. Worker `capacity_mb` and issuer memory/deadline requests remain self-asserted within the existing clamps. |
| W2-40 (A-27) | Info | Garage's admin `/metrics` endpoint was unauthenticated (no `metrics_token`); it exposes cluster statistics, not data or credentials. `up.sh`, `bootstrap.sh` and P3's `cluster-up.sh` now generate a random `PARALEAN_GARAGE_METRICS_TOKEN` in the owner-only `credentials.sh` (added to an existing file that lacks one) and write it as `[admin] metrics_token`. The boundary check refuses a `garage.toml` without a 32-character token, and a running Garage whose `/metrics` answers without it or refuses it (one started before its config had a token: restart it; the default cluster needs `bootstrap.sh` again to rewrite its config). On a fresh instance `/metrics` answered 403 without a token, with a wrong one and with the admin token, and 200 with the metrics token. Test `test_metrics_require_the_config_token`; `metrics_token_required`, `metrics_unauthenticated_refused`. |
| W2-41 | Medium (merge) | W4's controller binary left snapshot and history GC off unless `--gc`. Every state change retires the previous snapshot (W4 no longer clears it in the head swap, which superseded W2-33's chunk clear), so without the collector FDB grew by one snapshot per change and the snapshot's settled history was never compacted. The controller now collects unless `--no-gc`; the library default stays off for tests. Test `controller_collects_unless_told_not_to`; `mutate-gc-off-by-default`. |
| W2-42 | Medium (merge) | W4's validation shard route and shard-local job index were keyed by request ID alone, so one workspace's request ID routed (and so blocked or squatted) another workspace's identical ID: W2-32 reopened across shards. Both keys are now (workspace, request), like J1-J3, and recovery checks the scoped route. Test `sharded_validation_routes_are_scoped_per_workspace`; `mutate-unscoped-job-keys` (now unscopes both). |
| W2-43 | Medium (merge) | W2-33 evicted poll tokens and finished work from the snapshot, but W4's replay history requires that nothing leaves it without an immutable replay row committed in the same transaction (a retried token must not get a fresh poll's answer); and W4 alone, with GC off, kept them all. Over-cap entries (a worker's tokens beyond its newest 16, finished work beyond 1,024 that no kept token names) now spill into W4 replay rows atomically with the save, at most 200 KiB per save; a row over FDB's 90 KiB value limit stays in the snapshot rather than failing every save. W2's expiry step that deleted a dead worker's tokens outright is removed (re-verification found that W4's `mutate-history-no-poll-epoch` survived because of it). Tests `worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot`, `one_save_spills_within_its_budget`, `rows_over_the_value_limit_stay_in_the_snapshot`, `spilled_poll_tokens_keep_their_first_answer`; `mutate-unbounded-poll-responses`, `mutate-no-work-gc`, W4's `mutate-history-omit-poll-marker`. A spilled request resubmitted is now a `Duplicate`, not new work. |
| W2-44 | Low (merge) | The request-ID length bound ran after W4's shard routing, which writes a durable work-shard reservation and target claim for the ID. It now runs before routing. Test `overlong_request_id_is_refused_before_shard_routing`; `mutate-unbounded-poll-responses`. |
| W2-45 | Low (merge) | W3's rotation-aware writer verification (`FederationMember::verify_writer`, `KeyRing::signing_writer_key`) bypassed the anti-entropy import path verifier, so `mutate-relaxed-import-sig` no longer covered those import signatures (they stayed strict through `sign::verify`). W2's line, kept by the textual merge, would also have narrowed import to current keys and broken W3 rotation. Import now uses `verify_writer_path` / `signing_writer_key_path` with the import flag everywhere. Tests `antientropy_import_strict_signature_vectors`, `antientropy_group_import_strict_signature_vectors`; `mutate-relaxed-import-sig`. |
| W2-46 | Low (coverage) | W3's agent-key grant, agent-key revocation and controller deletion grant verified strictly but had no per-path regression. Each now verifies through `verify_path` with its own mutation, detected by a strict-vector test (grants and revocations also through FDB registration). Grants name their own issuer; every caller pins it (`active_agent_key_from`, `register_agent_key`, `FederationMember::verify_writer`, the audit), which was checked. Tests `agent_key_grant_strict_signature_vectors`, `agent_key_revocation_strict_signature_vectors`, `controller_delete_grant_strict_signature_vectors`; `mutate-relaxed-agent-grant-sig`, `mutate-relaxed-agent-revocation-sig`, `mutate-relaxed-controller-delete-sig`. |
| W2-47 | Low (coverage) | W4's sharded controller endpoints use W2's RPC verifier and admission (`serve_authenticated`, `call_authenticated`); no path of their own existed. A live two-shard test sends every strict vector on each shard's own challenge, with each vector's key configured as a workspace writer (W2-08's threat). Test `sharded_controller_rpc_strict_signature_vectors`; `paralean-validator-api/mutate-relaxed-rpc-sig`. |
| W2-48 | Medium (robustness) | Processes that left `main` with FDB's network thread running crashed in libfdb_c's exit-time destructors (about 1% of exits right after dropping a database; stack in w2-chaos-notes.md). This was the post-test SIGSEGV of the stock-harness suites and the exit shape of the pre-`667dcf6` stress worker; the P3 controller/validator, `plr` and the P5 bridge still had it. Every FDB test suite now runs a `libtest-mimic` main that stops FDB before exiting (an unlisted test is a compile error); binaries use `meta::run_main`. Test `meta::lifecycle_tests::network_stops_before_process_exit`; `mutate-no-network-shutdown` (`check-network-shutdown.sh`); reproducer `scripts/exit-race-repro.sh`. |
| W2-49 | High (W5) | The editor publication write `(work/file).resolve().write_text(buffer)` followed links the worker controls: a hard link to any of the controller's files, a symlinked `work/`, or a leaf symlink planted after the last check. It now replaces the file by rename beneath the workspace root without following links, and the pre-commit guard reads no-follow and bounded. Test `test_publish_replaces_planted_source_links_without_writing_through`; `publish_write_no_follow`, `precommit_disk`. |
| W2-50 | Medium (W5) | Capture-worker replies had asyncio's 64 KiB line limit (large captures failed) and an over-limit or malformed reply left a desynchronised worker running. The limit is 64 MiB and any bad reply stops the worker. Tests `test_large_and_overlimit_capture_replies`, `test_malformed_capture_reply_stops_worker`; four mutations. |
| W2-51 | Medium (W5) | The policy probe read worker cache markers unbounded and through links while holding the lock every workspace needs; a planted FIFO hung all of them. Markers are read non-blocking, no-follow, regular files of at most 1 MiB. Tests `test_policy_probe_reads_markers_without_following_worker_links`, `test_policy_probe_rejects_sparse_oversized_marker`; `probe_marker_bounded_read`. |
| W2-52 | Medium (W5) | The LSP router read worker store files, sources and environment inputs on its event loop unbounded, through links (marker `pid`/`capsule` values could leave the store) and blocking on FIFOs. Bounded, non-blocking, contained reads. Five tests; `router_store_bounded_read`, `router_store_contained_read`, `router_source_bounded_read`, `router_environment_bounded_read`. Two residuals are fixed too: a readable record with a malformed field (a non-integer `startLine`, non-list `publicNames`, non-name entries, mistyped marker or revision fields) raised in `registry_symbols` and left the `workspace/symbol` request unanswered; such entries are now skipped. With `PARALEAN_LSP_DEBUG`, a Lean stderr line over asyncio's 64 KiB limit killed the forwarder, after which Lean blocked on its full stderr pipe; stderr is now read in chunks and lines are cut at 16 KiB. Tests `test_registry_symbols_skip_malformed_entries`, `test_symbol_request_is_answered_despite_malformed_records`, `test_debug_stderr_forwarding_bounds_long_lines`, `test_debug_stderr_forwarding_keeps_lean_running`; seven `router_registry_*` and two `router_stderr_*` mutations. |
| W2-53 | Low (W5) | The editor's source path was not checked against P2's `check_file_path` before validation and the write (T1 still refused it later), and LSP headers accepted any number of lines and repeated or non-decimal `Content-Length`. Tests `test_source_path_rule_matches_p2_check_file_path`, `test_lsp_frame_header_budget`, `test_lsp_frame_content_length_is_single_decimal`; `source_path_rule`, `router_frame_header_budget`, `router_frame_strict_length`. |
| W2-54 | Medium (W3, pre-existing) | Anti-entropy import (T9) returned an error, not a rejection, for a group whose only author-bound certificate does not verify (for example a damaged signature beside another writer's valid certificate). The puller retries an errored event on every round, so one such item from an authenticated peer stalled that source's queue for good. It is now rejected, like every other evidence failure. The convergence proptest found it after the merge; the regression fails on `origin/main` `a5dfc5c` too. Test `group_without_a_valid_author_certificate_is_rejected`; `mutate-author-cert-error`. |
| W2-55 | Low | The checker sandbox's root is bwrap's own tmpfs, which holds the parent directories bwrap creates for each bind target (for example the checker binary's directory). It stayed writable, so a checker could write there: not to the host, but outside the size-capped `/tmp` and `/work` (bounded only by the cgroup memory limit), contrary to W2-11's "read-only except scratch". The sandbox test missed it whenever `TMPDIR` was under `/tmp`; it now places its files outside `/tmp`. The root is remounted read-only after the binds. Test `checker_cannot_read_secrets_write_outside_or_use_network`; `mutate-writable-sandbox-root`. |

## Findings summary

Status: **Fixed** means a regression test and a guard-removal mutation exist and pass
(the mutation is detected) on the final tree; **Covered** means the path was already
strict and gained a per-path regression and mutation; **OPEN** is not fixed.

| ID | Severity | Status | Regression test (mutation evidence in the finding) |
| --- | --- | --- | --- |
| W2-01 | High | Fixed | P5 source-path and snapshot tests (`test_source_paths.py`, `test_export_snapshot.py`) |
| W2-02 | High | Fixed | controller secret child-environment test (`test_child_env.py`) |
| W2-03 | Medium | Fixed | key-restore symlink and stale-key tests (`test_recovery.py`) |
| W2-04 | Medium | Fixed | replaced valid head test (`test_export_snapshot.py`) |
| W2-05 | High | Fixed | `p3_security.py` signed Lean fixtures |
| W2-06 | Medium | Fixed, superseded by W2-36 | `connection_admission_is_bounded_before_authentication`, `incomplete_frames_expire_and_release_admission` |
| W2-07 | Medium | Fixed | `private_key_file_replaces_public_inode_and_symlink`, `debug_does_not_disclose_role_seeds` |
| W2-08 | Medium | Fixed | `weak_public_key_identity_signature_is_rejected` |
| W2-09 | Medium | Fixed | `hostile_counts_are_bounded_before_container_allocation`, `oversized_s3_body_is_rejected_before_hashing` |
| W2-10 | High | Fixed | `test-storage-boundary.py`, s3-guard query tests |
| W2-11 | High | Fixed (host containment) | `sandbox.rs` adversarial suite |
| W2-12 | High (hostile workers) | Accepted: workers are trusted | `reproduce_worker_isolation.py` (documents the shared account) |
| W2-13 | High | Fix opt-in (split check, default off: trusted agents) | `forged_frontend_acceptance_cannot_pass_the_kernel_check` |
| W2-14 | High | Fixed | `marker_and_tombstone_file_paths_follow_the_relative_path_rule`, `file_paths.rs` |
| W2-15 | High | Fixed | Lean `export_module_path`, `capsule_module_matches_file` |
| W2-16 | Medium | Fixed | `put_capsule_refuses_traversing_package_ids_and_mismatched_bytes`, Lean `meta_package_id` |
| W2-17 | Low | Fixed | Lean `payload_varint_overflow`, `payload_varint_canonical` |
| W2-18 | High | Fixed, residual trust OPEN | `lean_security.py` (eval, init, skipkernel refused; benign loads) |
| W2-19 | Low | Fixed | Lean gate tests |
| W2-20 | Low | Fixed | `test_worker_folder_writes.py`, `test-ws.py` |
| W2-21 | Medium | Fixed | `test_recovery_secret.py` |
| W2-22 | Medium/High | Fixed (exposed seeds must be rotated) | `test_key_bundles.py` |
| W2-23 | Low | Fixed | `test_child_env.py` |
| W2-24 | Medium | Fixed | `check-ed25519.sh` path vectors (12/12 Rust, Lean vectors) |
| W2-25 | High | Fixed | `s3_checksum_delete_and_corruption`, `overwrites_copies_and_unaddressed_keys_are_denied` |
| W2-26 | High (operational) | Fixed (old clusters exposed) | `test-storage-boundary.py` `private_secret_files` |
| W2-27 | Medium | Fixed | instance bring-up check (no mutation) |
| W2-28 | Medium | Fixed | `cancelled_request_is_not_received_by_its_issuer`, `received_group_waits_for_job_dependencies_here` |
| W2-29 | Medium | Fixed | `t1_requires_the_pinned_target_statement`, `assignment_pins_the_statement_the_controller_stamps` |
| W2-30 | Medium | Fixed | `endless_event_parts_are_capped_and_archived` and two more `network.rs` tests |
| W2-31 | High | Fixed | `hostile_capsule_gid_is_refused_before_any_write`, `hostile_gid_cannot_escape_the_scratch_store` |
| W2-32 | Medium | Fixed | `request_ids_are_scoped_per_workspace`, `validator_slots_are_scoped_by_issuer_and_workspace` |
| W2-33 | Medium | Fixed (changed by merge, W2-41, W2-43) | `worker_chosen_poll_tokens_and_finished_work_do_not_grow_the_snapshot` |
| W2-34 | Medium | Fixed | `inconclusive_recovery_is_bounded` |
| W2-35 | Medium | Fixed | `dropped_validation_still_finishes_and_releases_its_resources` |
| W2-36 | Medium | Fixed | `long_authenticated_calls_cannot_lock_out_the_authority`, `one_source_cannot_hold_every_handshake_slot` |
| W2-37 | Medium | Fixed | `roles_refuse_key_files_with_other_roles_seeds`, `processes_refuse_key_files_with_seeds_of_other_roles` |
| W2-38 | Low | Fixed | `request_signature_binds_server_key_and_service` |
| W2-39 | Low | Fixed | `validator_workdir_must_be_private_and_ours`, `published_means_a_certificate_that_verifies` |
| W2-40 | Info | Fixed | `test_metrics_require_the_config_token` |
| W2-41 | Medium (merge) | Fixed | `controller_collects_unless_told_not_to` |
| W2-42 | Medium (merge) | Fixed | `sharded_validation_routes_are_scoped_per_workspace` |
| W2-43 | Medium (merge) | Fixed | `spilled_poll_tokens_keep_their_first_answer`, `one_save_spills_within_its_budget` |
| W2-44 | Low (merge) | Fixed | `overlong_request_id_is_refused_before_shard_routing` |
| W2-45 | Low (merge) | Fixed | `antientropy_group_import_strict_signature_vectors` |
| W2-46 | Low (coverage) | Covered | `agent_key_grant_strict_signature_vectors` and two more |
| W2-47 | Low (coverage) | Covered | `sharded_controller_rpc_strict_signature_vectors` |
| W2-48 | Medium (robustness) | Fixed | `network_stops_before_process_exit`; reproducer `exit-race-repro.sh` |
| W2-49 | High (W5) | Fixed | `test_publish_replaces_planted_source_links_without_writing_through` |
| W2-50 | Medium (W5) | Fixed | `test_large_and_overlimit_capture_replies`, `test_malformed_capture_reply_stops_worker` |
| W2-51 | Medium (W5) | Fixed | `test_policy_probe_reads_markers_without_following_worker_links` |
| W2-52 | Medium (W5) | Fixed | `test_registry_symbols_ignore_planted_fifo_and_links` and eight more |
| W2-53 | Low (W5) | Fixed | `test_source_path_rule_matches_p2_check_file_path`, `test_lsp_frame_header_budget` |
| W2-54 | Medium (W3) | Fixed | `group_without_a_valid_author_certificate_is_rejected` |
| W2-55 | Low | Fixed | `checker_cannot_read_secrets_write_outside_or_use_network` |

## Capsule command gate (W2-18) and what remains

**Before the fix.** Neither the validator nor the consumer refused code-running commands.
The validator's source replay elaborated every closure capsule (`#eval` ran inside the
checker; initializer groups were materialized, built and imported with initializers
enabled), and the kernel check of the result does not care what the elaborator executed.
A capsule with `#eval IO.Process.run …` could therefore get a receipt (an effect-only group
produces no members to compare) and run in every teammate's `remote%`. The fixture test
reproduces both halves with the baseline code removed by mutation.

**The gate** (`Gate.checkCommand`) runs on each command's parsed syntax, with the parser
state that will elaborate it, before elaboration (`Capture.processCommandGated` in the
validator's `runCommands`; `Remote.elabSourceAtRoot` in the consumer). It admits:

* command kinds: declarations (including `instance`, `structure`, `inductive`, `axiom` —
  axioms remain a policy matter — and Mathlib's `lemma`), `section`/`namespace`/`end`,
  `open`, `variable`, `universe`, `include`/`omit`, `export`, `attribute`, `set_option`,
  `deriving instance`, `notation` and mixfix, doc comments, and `in`/`mutual` built from
  these;
* options: `maxHeartbeats`/`synthInstance.maxHeartbeats` (not 0), `maxRecDepth`,
  `synthInstance.maxSize`, `autoImplicit`, `relaxedAutoImplicit`, `Elab.async`, `pp.*`,
  `linter.*`, `trace.*`, in command, term and tactic `set_option` alike, identified from the
  parsed name (so `«debug».skipKernelTC` is `debug.skipKernelTC`); the old text search for
  `debug.*` is kept as well;
* attributes: a fixed data-only set (`simp`, reducibility, `instance`, `ext`, `simps`,
  `to_additive`, `norm_cast`, `gcongr`, `grind`, …) and registered simp sets;

and refuses anywhere in the tree: `#eval`/`#eval!`, `run_cmd`/`run_elab`/`run_meta`,
`by_elab`, `run_tac`, `native_decide`, `decide +native`, `unsafe` (modifier or term),
`initialize`/`builtin_initialize`, `macro`/`macro_rules`/`syntax`/`elab`/`elab_rules`,
identifiers naming `reduceBool`/`reduceNat`/`ofReduceBool`/`ofReduceNat` (kernel native
evaluation), every other attribute (`implemented_by`, `extern`, `export`, `init`, elaborator,
macro, delaborator, simproc and tactic-extension attributes, `aesop`, `norm_num`, …), and
`remote%`/`remote_decl%`/`remote_value%` for another package.

**Corpus impact.** Over the no-Mathlib corpus (`gate-corpus-*.json` in
`results/w2/lean-fixes/`) the W2 validator accepts 83 of 97 core groups and every F14, F15,
diagmap, conflict, N5 and duplicate-instance group the baseline accepts. The 14 newly
refused groups are exactly the code-running ones: F12 (`macro`, `syntax`+`macro_rules`,
`elab`, a declared tactic, and the four theorems that use them), F13a (`initialize`,
`register_option`) and F10a (`register_simp_attr`, which is an `initialize`). These cannot
be published any more; they are not provably safe (macro bodies can construct any syntax,
including refused commands, and initializers run arbitrary IO when imported). They still
capture, replay and export locally in P1, where the author's own code is trusted, and
anything that needs them must come from the pinned base imports. M06–M08 and M17 in the
Mathlib corpus are local-capture cases of the same kinds.

**What remains (trust that the gate does not remove):**

1. Elaboration-time code from *imported* packages still runs on capsule input: tactics
   (`simp`, `omega`, Mathlib's automation), term elaborators, notation and macro expansion,
   deriving handlers, and attribute handlers such as `simps`/`to_additive` that generate
   declarations. The pinned base is trusted code, and a bug or hostile extension there is
   reachable from capsule text. With W2-13's split enabled, such a defect can only affect
   the frontend's source-identity evidence, not the kernel verdict.
2. Terms produced by imported tactics may contain `Lean.reduceBool`, which the kernel
   evaluates natively; the gate only refuses capsule text that names it. Proof terms that
   `remote_value%` takes from a payload are refused if any member uses `Lean.reduceBool`
   or `Lean.reduceNat`, but the validator's kernel replay of payloads (inside its sandbox)
   and consumer elaboration of tactic-produced terms do not scan for them.
3. Elaboration cost is bounded only by heartbeats and recursion limits the capsule may raise
   (not to 0); a consumer can still be slowed down.
4. Paths without the gate: P1's local transparent prelude and `paralean merge` replay other
   stores' capsules ungated (P1's local trust model); `ws-export` builds published capsules
   with stock `lake build` and relies on the receipts of the gated validator; the
   validator's own sandbox (W2-11) remains the containment for the replay itself.
5. The attribute and option sets are allowlists by name; an imported attribute macro whose
   syntax kind differs from its attribute name is refused (fail closed) rather than
   expanded.

## Keys, replay and fencing

Authority seeds authorize fence rotation, assignment, revocation and target
envelopes. Issuers authorize target-free envelopes only. Validator seeds sign
receipts; workspace seeds sign writer certificates and authenticate worker
operations. Random key initialization is the deployment path; deterministic
`--demo` keys are explicitly test-only. Secure key-file output is owner-readable
and atomically replaces symlinks or formerly public files. Configured key/import
directories remain operator-controlled. Environment filtering and namespace
mount omission protect validator children; same-UID unsandboxed programs remain
capable of reading operator data.

Validator rotation adds a new public key, then retires/revokes the old key.
R1 revocations are signed and transactionally read by later publication/import;
consumer checks reject revoked published receipts. Removing an issuer or
workspace key requires distributing updated trust configuration and restarting
long-lived processes; there is no general online issuer/workspace revocation
service. Authority rotation is an operator migration, not automatic failover.
In-memory trust caches are not advertised as immediately following edited
configuration files.

Content addressing, write-once request records, nonce-bound RPC and request IDs
separate harmless duplication from replay. An ambiguous FDB commit may return
“already present” on retry: durable effect is the correctness oracle, not
first-attempt freshness. T4 owner/epoch/head and T5 catalogue fence reads occur
inside the committing transaction; cached receipts cannot authorize a new
epoch. T9 respects target homes. Restoring old FDB metadata under an existing
deployment identity remains outside the failure envelope.

## Decoder, storage and availability bounds

PCE rejects bad lengths, tags, trailing bytes, nonminimal integers and
noncanonical sets; W2 adds allocation accounting. Signed outer objects decode
bounded byte slices. Anti-entropy has 1 MiB metadata and 64 MiB object limits
with deadlines and bounded concurrency, and each anti-entropy event and source
now has part and declared-object caps (W2-30). P3 JSON frames are at most
16 MiB; RPC handshakes have 128 slots (32 per source IP) and executions 32
authority-reserved plus 64 shared slots (16 per principal). The gateway bounds
simultaneous connections to 16, at most 4 of them from one source address
(`one_source_cannot_hold_every_connection_slot`, `mutate-no-per-source-admission`),
and each body to 65 MiB, with a whole-connection deadline, and accepts only whole
content-addressed PUTs. The gateway sees addresses, not S3 principals: clients
behind one address share its 4 connections.

FDB limits remain 100,000-byte values, 10,000-byte keys and bounded
transactions. The merged chunk index caps references at 2,048 (worst-case
75,778-byte encoding), with an existing regression. Oversized general metadata
transactions fail rather than partially committing. This audit does not claim
that arbitrarily large valid declarations always fit one transaction.

The new `Ingress` model abstracts connection/byte caps and the append-only
storage boundary. It does not model Linux, seccomp, cryptography, allocator
implementation or process isolation. Existing receipt, target, fencing,
certificate, workspace and hardened model suites remain the protocol evidence.
No new proof-level theorem is claimed.

## Validator containment and evidence

See [w2-sandbox-notes.md](w2-sandbox-notes.md) for the exact launch profile,
adversarial results, legitimate Lean/initializer checks, mutation evidence,
overhead and the precise limits of the boundary. Each checker runs under
Bubblewrap (new user/PID/net/IPC/UTS namespaces, all capabilities dropped,
read-only root but a size-capped scratch tmpfs, an x86_64 seccomp allowlist
including the io_uring and terminal-injection surfaces) inside a transient
systemd user scope that applies hard `MemoryMax`/`MemorySwapMax`/`TasksMax`
limits; an OOM kill maps to a no-verdict memory outcome, with the resident-set
poll kept as a second layer. Memory and process limits therefore each have a
hard cgroup layer and a soft/rlimit layer. The host supports Bubblewrap even
though a direct user-namespace probe fails. Unsupported sandbox startup, a
missing Bubblewrap, or a cgroup whose controllers are not delegated all fail
closed with no verdict; there is no unsandboxed fallback, and the cgroup layer
is required in production (`PARALEAN_CHECKER_CGROUP=off` is an explicit opt-out
for hosts without delegated controllers). Sandboxed checker processes are
single-use: a process that ran one package's code never judges another's.
Production configuration (`CheckerConfig::from_env`) enables the sandbox and the
cgroup layer; mock checker tests explicitly choose their test configuration.
All sandbox and protocol tests pass with none ignored, and every checker guard
has a detecting mutation case.

The sandbox contains each checker process. W2-13's opt-in split keeps the verdict out of
the process that elaborates capsules, and both phases run under this profile. P5's networked
CLI workers are not sandboxed: they are trusted agents (W2-12).

Garage's Unix socket capability is documented in the
[Garage configuration reference](https://garagehq.deuxfleurs.fr/documentation/reference-manual/configuration/#api_bind_addr).
Because Garage creates an S3 socket writable by other users, the private parent
directory is part of the enforced boundary and is tested, not merely the
socket filename.
