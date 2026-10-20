# W2 threat model and security findings

This audit is against `fee94d9` plus the W2 changes recorded in
[w2-log.md](w2-log.md). It is an implementation audit and bounded test campaign,
not a proof of absence of vulnerabilities. **Hostile P5 workers and native code
inside the authoritative Lean checker remain unresolved trust boundaries.**

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

## Path-by-path review

| Path | Current enforcement and limitations |
| --- | --- |
| T1 publication | `receipt::check` checks validator signature, acceptance, group, signed envelope, pinned policy/checker and exact target bindings. T1 transactionally reads revocation, cancellation, every declared target's owner/epoch/head and certified dependencies. Existing guard mutations exercise these reads. |
| Anti-entropy T9/T10 | Authenticated deployment peers, signed certificate validation, receiver-local receipt pins and revocation checks, acknowledged/rehashed payloads, and pinned target homes. Peer authorities become target-free issuers, not local fence authorities. A transport signature alone is insufficient to import a group. |
| Lean `remote%` | Each closure receipt is checked locally and against live store consumer verification. W2 fixes authority-only target signing, exact target bytes, noncanonical/unbounded varints and cached-job replacement. Every capsule command passes the command gate (W2-18) before it elaborates; records, capsule modules/files and package IDs are checked (W2-14 to W2-16). Published-consumer verification reads revocation; cancellation prevents later publication but does not retroactively unpublish content. |
| Validator RPC | Fresh server challenge, signed request and signed response; authority/issuer authorization. Signed job binding/policy/checker/dependency checks precede a receipt. OS containment protects the signing parent from child file/network access. Checker verdict integrity remains open below. |
| Controller RPC | Worker operations bind the authenticated key to the claimed workspace; administrative operations require authority. Fresh nonces reject captured exchanges. Durable controller term/holder checks fence stale controller writes. W2 bounds pre-authentication connections and handshake time. |
| P5 | Authenticated journals, separate recovery secret, target owner/epoch/head checks and stock export. W2 secures its own path operations and checks recorded export heads. CLI workers themselves remain outside a hostile-process boundary. |

## Findings

| ID | Severity | Finding and disposition |
| --- | --- | --- |
| W2-01 | High | P5 source/cache symlinks and unchecked IDs could escape workspace paths. Fixed with descriptor-relative `O_NOFOLLOW` traversal, regular-file checks, canonical relative names and 64-hex capsule IDs; source-path and snapshot regressions. |
| W2-02 | High | Runtime children inherited Garage admin/RPC secrets. Removed from all audited P5 runtime environment construction; child-environment regression and mutation. Raw S3/FDB client access remains W2-12. |
| W2-03 | Medium | Restored keys followed symlinks or accepted stale local bytes. Atomic private installation, symlink rejection and comparison with authenticated journal plaintext; restoration regressions/mutations. |
| W2-04 | Medium | Explicit export could checkpoint a newly replaced valid target instead of the recorded completed group. Checks before and after export now require exact recorded groups; replacement regression/mutation. |
| W2-05 | High | Lean receipt gate diverged from Rust for target issuers/bindings; cached admission could return a replacement job. Exact target-slot comparison, authority-only target signer and cached envelope ID guard added; real signed Lean fixtures and four mutation cases. |
| W2-06 | Medium | P3 accepted unlimited idle unauthenticated connections and partial frames. Maximum 32 active exchanges, 5-second handshake/write deadlines and a bounded execution wait. Oversized frames rejected before allocation/read; admission, slowloris and frame mutations. Existing work/validation queue limits remain. |
| W2-07 | Medium | CLI key writes used default permissions and followed destination symlinks; derived debug output exposed seeds. Atomic owner-only inode replacement and redacted debug implementations cover P2, P3 and remote key writers. Symlink/mode/redaction tests and mutations. |
| W2-08 | Medium | Relaxed Ed25519 verification accepted weak-key identity signatures if a weak key entered trust configuration. Strict verification rejects small-order keys/points; identity forgery regression and mutation. Correctly generated signatures still verify. |
| W2-09 | Medium | PCE count checks bounded wire bytes but allowed much larger container allocation; S3 body collection was unbounded. Decoder container/string budget is 64 MiB; S3 reads are bounded to 65 MiB and 60 seconds per body. Lean varints have a ten-byte canonical u64 bound. Boundary regressions/mutations cover rejection. This does not bound total memory of arbitrary caller code. |
| W2-10 | High | Garage's loopback S3 port bypassed delete denial for other local clients with an S3 key; encoded query keys bypassed gateway classification. Instance/default/P3 launch configs use owner-private Unix sockets; startup checks reject the legacy TCP path. Decoded write-query allowlist denies deletion/configuration changes. Tests retain legitimate signed PUT/GET and checksum rejection. |
| W2-11 | High | Untrusted checker had host filesystem/network/process access. Now contained in a rootless Bubblewrap sandbox inside a transient systemd cgroup scope: no network, read-only host except a size-capped scratch tmpfs, x86_64 seccomp allowlist (io_uring and TIOCSTI/TIOCLINUX closed), hard cgroup memory/task limits plus rlimit/RSS second layers, fail-closed with no unsandboxed fallback, single-use processes. Evidence, mutation results and overhead in the section below and w2-sandbox-notes.md. This closes the host/key-containment part of W2-11; it does **not** close W2-13 (verdict provenance inside the checker process). |
| W2-12 | High, OPEN | P5 CLI workers share the controller UID, can read outside workspaces and hold raw store access. A sentinel reproduction confirms filesystem reach. Needs narrowly mounted worker isolation plus authenticated brokered storage operations; current direct FDB access cannot be made safe by client-side guards. |
| W2-13 | High, OPEN | Package source/native execution and trusted replay share a checker address space. The signer trusts checker stdout. Namespace isolation and response nonces do not authenticate results against code in that same process. A separate trusted verifier must consume independently checked immutable kernel inputs and execute no package code. Static review only; no exploit demonstrated. |
| W2-14 (A-6) | High | Working copies wrote files at another worker's `Marker.filePath` (`Copy.sync`) with no path rule anywhere, so `../../.bashrc` or `.git/config` reached every syncing copy. Fixed with one canonical relative-path rule (non-empty, at most 1024 bytes, relative, no `\`, NUL or ASCII control character, non-empty components that are not `.`, `..` or `.git` in any ASCII case, a `.lean` file with a non-empty stem): `objects::check_file_path` (Rust) and `Safety.checkRelPath` (Lean) are the same rule. Marker and tombstone decoding refuses it (T9 import, every store read), the writer refuses it before T1/T8 (`Writer::check_package`, `Writer::tombstone`), `plr` and the P5 store bridge refuse it where they construct markers or deliver records, Lean refuses it when records decode (`P3.Marker.ofJson`/`Tomb.ofJson`, together with 64-hex record IDs), and `Copy.sync` joins with `Safety.safeJoin`, which re-checks the rule and refuses symbolic links below the work tree. T1 itself (`meta.rs`) does not decode the staged marker value, so a raw FDB writer (W2-12) is still not stopped there; receivers and working copies are. Regressions: Rust unit, T1/T8/T9 cluster tests, `plr` cache tests, Lean unit tests; mutations `mutate-unchecked-file-path`, `mutate-unchecked-publish-path`, `rel_path_dot_component`, `marker_file_rule`, `safe_join_symlink`. |
| W2-15 (A-7) | High | Export module paths and the generated `lakefile.toml` came straight from capsule metadata: `«..».«..».victim` wrote outside the export directory, and a quote plus newline injected TOML; files were written before reject diagnostics were checked. Fixed: every module name component must be a plain ASCII identifier and map below the export root (`safeModulePath`), checked for all modules before anything is removed or written; TOML strings are escaped; the validator (`checkGroup`), the consumer's capsule loader (`P3.loadCapsule`) and `ws-export` require `capsule.module` to be exactly the module derived from `capsule.file` under the path rule. Lean unit tests and mutations `export_module_path`, `capsule_module_matches_file`. |
| W2-16 (A-8) | Medium | `plr` stored `meta/<gid>.json` under a capsule's self-declared `gid` (path traversal for new `.json` files) and first writer won, while Lean `Store.getMeta` trusted the record. Fixed: `plr` requires a 64-hex package ID and capsule bytes that hash to the capsule ID, and reports a different capsule already stored for that package; Lean `getMeta` requires a 64-hex ID and recomputes the package ID from the record (`GroupRec.packageIdOf`, P1's `H("v0/package", (declId, capsuleID))`) and refuses a mismatch, so a forged record can block but never shadow a package; object IDs are hex-checked too. The scheme allows recomputation only from the record itself (`declId` is checked by the validator's replay). Tests and mutations `mutate-unchecked-pid`, `mutate-unchecked-capsule-id`, `meta_package_id`, `meta_hex_id`. |
| W2-17 (A-11) | Low | The Lean payload decoder's `uvarint` recursed once per byte without a bound. It is now iterative, at most ten bytes (the tenth carrying one bit) and canonical, exactly as `pce.rs`; mutations `payload_varint_overflow`, `payload_varint_canonical`. |
| W2-18 (A-28) | High, partly OPEN | `remote%` elaborated another worker's capsule source in the consumer's own Lean process, and the validator replayed it; `#eval`, `run_cmd`, `initialize`, `elab`/`macro` bodies and similar ran in both (the validator only inside its sandbox), and the `debug.*` guard was a text search that `«debug».skipKernelTC` defeated. Fixed by a command gate on parsed syntax (`Paralean/Gate.lean`, below) applied to every command of a rendered capsule before it elaborates, in the validator (`check-group`) and in the consumer (`remote%`/`remote_decl%`, both for declarations and for effect-only groups). The validator also refuses groups with initializer effects before materialization. End-to-end tests publish receipted-looking capsules (`#eval` and `initialize` writing a sentinel, `«debug».skipKernelTC`) and show refusal with the sentinel absent on both sides; mutations `gate_command_allowlist`, `gate_option_name`, `consumer_gate_call`, `validator_gate_call`, `validator_initializer_refusal`. The residual trust is described in the next section. |
| W2-19 (A-29) | Low | `remote_value%` skipped its receipt check whenever any package was loading. It now skips it only for the package whose capsule is being elaborated at that moment (a stack of loading package IDs; each was receipt-checked immediately before), and the gate refuses `remote_value%` for any other package and `remote%`/`remote_decl%` inside capsules. |
| W2-20 (A-9) | Low | The P5 controller wrote the target receipt and plan into the worker folder through possible symlinks. They are now staged in a fresh owner-only directory under the state directory with `O_EXCL|O_NOFOLLOW`; worker log/prompt files are replaced rather than followed, and controller reads of worker files do not follow links. Tests plant symlinks/hard links to sentinels; three mutations. `impl/p3-remote/scripts/ws.py` still writes `receipt.json`/`plan.json` into the worker directory on the non-target publish path. |
| W2-21 (A-20) | Medium | `env.sh` defaulted the P5 recovery secret to the Garage admin token. It now creates a random 256-bit secret once in an owner-only file (`PARALEAN_P5_RECOVERY_SECRET_FILE`), and the controller fails closed if the secret is missing, short, equal to the Garage admin/RPC or S3 credentials, or its file is a symlink, not a regular file, not owned by the controller user or group/world-readable. Journals authenticated under the old admin-token-derived secret no longer verify; affected tasks must be rerun. Two mutations. |
| W2-22 (A-21) | Medium/High | P5 accepted legacy key bundles sealed under a key derived from the S3 secret every worker holds, and S3 keeps old blobs. The runtime now refuses any non-`v2:` bundle and never re-journals one; no in-place migration is offered. **Deployments that ever stored a legacy bundle must treat those seeds as exposed: rotate them (new keys and trust roots), rerun the affected tasks and expire the old journal blobs.** Two mutations. |
| W2-23 (A-23) | Low | P5 child environments used a short denylist. Children now receive no credential-shaped variable (names containing SECRET, TOKEN, PASSWORD, PASSWD, CREDENTIAL, PRIVATE, SEED, API_KEY, ACCESS_KEY, every `PARALEAN_PEER_*`, every `PARALEAN_*` containing KEY) except those each child needs (deployment S3 credentials and key-file path; a coding CLI's own login variables; operator-named passthroughs). A strict allowlist was impractical for arbitrary worker CLIs. Two mutations. |

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
   declarations. This is the W2-13 class: the pinned base is trusted code, and a bug or
   hostile extension there is reachable from capsule text.
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
with deadlines and bounded concurrency. P3 JSON frames are at most 16 MiB.
The gateway bounds simultaneous connections to 16 and each body to 65 MiB,
with a whole-connection deadline. Aggregate caps are finite but not a
per-principal fairness guarantee.

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

The sandbox does not close W2-13. Nor does it sandbox P5's networked CLI
workers. Completion of the remaining hostile-code boundary requires both a
trusted verifier process separation and a brokered worker/store design.

Garage's Unix socket capability is documented in the
[Garage configuration reference](https://garagehq.deuxfleurs.fr/documentation/reference-manual/configuration/#api_bind_addr).
Because Garage creates an S3 socket writable by other users, the private parent
directory is part of the enforced boundary and is tested, not merely the
socket filename.
