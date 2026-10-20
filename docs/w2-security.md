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
| Lean `remote%` | Each closure receipt is checked locally and against live store consumer verification. W2 fixes authority-only target signing, exact target bytes, noncanonical/unbounded varints and cached-job replacement. Published-consumer verification reads revocation; cancellation prevents later publication but does not retroactively unpublish content. |
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
| W2-11 | High | Untrusted checker had host filesystem/network/process access. Rootless sandbox work is described below; final evidence and resource limitations must be read before treating this as closed. |
| W2-12 | High, OPEN | P5 CLI workers share the controller UID, can read outside workspaces and hold raw store access. A sentinel reproduction confirms filesystem reach. Needs narrowly mounted worker isolation plus authenticated brokered storage operations; current direct FDB access cannot be made safe by client-side guards. |
| W2-13 | High, OPEN | Package source/native execution and trusted replay share a checker address space. The signer trusts checker stdout. Namespace isolation and response nonces do not authenticate results against code in that same process. A separate trusted verifier must consume independently checked immutable kernel inputs and execute no package code. Static review only; no exploit demonstrated. |

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
overhead and memory/process limitations. The host supports Bubblewrap even
though a direct user-namespace probe fails. Unsupported sandbox startup must
fail closed. Production configuration enables the sandbox; mock checker tests
explicitly choose their test configuration.

The sandbox does not close W2-13. Nor does it sandbox P5's networked CLI
workers. Completion of the remaining hostile-code boundary requires both a
trusted verifier process separation and a brokered worker/store design.

Garage's Unix socket capability is documented in the
[Garage configuration reference](https://garagehq.deuxfleurs.fr/documentation/reference-manual/configuration/#api_bind_addr).
Because Garage creates an S3 socket writable by other users, the private parent
directory is part of the enforced boundary and is tested, not merely the
socket filename.
