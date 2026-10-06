# P3 control plane: validators and the controller

Implements the control-plane half of [docs/plan.md](../../docs/plan.md) P3: validators that
sign Ed25519 receipts bound to an immutable job envelope, and a controller that assigns
targets with P2's T4, dispatches work and validation, deduplicates retries, cancels,
admits work within each worker's memory, applies backpressure and reassigns the targets of
a worker whose lease expired. The publication transaction T1 of P2 checks the receipt
binding itself. Log, decisions and deviations: [docs/p3-log.md](../../docs/p3-log.md).
`remote%` across machines builds on these receipts in the P3 remote-imports work.

## Reproduce

```
impl/p2/scripts/bootstrap.sh       # once: FDB 7.3 + Garage binaries (P2)
impl/p3/scripts/cluster-up.sh      # this instance: FDB :4989, Garage :18739-18741, s3-guard :18733
impl/p3/scripts/test.sh            # builds impl/p1 and its fixture stores if missing; 20 tests
impl/p3/scripts/check-mutations.sh # 13 check-removal mutations; each named test must fail
impl/p3/scripts/cluster-down.sh
```

`scripts/env.sh` takes every port and the data prefix from `PARALEAN_P3_*` variables, uses
the binaries P2's bootstrap installed (read-only) and sources impl/p1's `env.sh` for the
checker (`PARALEAN_BIN`, the toolchain; `PARALEAN_LEAN=fork` selects the fork). The tests
read the P1 stores of `impl/p1/scripts/run-core.sh` (F01–F13) and `run-negative.sh`
(N1–N6) under `.runs/`.

## Layout

| Path | Contents |
|---|---|
| `impl/p2/crates/store/src/receipt.rs` | **receipt format and staging rule** (`paralean_store::receipt`): job envelope, policy, checker version, target bindings, revocation, `check`, P3's write-once transactions J1–J3 and R1 |
| `crates/validator-api` | **validator API** (`paralean-validator-api`): wire types, `validate` client, framing, `published_receipt` for consumers |
| `crates/control` | `paralean-control` library and the `paralean-p3` binary: `checker`, `validator`, `controller`, `worker`, `p1`, `server` |
| `crates/control/tests` | `adversarial.rs` (12), `control.rs` (6), `processes.rs` (1), `fork.rs` (1; fork-mode validators, skipped without a fork build), `measure.rs` (ignored; check costs on F01–F13) |
| `impl/p1` `check-group` | the validator's Lean side: one group from its exact closure; source replay, stock-kernel replay, axioms from the kernel, re-derived statement hashes |

Both crates are members of impl/p2's cargo workspace (`impl/p2/Cargo.toml`), so they share
its lock file and build directory.

## Receipt binding (OPEN-7)

The §6 receipt body is unchanged in shape; P3 fixes the contents of three slots:

| Slot | Contents |
|---|---|
| `validatorBin` | ID of `CheckerVersion {leanGithash, checkerSha256, mode}` (`v0/checker`) |
| `requestID` | ID of the `JobEnvelope` (`v0/job`) the receipt answers; required |
| `targetID` | PCE `set` of `TargetBinding {name, epoch, statement}`, or none |

`JobEnvelope {request, group, capsule, deps, base, policy, checker, worker, targets,
deadlineMs, memoryMb}` is signed by the controller (the fence authority key). The staging
rule `receipt::check` requires a receipt signed by a configured validator key, accepted,
naming the group, bound to a controller-signed envelope whose group, base, policy, checker
and targets equal the receipt's, a pinned policy and checker, and exactly the target names
and epochs the publication was prepared under. Workers run it before staging; T1 runs it
again inside the publication transaction and also reads `vrevoke/<key>` and
`jobcancel/<request>` there, and refuses a revision of any name that has a target record
unless it is a prepared target.

## Processes

```
paralean-p3 keys init keys.json [--validators N] [--workspaces N]   # pins policy v1 and this checker
export PARALEAN_KEYS=keys.json PARALEAN_DEPLOYMENT=demo
paralean-p3 validator  --listen 127.0.0.1:7001 --key v0
paralean-p3 validator  --listen 127.0.0.1:7002 --key v1
paralean-p3 controller --listen 127.0.0.1:7000 --validators 127.0.0.1:7001,127.0.0.1:7002
paralean-p3 worker --name w0 --controller 127.0.0.1:7000 --p1-store .runs/p1-core/store
paralean-p3 submit --controller 127.0.0.1:7000 --request r1 --target F04.red_ne_green
paralean-p3 keys add-validator keys.json v2 | keys retire-validator keys.json v0 | keys revoke-validator v0 "reason"
```

Requests and answers are length-prefixed JSON frames over TCP, one exchange per connection
(`validator-api/src/rpc.rs`; types in `ValidatorRequest`/`ValidatorResponse` and
`ControlRequest`/`ControlResponse`).

## Module → mechanism → guard

| Where | Mechanism | Guard it implements |
|---|---|---|
| `receipt::check`, `writer::check_package`, `meta::t1_body` | staging rule before staging and inside T1 | PublicationReceipts `Guard`/`receipt_sound`; contract "policy and checker version bound, pinned" |
| `meta::t1_body` (`vrevoke/`, `jobcancel/`) | revocation and cancellation read in T1 | fail-closed revocation; cancelled requests never publish |
| `meta::t1_body` (`UndeclaredTarget`) | every revision of a target name is fenced | TargetNames: every group declaring a target name is guarded |
| `controller::validate` | owner check and epoch stamp from the target record | TargetNames `PrepareOk` (i) at dispatch; receipts carry the epoch |
| `controller::expire_leases` | immediate T4 on lease expiry | TargetNames `reassign`; stale owner fenced by T1's epoch check |
| `validator::fetch_inputs` | dependencies must be published with a receipt that verifies | §6 "rebuilds from the dependency groups' receipted manifests" |
| `validator::check`, `checker::run` | stock-kernel re-check; axioms from the kernel; policy; statement | §6 axiom policy; target contracts |
| J1/J2 (`jobreq/`, `jobreceipt/`), in-flight map | retry deduplication by request ID | — |
| `checker::run` | deadline, resident-memory watchdog, kill on cancel | "timeout/unavailable bytes are inconclusive" |
