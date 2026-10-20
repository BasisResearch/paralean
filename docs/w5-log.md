# W5: LSP to controller wiring

Started from `fee94d9` on branch `w5-lsp-wiring`, 2026-10-20. The parent
delegated controller integration, transactional rename, and Lean recapture /
method discovery to three GPT-6 Sol agents, and owns review, formal modeling,
SSH measurements, integration verification and commits.

## Isolation

W5 owns `.runs/w5/cluster`, instance `p5-w5`, FDB port 23589, Garage
23639–23641, S3 gateway 23633 and validator 23691. The attempted choices 5289
and 19333 were occupied; startup refused them before touching their services.
Source `impl/p5/scripts/w5-env.sh` to reproduce this configuration.
Private P1 build artifacts were copied from P4; shared caches are not rebuilt.
TLC runs use one worker each. Initial free space under `/data` was 244 GB.

The SSH test uses a separate user-space `sshd` bound to localhost port 22955,
with private host/client keys and a pinned known-hosts file under `.runs/w5`.
Its authenticated host reports `aws-dev`. Editor and worker roots are distinct.
The delay proxy delays both encrypted byte streams without modifying network
settings. This is a real loopback SSH test, not a second physical machine.

## Protocol model before implementation

`verification/tla/EditorWiring.tla` models three finite scenarios:

- Publication requires a validator receipt, explicit action or policy, and
  the captured document/environment/generation stamp still being current.
  Policy advancement invalidates old editor sessions.
- Rename requires every participant, complete dependency inventory, valid
  plans and current stamps, with one atomic change of the buffer set.
- Derived legacy field metadata requires identity matching and verified
  replay; it does not replace signed capsule bytes.

Initial checks passed: publication 178 distinct states, rename 872, private
replay 5. Eleven guard removals produce the expected safety counterexamples;
three reachability cases establish publication, rename and replay are possible.
The scenarios and mutations are wired into the normal check scripts. Full
suite and archive verification are pending at this checkpoint.

## SSH evidence

`impl/p4/tests/ssh_gate.py` sends actual LSP frames through the router and SSH
to a separately rooted persistent Lean worker. It edits an unsaved buffer,
checks error and clean diagnostics, exact source/version, hover, goals and
completion. The initial ten-sample baseline passed using the existing P4 fork
and frozen P4 library. Evidence: `impl/p4/results/w5-ssh-baseline.json`.
The added-delay run and final-runtime rerun are pending.

## Integration review in progress

Controller publication uses the existing P2/P3 receipt and frozen-target
checks. Review identified and requested fixes for unsaved buffers omitted
from rename inventory, capture process identity after edits/restarts, and
reporting a successful publication after its registry update.

The rename implementation commits server-owned replay buffers, not a claim
that an arbitrary editor will atomically apply a WorkspaceEdit. Semantic
anchor identity and a real Lean multi-workspace fixture remain review gates.

## Proposed documentation sentences

For plan.md: “W5 connects stamped private editor capture to controller-owned,
receipt-validated publication and adds policy invalidation and transactional
buffer refactoring; see docs/w5-log.md for verified scope and limits.”

For README.md: “The LSP/controller integration and reproducible SSH latency
gate live in impl/p4 and impl/p5; docs/w5-log.md records their evidence.”
