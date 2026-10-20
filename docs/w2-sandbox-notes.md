# W2 validator checker sandbox (W2-11)

This is the exact launch profile for running an untrusted Lean checker, what each test
proves, the mutation evidence, the overhead, and the precise limit of the boundary.

The sandbox protects the host and the validator's secrets from the untrusted package code a
checker runs (initializers, `run_tac` native code, the Lean frontend). **It does not
authenticate the verdict against code in the same process (W2-13).** Package execution and
trusted kernel replay still share one Lean process, and the controller trusts that process's
stdout. Namespace isolation, resource limits, the output cap and the response nonce constrain
what that process can touch and how much it can consume; none of them establishes that a
`CHECK`/`WARM` frame was produced by trusted code rather than forged by the package's own
code. Closing W2-13 needs a separate trusted verifier (see `docs/w2-p5-notes.md`,
"Validator result provenance"); it is out of scope here and nothing below should be read as
closing it.

Code: `impl/p3/crates/control/src/checker.rs`. Tests: `tests/sandbox.rs`,
`tests/checker_protocol.rs`. Mutations: `impl/p3/scripts/check-mutations.sh`.

## Launch profile

Every production checker (`CheckerConfig::from_env`, `sandbox = true`, `cgroup = true`) is
launched as:

```
systemd-run --user --scope --quiet --unit paralean-checker-<rand>
    -p MemoryMax=<job limit bytes> -p MemorySwapMax=0 -p OOMPolicy=kill -p TasksMax=96
  -- /bin/sh -c <SCOPE_PREAMBLE> paralean-scope <mem> <tasks>
     /usr/bin/bwrap
       --unshare-user --unshare-pid --unshare-net --unshare-ipc --unshare-uts
       --cap-drop ALL --disable-userns --die-with-parent --clearenv
       --proc /proc --dev /dev
       --size 268435456 --tmpfs /tmp
       --seccomp <fd>
       --ro-bind /usr /usr --ro-bind /bin /bin --ro-bind /lib /lib --ro-bind /lib64 /lib64
       --ro-bind /etc/ld.so.cache /etc/ld.so.cache
       --ro-bind <host input store> /input
       --size 268435456 --tmpfs /work
       --ro-bind <lean sysroot> ... --ro-bind <checker bin> ...
       --ro-bind <PARALEAN_LIB/PARALEAN_MATHLIB/LEAN_PATH entries> ...   (each, if present)
       --setenv PATH <sysroot>/bin:/usr/bin:/bin --setenv HOME /tmp --setenv TMPDIR /tmp
       --setenv PARALEAN_SYSROOT ... --setenv PARALEAN_LAKE ...
       --setenv <only PARALEAN_LIB/PARALEAN_MATHLIB/LEAN_PATH/LEAN_PARALEAN/PARALEAN_FORK_HOOKS/LEAN_NUM_THREADS>
       --chdir /work
       -- /bin/sh -c 'cp -R /input/. /work/ && exec /usr/bin/prlimit --nproc=64:64 -- "$@"'
          sandbox-checker <checker bin> <checker args>
```

Before `exec`, the controller sets rlimits on the `systemd-run` child via `pre_exec`
(inherited through the scope and Bubblewrap) and, when a seccomp program is passed,
`close_range(3.., CLOEXEC)` so no inherited descriptor (store client sockets, the FDB
cluster fd, the signing material) crosses into the checker.

### Namespaces and mounts
- New user, PID, network, IPC and UTS namespaces; all capabilities dropped;
  `--disable-userns` so the checker cannot create further user namespaces.
- Empty root. Read-only binds of the system runtime (`/usr`, `/bin`, `/lib`, `/lib64`,
  `/etc/ld.so.cache`), the Lean sysroot, the checker binary, and the declared Lean import
  roots only. No network interface exists (`--unshare-net`, no loopback brought up).
- The verified input store is bound read-only at `/input`. The checker works on a copy in a
  private tmpfs `/work` (`cp -R /input/.`), so initializer materialization and any writes
  land in the sandbox, never in the host store. `/tmp` is a second private tmpfs.
- Both tmpfs mounts are capped at 256 MiB (`--size 268435456`).

### Environment
`--clearenv`, then only: `PATH`, `HOME=/tmp`, `TMPDIR=/tmp`, `PARALEAN_SYSROOT`,
`PARALEAN_LAKE`, and the Lean input variables `PARALEAN_LIB`, `PARALEAN_MATHLIB`,
`LEAN_PATH`, `LEAN_PARALEAN`, `PARALEAN_FORK_HOOKS`, `LEAN_NUM_THREADS`. The validator's S3
credentials, FDB cluster, admin token and signing seed are never passed (asserted by
`sandbox_configuration_enforces_kernel_limits`).

### Seccomp (x86_64 only; other architectures fail closed)
A classic-BPF program (built in `seccomp_filter`) installed via `--seccomp`. A non-x86_64
syscall ABI is `SECCOMP_RET_KILL_PROCESS`. The 64-bit x86_64 ABI then **EPERM**s:
- sockets/network: `socket`, `socketpair`, `connect`, `bind`, `listen`, `accept`,
  `accept4`, `sendto`;
- mounts, old and new API: `mount`, `umount2`, `pivot_root`, `chroot`, `open_tree`,
  `move_mount`, `fsopen`, `fsconfig`, `fsmount`, `fspick`, `mount_setattr`;
- namespaces/trace/cross-process: `setns`, `unshare`, `ptrace`, `process_vm_readv`,
  `process_vm_writev`, `pidfd_open`, `pidfd_getfd`, `pidfd_send_signal`;
- kernel surfaces: `bpf`, `perf_event_open`, `keyctl`, `add_key`, `request_key`,
  `open_by_handle_at`, `name_to_handle_at`, `userfaultfd`, `init_module`, `finit_module`,
  `delete_module`, `kexec_load`, `kexec_file_load`, `reboot`, `swapon`, `swapoff`, `acct`,
  `quotactl`, `iopl`, `ioperm`, `syslog`;
- process-group/session: `setsid`, `setpgid` (the validator kills the checker by process
  group, so the checker must not escape it);
- **io_uring**: `io_uring_setup`, `io_uring_enter`, `io_uring_register` (an async submission
  ring would otherwise reach files and sockets without issuing the syscalls above);
- terminal injection: `ioctl` with request `TIOCSTI` or `TIOCLINUX`.

`clone`/`clone3` are **allowed**: threads require them and Lean/Lake spawn worker threads.
New namespaces via `clone3` are prevented structurally by `--cap-drop ALL` and
`--disable-userns`, not by the filter, because `clone3`'s flags live behind a user pointer a
classic-BPF filter cannot dereference. This is the standard bubblewrap posture and is why the
mount/userns syscalls above are also denied directly.

### Resource limits (two layers each for memory and processes; fail closed)
- **Memory — hard:** the scope's `MemoryMax` = the job's limit, `MemorySwapMax=0`,
  `OOMPolicy=kill` (so `memory.oom.group=1`: the whole scope dies together). An OOM kill is
  mapped to `NoVerdict::Memory`. This stops a fast allocator that overshoots between RSS
  polls.
- **Memory — soft (second layer):** the resident set of the checker's process group is
  polled every 50 ms and compared to the job limit (`group_rss_kb`). This is the only memory
  limit when the cgroup layer is disabled.
- **Processes — hard:** `prlimit --nproc=64:64` inside the sandbox.
- **Processes — second layer:** the scope's `TasksMax=96` (counts every task/thread in the
  scope, bwrap included).
- **Disk:** the `/work` and `/tmp` tmpfs `--size` caps (ENOSPC) and `RLIMIT_FSIZE`
  (128 MiB per file). The host input store is read-only and never grows, so there is no
  host-directory size scan (the earlier `scratch_bytes(store)` check was dead and was
  removed).
- **CPU:** `RLIMIT_CPU` = deadline + 2 s, plus the controller's wall-clock deadline poll.
- **Other rlimits:** `RLIMIT_NOFILE=256`, `RLIMIT_CORE=0`, `RLIMIT_AS=16 GiB` (a backstop
  only — Lean reserves far more address space than it uses, so `RLIMIT_AS` cannot be the job
  memory limit).

### SCOPE_PREAMBLE and fail-closed behaviour
`systemd` silently ignores a resource property whose cgroup controller is not delegated. To
turn that into a setup failure rather than an unlimited run, the scope first runs a shell
preamble that reads its own `memory.max`, `memory.swap.max` and `pids.max` from
`/sys/fs/cgroup` and exits 125 unless they are exactly the requested values; only then does
it `exec` Bubblewrap.

Production configuration (`CheckerConfig::from_env`) always sets `sandbox = true` and, unless
`PARALEAN_CHECKER_CGROUP=off`, `cgroup = true`. Any other value of that variable is a
configuration error. The cgroup layer is **required in production** (fail closed); the
`off` opt-out exists for hosts without delegated cgroup v2 controllers, where only the RSS
poll and `prlimit` apply (the loss is documented above: a fast overshoot between polls).
A missing Bubblewrap, a failed scope, a seccomp build failure, a non-canonical mount, or any
other setup error yields no verdict (`NoVerdict::Crashed`); there is **no unsandboxed
fallback** — the checker never runs outside the sandbox.

Host facts this relies on (aws-dev): bubblewrap 0.11.1; unprivileged user namespaces via
`bwrap` work even though a direct `unshare` probe is restricted
(`kernel.apparmor_restrict_unprivileged_userns=1`); delegated cgroup v2 `cpu`, `memory` and
`pids` controllers in the user manager (`systemd-run --user --scope`).

## What each test demonstrates

`tests/sandbox.rs` (all run the production profile; the real-Lean cases build their own P1
fixtures with `PARALEAN_BIN` and skip with a message only when it is absent):

| test | demonstrates |
| --- | --- |
| `sandbox_configuration_enforces_kernel_limits` | the rlimits (`FSIZE=128 MiB`, `NOFILE=256`, `CORE=0`, `NPROC=64`, `CPU`, `AS=16 GiB`) are applied and no credential env leaks in |
| `checker_cannot_read_secrets_write_outside_or_use_network` | a key file outside the mounts is unreadable, a write outside `/work` fails, `socket()` fails, `setsid()` fails, and a legitimate write to `/work` stays out of the host store |
| `checker_io_uring_is_blocked` | `io_uring_setup` is EPERM |
| `checker_cpu_budget_kills_busy_loop` | a busy loop past the deadline → `NoVerdict::Timeout` |
| `checker_memory_cgroup_hard_limit_kills_fast_burst` | a 96 MiB memset burst that exits with a forged `CHECK` between RSS polls is OOM-killed by the cgroup → `NoVerdict::Memory` |
| `checker_memory_rss_poll_catches_sustained_hog_without_cgroup` | with the cgroup disabled, a sustained 256 MiB resident set is caught by the 50 ms poll → `NoVerdict::Memory` |
| `checker_disk_budget_is_tmpfs_enospc_and_rlimit_fsize` | filling `/work` with sub-`FSIZE` files raises ENOSPC at the tmpfs cap, and a single growing file hits `RLIMIT_FSIZE` (EFBIG) first |
| `checker_process_count_is_hard_limited` | 75 forks (between `NPROC`=64 and `TasksMax`=96) are blocked by `prlimit` |
| `sandbox_fails_closed_when_bwrap_is_missing` | a missing Bubblewrap → `NoVerdict::Crashed` and the checker never ran |
| `production_config_enables_the_sandbox` | `from_env` sets `sandbox` and `cgroup` |
| `real_plain_theorem_passes_inside_and_outside_the_sandbox` | a captured F01 theorem checks `ok` both direct and sandboxed |
| `real_initializer_materializes_in_private_scratch` | a captured F13 initializer package checks `ok` under the sandbox, materializing in the tmpfs, not the host store |
| `native_lean_tactic_cannot_reach_host` | the `run_tac` package of `fixtures/Attack.lean.in` (reads a key, writes outside, opens the host TCP listener) is fully contained and its legitimate `trivial` proof still checks |

`tests/checker_protocol.rs` (framing, no Lean/store needed):
`warm_ignores_spoofed_and_replayed_frames`, `cold_uses_last_check_line`,
`cold_nonzero_exit_never_accepts_printed_check`,
`cold_output_flood_cannot_fill_validator_memory` (a checker printing > 1 MiB →
`NoVerdict::Output`), `cold_malformed_axiom_cannot_be_silently_dropped`.

Resource-exhaustion by real native code: the `native_lean_tactic_cannot_reach_host` package
demonstrates the host-reach attacks (read/write/network) while its honest proof still checks;
the CPU/memory/process/disk limits are proven under the identical production profile by the
stand-in checker tests above, which can drive each limit deterministically without also
needing the honest part to pass.

## Mutation evidence

`impl/p3/scripts/check-mutations.sh` deletes one guard per cargo feature and requires the
named test to then fail. Sandbox/checker guards and their detecting tests:

| feature (guard removed) | test that must fail |
| --- | --- |
| `mutate-no-checker-sandbox` | `checker_cannot_read_secrets_write_outside_or_use_network` |
| `mutate-no-checker-seccomp` | `checker_cannot_read_secrets_write_outside_or_use_network` |
| `mutate-checker-seccomp-allows-io-uring` | `checker_io_uring_is_blocked` |
| `mutate-no-checker-disk-limit` | `checker_disk_budget_is_tmpfs_enospc_and_rlimit_fsize` |
| `mutate-no-checker-fsize-limit` | `checker_disk_budget_is_tmpfs_enospc_and_rlimit_fsize` |
| `mutate-no-checker-process-limit` | `checker_process_count_is_hard_limited` |
| `mutate-no-checker-memory-limit` | `checker_memory_rss_poll_catches_sustained_hog_without_cgroup` |
| `mutate-no-checker-cgroup` | `checker_memory_cgroup_hard_limit_kills_fast_burst` |
| `mutate-no-checker-cpu-limit` | `checker_cpu_budget_kills_busy_loop` |
| `mutate-checker-config-unsandboxed` | `production_config_enables_the_sandbox` |
| `mutate-checker-fallback-unsandboxed` | `sandbox_fails_closed_when_bwrap_is_missing` |
| `mutate-unbounded-checker-output` | `cold_output_flood_cannot_fill_validator_memory` |

Full script output (all guards, including the pre-existing receipt/target/control ones) is
archived under `results/w2/` (see "Results" below). Every guard was detected; no mutation
survived.

## Warm pool under the sandbox (single-use)

A sandboxed checker runs one package's code, so it must never judge another package: the warm
pool keeps a sandboxed process only for the single job it was spawned for and kills it
afterwards (`WarmPool::run` returns a process to the idle set only when `!sandbox_active`).
The validator already routes initializer jobs to a disposable pool for the same reason; under
the sandbox that is now the behaviour for **all** jobs. The cost is that every sandboxed job
pays a cold process spawn plus the cgroup scope setup (measured below); warm reuse applies
only to the unsandboxed configuration used in protocol tests.

## Overhead

Method: `cargo test -p paralean-control --test overhead -- --ignored --nocapture`
(`tests/overhead.rs`). It captures its own F01 (plain) and F13 (initializer) P1 stores with
`PARALEAN_BIN`, then times `checker::run` over 12 runs per cell, reporting p50/p90/min in
milliseconds. `direct` = no sandbox; `sandbox+cg` = full production profile; `sandbox-nocg` =
sandbox without the cgroup scope (isolates the scope's cost). The scope-startup rows time a
trivial no-op checker. Warm rows use `PARALEAN_P3_WARM_BIN`: `warm-direct` reuses one
unsandboxed process (first spawn shown separately from reuse), `warm-sandbox` spawns a fresh
single-use process per job.

Numbers below are from one run on aws-dev (32 cores, otherwise idle), `LEAN_NUM_THREADS=2`,
`PARALEAN_MATHLIB` unset so the initializer package builds standalone. Milliseconds.

Cold check latency (12 runs; initializer 10 runs, each a fresh store copy so no materialize
cache carries over — as in production, where every job gets a fresh scratch store):

| fixture | mode | p50 | p90 | min |
| --- | --- | ---: | ---: | ---: |
| plain | direct | 292 | 332 | 251 |
| plain | sandbox + cgroup | 503 | 575 | 425 |
| plain | sandbox, no cgroup | 396 | 453 | 374 |
| initializer | direct | 11423 | 12771 | 10517 |
| initializer | sandbox + cgroup | 8916 | 9989 | 8661 |
| initializer | sandbox, no cgroup | 8517 | 9930 | 8087 |

- Plain theorem: sandboxing costs ~210 ms p50 over a direct spawn (292 → 503), of which the
  cgroup scope is ~110 ms (sandbox-nocg 396 → sandbox+cg 503). On a ~250 ms check this is
  noticeable but small in absolute terms.
- Initializer package: latency is dominated by the in-sandbox stock `lake build` of the
  materialized closure (~8–11 s here). The sandboxed numbers are **not** worse than a fair
  direct run — slightly better, because the build runs in the `/work` tmpfs rather than on
  disk. The earlier impression that initializers were ~10× slower sandboxed was an artifact
  of a direct benchmark that reused an on-disk materialize cache the single-use sandbox (and
  production's per-job scratch) cannot keep; with that cache cleared, both pay the full
  build.

Cgroup scope startup (trivial no-op checker, 12 runs): sandbox+cgroup p50 80 ms / p90 103 ms
vs sandbox-nocgroup p50 62 ms / p90 66 ms — the transient scope and its limit-verification
preamble add ~18 ms p50.

Warm path (plain fixture): a warm-direct (unsandboxed) pool pays ~337 ms for the first
process spawn, then reuses it at p50 13 ms / p90 14 ms per job (1 process for all 12 jobs). A
sandboxed pool is single-use by design, so every job spawns a fresh process + scope + cgroup:
p50 308 ms / p90 349 ms (12 spawns for 12 jobs). The single-use requirement therefore costs
roughly 295 ms per job versus warm reuse — the price of never letting a process that ran one
package's code judge another's.

## Results

- `results/w2/sandbox-tests.log` — `tests/sandbox.rs` + `tests/checker_protocol.rs`, all
  passing, none ignored.
- `results/w2/sandbox-mutations.log` — full `check-mutations.sh` output.
- `results/w2/sandbox-overhead.log` — the overhead table above.
