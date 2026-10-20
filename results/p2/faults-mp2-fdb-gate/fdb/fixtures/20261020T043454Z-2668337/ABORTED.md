# Aborted fixture attempt

Started 2026-10-20 04:34:54 UTC; stopped 04:49:36 UTC after a known failure in round 9. The harness and its process group were interrupted with SIGINT. This result is **FAIL/aborted**, not a complete 20-round gate.

`guards::paginated_scan_follows_partial_batches` panicked in setup at `guards.rs:315`, where a FoundationDB transaction commit was unwrapped after returning `Transaction may or may not have committed`. The scan assertion was not reached. There were 28 test-result summaries, including one failed summary, and 65 injected faults before interruption. Raw evidence is in `tests.log` and `events.log`.

After interruption all six own FDB processes and Garage were running, the FDB partition was healed, FDB reported database available with fault tolerance 2, and a new write/read probe succeeded. No harness, cargo, or test process remained. A test-only idempotent retry fix is being prepared separately; the full 20-round gate must be rerun from a fresh result directory.
