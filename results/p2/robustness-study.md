# P2 robustness study, 2026-10-20 UTC

All instances used the pinned FoundationDB 7.3.79 binaries under the P2 prefix and
their own `PARALEAN_INSTANCE=mp2-*` data and ports. The data filesystem had 251–253 GiB
free during the runs. No other instance was changed.

## FDB gray failures (`mp2-gray`)

Five FDB processes in five zones ran `triple` behind `netsplit`. The same 15-second
SIGSTOP of fdbserver-2 and 15-second partition of fdbserver-3 were repeated three
times per setting, with a successful probe write and fault tolerance 2 between
faults. One serial `fdbcli` write/read probe ran about once per second, each with an
8-second timeout. Probe start and completion times are recorded in nanoseconds.
For a failed window, the time between the preceding and following successful probe
completions is a conservative recovery bracket, not an exact outage duration.

| Setting | Pause failed probes, per trial | Pause recovery brackets for trials with failures | Partition failed probes, per trial | Partition recovery brackets, seconds |
|---|---|---|---|---|
| Default `failure_detection_delay=4.0` | 0, 1, 1 | 15.914, 15.924 s | 2, 2, 2 | 17.470, 17.131, 17.714 (median 17.470) |
| `failure_detection_delay=1.0` | 0, 1, 1 | 15.950, 15.993 s | 2, 2, 2 | 17.902, 16.999, 17.631 (median 17.631) |
| Above plus `connection_monitor_timeout=0.5`, `connection_monitor_loop_time=0.25` | 0, 0, 0 | no failed probe sampled; successful calls stalled up to 6.224 s | 4, 4, 4 | 43.803, 43.709, 43.643 (median 43.709) |

The first change gave no measurable improvement under this schedule. The second
change was a clear regression and is rejected. A zero failed-probe count does not
prove continuous availability: successful probe calls during pauses took as long as
7.936 s (default), 6.078 s (delay 1.0), and 6.224 s (aggressive candidate).
The [pinned Flow knobs](https://github.com/apple/foundationdb/blob/7.3.79/flow/Knobs.cpp)
define the defaults as 4.0, 2.0, and 1.0 seconds respectively. The
[trimmed trace excerpt](robustness-mp2-gray/trace-excerpt.md) shows a 41.856-second
transaction-server recruitment and repeated ratekeeper list-fetch timeouts during
the aggressive candidate's first partition; that explains why reducing a basic
failure delay alone did not shorten the measured recovery. The three-run sample is
small and role assignment varied, so it supports rejecting these two candidate
settings for this setup, not a general FDB tuning recommendation.

The raw probes, fault event times, per-trial FDB status, and generated comparisons
are under `robustness-mp2-gray/gray/{paired,fast}/gray/`. The instance was stopped
and ports 24100–24114 were clear after the runs.

## Permanent FDB coordinator loss (`mp2-coord`)

Six FDB processes on distinct loopback IPs (`127.0.0.2`–`127.0.0.7`), six zones,
five initial coordinators, and `triple` redundancy reached fault tolerance 2.
An acknowledged value was read back before loss. Coordinator 0 at
`127.0.0.2:24200` was killed permanently. `coordinators auto` reported
“Coordination state changed” and the FDB cluster file moved from endpoints `.2`–`.6`
to `.3`–`.7`, excluding the dead endpoint. The pre-loss value remained readable;
a new value committed and read back. The instance was stopped and ports 24200–24205
were clear afterward. The old and new connection strings, CLI output, and checks
are under `robustness-mp2-coord/coordinator/`.

Distinct loopback IPs matter here because [FDB's coordinator selection considers IP
addresses](https://apple.github.io/foundationdb/configuration.html#changing-coordination-servers).
This tests `coordinators auto` after a permanent loss with a live spare process,
while still using an isolated single-host process model.

The merged-tree `impl/p2/scripts/provision-fdb-study.sh` creates either FDB-only
instance, and `impl/p2/scripts/robustness-study.sh` runs the selected experiment.
