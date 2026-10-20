# FDB gray-failure trace excerpt (mp2-gray, 2026-10-20 UTC)

This excerpt comes from the rejected fast setting (`failure_detection_delay=1.0`,
`connection_monitor_timeout=0.5`, `connection_monitor_loop_time=0.25`) during the first
15-second partition of fdbserver-3. The complete local trace files remain in the private
instance under `/data/home/kirancodes/paralean-p2/inst/mp2-gray/fdb/`.

| UTC | Event | Trace file |
|---|---|---|
| 03:03:55.538 | `MasterRecoveryState=recruiting_transaction_servers` | `p1/log/trace.127.0.0.1.24101.1792465401.gWDYDe.0.1.xml` |
| 03:04:13.442 | First `RkSSListFetchTimeout` | `p4/log/trace.127.0.0.1.24104.1792465407.ZgsVtV.0.1.xml` |
| 03:04:16.329 | `RecruitStorageNotAvailable`, `no_more_servers` | `p1/log/trace.127.0.0.1.24101.1792465401.gWDYDe.0.1.xml` |
| 03:04:36.478 | Last `RkSSListFetchTimeout` | `p4/log/trace.127.0.0.1.24104.1792465407.ZgsVtV.0.1.xml` |
| 03:04:37.394 | `MasterRecoveryState=initializing_transaction_servers` | `p1/log/trace.127.0.0.1.24101.1792465401.gWDYDe.0.1.xml` |

The recruitment stage lasted 41.856 seconds. In this window p1 emitted 33
`RecruitStorageNotAvailable` events and p4 emitted 23 `RkSSListFetchTimeout` events.
The probe's adjacent successful completions were 43.803 seconds apart, while the
partition lasted 15 seconds. The same event pattern appeared in fast trial 2 (38
recruitment warnings, 23 list-fetch timeouts; 43.709-second recovery bracket).
This is evidence that transaction-server recruitment and ratekeeper list fetches
dominated the long recovery in this setup; it does not isolate a single FDB knob as
the cause. The basic `failure_detection_delay=1.0` setting showed no improvement
over the pinned 4.0-second default in three paired trials.
