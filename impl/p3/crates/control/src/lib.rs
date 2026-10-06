//! Paralean P3 control plane (docs/plan.md P3; impl/p3/README.md).
//!
//! | Module | Contents |
//! |---|---|
//! | `p1` | reading impl/p1 stores; P1 groups as P2 payloads (group bytes, metadata as capsule) |
//! | `checker` | `paralean check-group` as a subprocess: deadline, resident-memory watchdog, cancellation |
//! | `validator` | the validator service: envelope in, Ed25519 receipt out |
//! | `controller` | target assignment (T4), work and validation dispatch, deduplication, cancellation, memory admission, backpressure, leases |
//! | `worker` | a worker: registers, heartbeats, takes target work, gets receipts, publishes (T1) |
//! | `server` | the TCP frame server shared by both services |
//!
//! The receipt format and the staging rule are `paralean_store::receipt`; the validator's
//! wire API is the `paralean-validator-api` crate.

pub mod checker;
pub mod controller;
pub mod p1;
pub mod server;
pub mod validator;
pub mod worker;
