//! Paralean P2 storage (docs/store.md): FoundationDB 7.3 metadata (API 730) and an
//! S3-compatible payload store.
//!
//! | Module | Contents |
//! |---|---|
//! | `pce`, `id`, `objects`, `sign` | PCE encoding (§1.1), hash domains and IDs (§1.2), typed objects, Ed25519 |
//! | `s3` | content-addressed payload writes with `x-amz-checksum-sha256`, verified reads |
//! | `meta` | key layout, the idempotent transaction loop, bodies of T1–T7 |
//! | `store`, `writer` | the store handle; publication, certificates, checkpoints, controller, repair |
//! | `recovery` | discovery by certificates, head reconstruction, catalogue recovery |
//! | `audit` | whole-store invariant checks |
//! | `faults` | client-side fault injection |

pub mod audit;
pub mod error;
pub mod faults;
pub mod fixture;
pub mod id;
pub mod meta;
pub mod objects;
pub mod pce;
pub mod recovery;
pub mod s3;
pub mod sign;
pub mod store;
pub mod writer;

pub use error::{GuardFailure, Result, StoreError};
pub use faults::{CommitFault, CrashMode, Faults, GetFault, PutFault, RandomFaults, Txn};
pub use id::{AgentId, Domain, Id, Kind, ReplicaId, WorkspaceId};
pub use meta::{PreparedTarget, PublishOutcome};
pub use objects::*;
pub use s3::{Acked, S3Config};
pub use sign::{KeyFile, KeyRing, Signer};
pub use store::{Store, StoreConfig};
pub use writer::{CertKey, Checkpoint, Controller, Package, Writer};
