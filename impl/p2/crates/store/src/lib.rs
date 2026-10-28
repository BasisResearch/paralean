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
//! | `receipt` | P3 receipt binding (OPEN-7): job envelopes, policy and checker IDs, revocation, the staging rule |
//! | `audit` | whole-store invariant checks |
//! | `faults` | client-side fault injection |
//! | `antientropy` | exchange of published groups and tombstones between deployments |
//! | `batch` | atomic multi-group publication (T12) and its records |

pub mod ae;
pub mod authority;
pub mod batch;
pub mod antientropy;
pub mod audit;
mod checkpoint_guard;
pub mod error;
pub mod faults;
pub mod fixture;
pub mod group_chunks;
pub mod id;
pub mod meta;
pub mod objects;
pub mod pce;
pub mod receipt;
pub mod recovery;
pub mod s3;
pub mod sign;
pub mod store;
pub mod writer;

pub use error::{GuardFailure, Result, StoreError};
pub use authority::{controller_agent_id, AgentKeyGrant, AgentKeyRevocation, ControllerDeleteGrant};
pub use ae::{AeBundlePage, AeEvent, AeIdentity, AeKind, AeObjectPage, AePage, AePart, AePending, AePendingPage, AeProgress, FederationConfig, FederationMember, PendingState};
pub use faults::{CommitFault, CrashMode, Faults, GetFault, PutFault, RandomFaults, Txn};
pub use id::{AgentId, Domain, Id, Kind, ReplicaId, WorkspaceId};
pub use meta::{PreparedTarget, PublishOutcome};
pub use objects::*;
pub use receipt::{BindingFault, CheckerVersion, JobEnvelope, Pins, Policy, SignedJob, TargetBinding};
pub use s3::{Acked, S3Config};
pub use sign::{KeyFile, KeyRing, Signer};
pub use store::{Store, StoreConfig};
pub use writer::{CertKey, Checkpoint, Controller, Package, Writer};
pub use batch::{BatchEntry, BatchIntent, BatchItem, BatchMember, BatchOutcome, BatchPackage, BatchRecord, SignedBatch, MAX_BATCH_BYTES, MAX_BATCH_MEMBERS};
