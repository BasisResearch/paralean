//! Synthetic packages and checkpoints for tests, the CLI demo and the stress workers.
//! Group payloads are opaque bytes shaped like P1's (`paralean-group-v2` magic first).

use crate::id::{AgentId, Id, Kind, WorkspaceId};
use crate::meta::PreparedTarget;
use crate::objects::*;
use crate::pce::Enc;
use crate::sign::Signer;
use crate::writer::{Checkpoint, Package};

/// A fake P1-style group payload: `string "paralean-group-v2" ‖ string baseId ‖ body`.
pub fn group_bytes(tag: &str) -> Vec<u8> {
    let mut e = Enc::new();
    e.string("paralean-group-v2").string("base:test").bytes(tag.as_bytes());
    e.out
}

pub fn base_id() -> Id {
    Id(crate::id::sha256(b"paralean-p2-test-base"))
}

/// Build a package for one group declaring `name` (a revision per name), with an optional
/// prepared target. `parents` are the revisions it revises.
pub fn package(
    tag: &str,
    workspace: WorkspaceId,
    validator: &Signer,
    name: &Name,
    parents: Vec<Id>,
    target: Option<PreparedTarget>,
    lamport: u64,
) -> Package {
    let group = Opaque::new(Kind::Group, group_bytes(tag));
    let capsule = Opaque::new(Kind::Capsule, format!("capsule of {tag}").into_bytes());
    let chunks = vec![Opaque::new(Kind::Chunk, format!("chunk of {tag}").into_bytes())];
    let g = group.id();
    let receipt = Receipt::sign(
        ReceiptBody {
            group: g,
            base: base_id(),
            validator_key: validator.public(),
            validator_bin: b"validator-test".to_vec(),
            policy: Id(crate::id::sha256(b"policy")),
            request: None,
            target: None,
            verdict: Verdict::Accepted,
            axioms: vec![Name::parse("propext")],
        },
        validator,
    );
    let mut parents = parents;
    parents.sort();
    parents.dedup();
    let rev = Revision { group: g, name: name.clone(), parents, capsule: capsule.id(), workspace };
    let author = AgentId::derive(&format!("agent/{}", workspace.hex()));
    let marker = Marker {
        group: g,
        revisions: vec![rev.id()],
        receipt: receipt.id(),
        file_path: "Test/File.lean".into(),
        anchor: Anchor::FileStart,
        lamport,
        author,
        root_path: vec![],
        lineage_keys: vec![(name.clone(), lamport, author)],
    };
    Package { group, chunks, capsule, receipt, revisions: vec![rev], marker, targets: target.into_iter().collect() }
}

/// A checkpoint over the given revisions.
pub fn checkpoint(workspace: WorkspaceId, contents: Vec<Id>, predecessor: Option<Id>, token: TokenRef, tag: &str) -> Checkpoint {
    let mut contents = contents;
    contents.sort();
    contents.dedup();
    let source_root = Manifest::SourceRoot { files: vec![(format!("Test/{tag}.lean"), vec![])] };
    let build_receipt = Manifest::BuildReceipt {
        exporter_bin: b"exporter".to_vec(),
        lean_commit: "193c3589a4fc16c4059261ab38cfa365eb24f323".into(),
        mathlib_commit: "0575336843263378752eeb5f4c75a612327768a2".into(),
        layout: Id(crate::id::sha256(tag.as_bytes())),
        build_log_hash: crate::id::sha256(format!("log {tag}").as_bytes()).to_vec(),
        target_checks: vec![],
        verdict: BuildVerdict::Ok,
    };
    let snapshot = Snapshot {
        workspace,
        base: base_id(),
        contents,
        predecessors: vec![],
        targets: vec![],
        source_root: Manifest::id(&source_root),
        build_receipt: Manifest::id(&build_receipt),
    };
    Checkpoint { snapshot, source_root, build_receipt, predecessor, token }
}
