//! Validator receipts (p0-interfaces §6) behind a small interface.
//!
//! P3's control branch builds the validator service and its receipt module. Until that
//! lands, this module issues and checks receipts with P2's `Signed<ReceiptBody>` (Ed25519
//! over the body ID). Working copies and publishers use only `ReceiptIssuer` and
//! `ReceiptCheck`, so switching to the control branch's module replaces this file.
//!
//! Binding (§6, OPEN-7): `group` is the exact group ID; `request` is the ID of the check
//! request, `H("v0/job", PCE(groupID, capsuleID))`, so a receipt also pins the capsule
//! (frontend input and metadata) the validator replayed; `base` and `policy` are the IDs
//! below; `axioms` is the closure the validator's kernel replay found.

use paralean_store::pce::Enc;
use paralean_store::{Id, Name, Receipt, ReceiptBody, Signer, Verdict};
use sha2::{Digest, Sha256};

/// `H(domain, pce)` for domains P2 does not enumerate (`v0/job`, `v0/policy`).
pub fn domain_hash(domain: &str, pce: &[u8]) -> Id {
    let mut h = Sha256::new();
    h.update(b"paralean\x00");
    h.update(domain.as_bytes());
    h.update([0u8]);
    h.update(pce);
    Id(h.finalize().into())
}

/// The check request a receipt answers: one group with the capsule it was replayed from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckRequest {
    pub group: Id,
    pub capsule: Id,
}

impl CheckRequest {
    pub fn id(&self) -> Id {
        let mut e = Enc::new();
        self.group.encode_into(&mut e);
        self.capsule.encode_into(&mut e);
        domain_hash("v0/job", &e.out)
    }
}

trait EncodeInto {
    fn encode_into(&self, e: &mut Enc);
}
impl EncodeInto for Id {
    fn encode_into(&self, e: &mut Enc) {
        e.bytes(&self.0);
    }
}

/// The validator's verdict on one request.
#[derive(Clone, Debug)]
pub struct CheckResult {
    pub accepted: bool,
    pub reason: String,
    pub axioms: Vec<Name>,
}

/// The pinned base and policy, and the trusted validator keys.
#[derive(Clone, Debug)]
pub struct Trust {
    pub base: Id,
    pub policy: Id,
    pub validators: Vec<[u8; 32]>,
    pub allowed_axioms: Vec<String>,
}

pub const ALLOWED_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];

impl Trust {
    /// `base`: `H("v0/base", PCE(format, leanCommit, mathlibCommit))` (a reduced §2 manifest).
    /// `policy`: `H("v0/policy", PCE(format, allowed axioms, forbidden options))`.
    pub fn new(lean_commit: &str, mathlib_commit: &str, validators: Vec<[u8; 32]>) -> Trust {
        let mut e = Enc::new();
        e.uvarint(0).string(lean_commit).string(mathlib_commit);
        let base = domain_hash("v0/base", &e.out);
        let mut p = Enc::new();
        p.uvarint(0);
        p.set(&ALLOWED_AXIOMS, |e, a| {
            e.string(a);
        });
        p.set(&["debug.skipKernelTC", "Elab.async"], |e, o| {
            e.string(o);
        });
        let policy = domain_hash("v0/policy", &p.out);
        Trust { base, policy, validators, allowed_axioms: ALLOWED_AXIOMS.iter().map(|s| s.to_string()).collect() }
    }
}

pub trait ReceiptIssuer {
    fn issue(&self, req: &CheckRequest, res: &CheckResult) -> Receipt;
}

pub trait ReceiptCheck {
    /// `Ok` iff the receipt admits exactly this request under the trusted keys, base and
    /// policy, with an accepted verdict and axioms inside the policy.
    fn admits(&self, r: &Receipt, req: &CheckRequest) -> Result<(), String>;
}

/// The stand-in validator identity: an Ed25519 key and the hash of the validator binary.
pub struct Validator {
    pub signer: Signer,
    pub bin_hash: Vec<u8>,
    pub trust: Trust,
}

impl ReceiptIssuer for Validator {
    fn issue(&self, req: &CheckRequest, res: &CheckResult) -> Receipt {
        let mut axioms = res.axioms.clone();
        axioms.sort_by_key(|n| paralean_store::pce::Pce::to_pce(n));
        axioms.dedup();
        Receipt::sign(
            ReceiptBody {
                group: req.group,
                base: self.trust.base,
                validator_key: self.signer.public(),
                validator_bin: self.bin_hash.clone(),
                policy: self.trust.policy,
                request: Some(req.id().0.to_vec()),
                target: None,
                verdict: if res.accepted { Verdict::Accepted } else { Verdict::Rejected(res.reason.clone()) },
                axioms,
            },
            &self.signer,
        )
    }
}

impl ReceiptCheck for Trust {
    fn admits(&self, r: &Receipt, req: &CheckRequest) -> Result<(), String> {
        let b = &r.body;
        if b.group != req.group {
            return Err("receipt names another group".into());
        }
        if b.request.as_deref() != Some(&req.id().0[..]) {
            return Err("receipt answers another request (group, capsule)".into());
        }
        if b.verdict != Verdict::Accepted {
            return Err(format!("verdict {:?}", b.verdict));
        }
        if !self.validators.contains(&b.validator_key) {
            return Err("validator key is not trusted".into());
        }
        if b.base != self.base || b.policy != self.policy {
            return Err("receipt is for another base or policy".into());
        }
        if !r.verify(&b.validator_key) {
            return Err("signature does not verify".into());
        }
        for a in &b.axioms {
            if !self.allowed_axioms.contains(&a.to_string()) {
                return Err(format!("axiom {a} outside the policy"));
            }
        }
        Ok(())
    }
}
