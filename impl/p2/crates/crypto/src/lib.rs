//! The common Ed25519 acceptance policy for all Rust protocol consumers.
use ed25519_dalek::{Signature, VerifyingKey};

/// Require canonical compressed Edwards coordinates, including the sign of zero.
/// Dalek's strict equation and small-order checks are applied separately below.
pub fn canonical_point(bytes: &[u8; 32]) -> bool {
    if cfg!(feature = "mutate-noncanonical-point") { return true; }
    let mut y = *bytes;
    let sign = y[31] >> 7;
    y[31] &= 127;
    let mut p = [255; 32];
    p[0] = 237;
    p[31] = 127;
    if y.iter().rev().cmp(p.iter().rev()) != std::cmp::Ordering::Less {
        return false;
    }
    let mut one = [0; 32];
    one[0] = 1;
    p[0] -= 1;
    !(sign != 0 && (y == one || y == p))
}

pub fn verify(public: &[u8; 32], message: &[u8], signature: &[u8]) -> bool {
    let Ok(bytes) = <[u8; 64]>::try_from(signature) else { return false };
    let r: [u8; 32] = bytes[..32].try_into().unwrap();
    if !canonical_point(public) || !canonical_point(&r) { return false; }
    let Ok(key) = VerifyingKey::from_bytes(public) else { return false };
    key.verify_strict(message, &Signature::from_bytes(&bytes)).is_ok()
}
