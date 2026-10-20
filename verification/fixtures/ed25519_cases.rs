// Shared *test* adapter: apply encoding defects to a genuinely signed path message.
// Weak A vectors retain their paired weak R/S so relaxing verification is observable.
pub struct Case {
    pub name: String,
    pub public: [u8; 32],
    pub signature: [u8; 64],
    pub expected: bool,
}

/// The group order, little-endian.
const L: [u8; 32] = [0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10];

pub fn cases(public: [u8; 32], signature: [u8; 64]) -> Vec<Case> {
    let fixture: serde_json::Value = serde_json::from_str(include_str!("ed25519-strict-vectors.json")).unwrap();
    let mut result = vec![Case { name: "valid_path_signature".into(), public, signature, expected: true }];
    for v in fixture["vectors"].as_array().unwrap() {
        let kind = v["kind"].as_str().unwrap();
        // Mixed-order vectors are bound to their own message (an agreement check
        // between verifiers), so they do not transplant onto a path message.
        if v["expect"].as_bool().unwrap() || kind.starts_with("mixed_order") { continue; }
        let encoded_public: [u8; 32] = hex::decode(v["public_key_hex"].as_str().unwrap()).unwrap().try_into().unwrap();
        let encoded_sig: [u8; 64] = hex::decode(v["signature_hex"].as_str().unwrap()).unwrap().try_into().unwrap();
        let mut bad = signature;
        let mut key = public;
        if kind.ends_with("_A") {
            key = encoded_public;
            if kind == "small_order_A" { bad = encoded_sig; }
        } else if kind.ends_with("_R") {
            bad[..32].copy_from_slice(&encoded_sig[..32]);
        } else if v["case"] == "S_malleated_plus_L" {
            // Malleate this path's own signature: S + L verifies unless S < L is checked.
            let mut carry = 0u16;
            for (i, l) in L.iter().enumerate() {
                let sum = bad[32 + i] as u16 + *l as u16 + carry;
                bad[32 + i] = sum as u8;
                carry = sum >> 8;
            }
            assert_eq!(carry, 0);
        } else if kind == "noncanonical_S" {
            bad[32..].copy_from_slice(&encoded_sig[32..]);
        } else {
            panic!("unrecognized vector kind: {kind}");
        }
        result.push(Case { name: v["case"].as_str().unwrap().into(), public: key, signature: bad, expected: false });
    }
    result
}
