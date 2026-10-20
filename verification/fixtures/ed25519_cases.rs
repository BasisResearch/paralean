// Shared *test* adapter: apply encoding defects to a genuinely signed path message.
// Weak A vectors retain their paired weak R/S so relaxing verification is observable.
pub struct Case {
    pub name: String,
    pub public: [u8; 32],
    pub signature: [u8; 64],
    pub expected: bool,
}

pub fn cases(public: [u8; 32], signature: [u8; 64]) -> Vec<Case> {
    let fixture: serde_json::Value = serde_json::from_str(include_str!("ed25519-strict-vectors.json")).unwrap();
    let mut result = vec![Case { name: "valid_path_signature".into(), public, signature, expected: true }];
    for v in fixture["vectors"].as_array().unwrap() {
        if v["expect"].as_bool().unwrap() { continue; }
        let kind = v["kind"].as_str().unwrap();
        let encoded_public: [u8; 32] = hex::decode(v["public_key_hex"].as_str().unwrap()).unwrap().try_into().unwrap();
        let encoded_sig: [u8; 64] = hex::decode(v["signature_hex"].as_str().unwrap()).unwrap().try_into().unwrap();
        let mut bad = signature;
        let mut key = public;
        if kind.ends_with("_A") {
            key = encoded_public;
            if kind == "small_order_A" { bad = encoded_sig; }
        } else if kind.ends_with("_R") {
            bad[..32].copy_from_slice(&encoded_sig[..32]);
        } else if kind == "noncanonical_S" {
            bad[32..].copy_from_slice(&encoded_sig[32..]);
        } else {
            panic!("unrecognized vector kind: {kind}");
        }
        result.push(Case { name: v["case"].as_str().unwrap().into(), public: key, signature: bad, expected: false });
    }
    result
}
