use ed25519_dalek::{Signature, VerifyingKey};

#[test]
fn strict_vectors_match_dalek() {
    let fixture: serde_json::Value = serde_json::from_str(include_str!("../../../../../verification/fixtures/ed25519-strict-vectors.json")).unwrap();
    let mut count = 0;
    for v in fixture["vectors"].as_array().unwrap() {
        let public: [u8; 32] = hex::decode(v["public_key_hex"].as_str().unwrap()).unwrap().try_into().unwrap();
        let signature: [u8; 64] = hex::decode(v["signature_hex"].as_str().unwrap()).unwrap().try_into().unwrap();
        let message = hex::decode(v["message_hex"].as_str().unwrap()).unwrap();
        let expected = v["expect"].as_bool().unwrap();
        let dalek = VerifyingKey::from_bytes(&public).is_ok_and(|key| key.verify_strict(&message, &Signature::from_bytes(&signature)).is_ok());
        assert_eq!(dalek, expected, "dalek: {}", v["case"]);
        assert_eq!(paralean_crypto::verify(&public, &message, &signature), dalek, "protocol: {}", v["case"]);
        count += 1;
    }
    assert_eq!(count, 99);
}

#[test]
fn point_encoding_is_canonical() {
    for offset in 0..19u8 {
        for sign in [0, 128] {
            let mut p = [255; 32];
            p[0] = 237 + offset;
            p[31] = 127 | sign;
            assert!(!paralean_crypto::canonical_point(&p));
        }
    }
    for first in [1, 236] {
        let mut p = if first == 1 { [0; 32] } else { [255; 32] };
        p[0] = first;
        p[31] = if first == 1 { 128 } else { 255 };
        assert!(!paralean_crypto::canonical_point(&p), "negative zero");
        p[31] &= 127;
        assert!(paralean_crypto::canonical_point(&p));
    }
}
