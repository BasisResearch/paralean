#[path = "../../../../../verification/fixtures/ed25519_cases.rs"]
mod vectors;

use paralean_store::Signer;
use paralean_validator_api::{rpc, ValidatorRequest};

#[test]
fn validator_rpc_strict_signature_vectors() {
    let signer = Signer::from_seed(std::array::from_fn(|i| i as u8));
    let nonce = [42; 32];
    let request = rpc::signed_request(ValidatorRequest::Status, &signer, &nonce).unwrap();
    for case in vectors::cases(signer.public(), request.signature.clone().try_into().unwrap()) {
        let mut r = request.clone();
        r.public = case.public;
        r.signature = case.signature.to_vec();
        assert_eq!(rpc::verify_request(&r, &nonce), case.expected, "request: {}", case.name);
    }
    let challenge = rpc::challenge(&signer);
    for case in vectors::cases(signer.public(), challenge.signature.clone().try_into().unwrap()) {
        let mut c = challenge.clone();
        c.signature = case.signature.to_vec();
        assert_eq!(rpc::verify_challenge(&c, &case.public), case.expected, "challenge: {}", case.name);
    }
}
