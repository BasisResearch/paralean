// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;
#[path = "../../../../../verification/fixtures/ed25519_cases.rs"]
mod vectors;

use paralean_control::checker::CheckerConfig;
use paralean_control::validator::{Validator, ValidatorConfig};
use paralean_store::*;
use paralean_validator_api::ValidatorResponse;

#[tokio::main(flavor = "current_thread")]
async fn validator_envelope_strict_signature_vectors() {
    let cfg = StoreConfig::from_env(&common::deployment("strict-validator")).unwrap();
    let kf = KeyFile::demo(1);
    let authority = kf.authority_signer().unwrap();
    let validator = kf.validator_signer("v0").unwrap();
    let (writer, _) = kf.workspace("w0").unwrap();
    let p = fixture::package_by(&authority, "strict", writer, &validator,
        &Name::parse("Strict.fixture"), vec![], None, 1);
    let checker = CheckerConfig { default_memory_mb: 256,
        ..CheckerConfig::sandboxed(std::env::current_exe().unwrap(), "strict-test") };
    let dir = common::scratch("strict-validator");
    for case in vectors::cases(authority.public(), p.job.sig) {
        let mut ring = kf.ring();
        ring.authority = case.public;
        let store = Store::open(&cfg, ring, Faults::none()).unwrap();
        let v = Validator::new(ValidatorConfig { store, signer: validator.clone(), checker: checker.clone(),
            base: Id([0; 32]), policies: vec![receipt::Policy::v1()], max_running: 1,
            max_queued: 1, workdir: dir.clone() }).unwrap();
        let mut job = p.job.clone();
        job.sig = case.signature;
        let response = v.validate(job).await;
        let ValidatorResponse::Refused { reason } = response else { panic!("{}: {response:?}", case.name) };
        if case.expected {
            assert!(reason.starts_with("envelope names checker"), "{}: {reason}", case.name);
        } else {
            assert_eq!(reason, "envelope is not signed by the controller", "{}", case.name);
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("validator_envelope_strict_signature_vectors", || { validator_envelope_strict_signature_vectors(); Ok(()) }),
    ]);
}
