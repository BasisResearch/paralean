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

/// W4's sharded controller endpoints authenticate with W2's strict RPC verifier: each
/// vector's key is the configured writer key of its own workspace (W2-08: a weak key in
/// trust configuration), and the client sends that vector's signature on the shard's own
/// fresh challenge. Only the genuine signature may register, at every shard.
#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn sharded_controller_rpc_strict_signature_vectors() {
    use paralean_control::controller::{ControlPlane, ControlRequest, ControlResponse, ControllerConfig};
    use paralean_validator_api::rpc;
    let kf = KeyFile::demo(1);
    let authority = kf.authority_signer().unwrap();
    let signer = Signer::from_seed(std::array::from_fn(|i| (i * 11) as u8));
    let keys = vectors::cases(signer.public(), [0; 64]);
    let workers: Vec<WorkspaceId> = (0..keys.len()).map(|i| WorkspaceId::derive(&format!("strict-shard-{i}"))).collect();
    let mut ring = kf.ring();
    for (w, case) in workers.iter().zip(&keys) { ring.writers.insert(*w, case.public); }
    let store = Store::open(&StoreConfig::from_env(&common::deployment("strict-shards")).unwrap(), ring, Faults::none()).unwrap();
    let cfg = ControllerConfig {
        store, authority: authority.clone(), validators: vec![],
        base: fixture::base_id(), policy: receipt::Policy::v1().id(),
        checker: receipt::CheckerVersion::fixture().id(), lease: std::time::Duration::from_millis(500),
        max_work_queue: 4, max_validations: 1, validation_deadline: std::time::Duration::from_secs(1),
        validation_memory_mb: 128, validator_attempts: 1,
    };
    for shard in 0..2 {
        let cp = ControlPlane::new_shard(cfg.clone(), shard, 2);
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let addr = listener.local_addr().unwrap();
        let _server = cp.serve(listener);
        for (i, w) in workers.iter().enumerate() {
            let mut s = tokio::net::TcpStream::connect(addr).await.unwrap();
            let c: rpc::Challenge = rpc::read_frame(&mut s).await.unwrap();
            assert!(rpc::verify_challenge(&c, "paralean/controller", &authority.public()));
            let mut r = rpc::signed_request(ControlRequest::Register { worker: w.hex(), capacity_mb: 1 },
                &signer, &authority.public(), &c.nonce).unwrap();
            let case = &vectors::cases(signer.public(), r.signature.clone().try_into().unwrap())[i];
            r.public = case.public;
            r.signature = case.signature.to_vec();
            rpc::write_frame(&mut s, &r).await.unwrap();
            let answer: std::io::Result<rpc::SignedResponse<ControlResponse>> = rpc::read_frame(&mut s).await;
            let registered = answer.as_ref().is_ok_and(|a| rpc::verify_response(a, "paralean/controller", &authority.public(), &c.nonce)
                && matches!(a.payload, ControlResponse::Registered { .. }));
            assert_eq!(registered, case.expected, "shard {shard}: {}: {answer:?}", case.name);
        }
    }
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("validator_envelope_strict_signature_vectors", || { validator_envelope_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("sharded_controller_rpc_strict_signature_vectors", || { sharded_controller_rpc_strict_signature_vectors(); Ok(()) }),
    ]);
}
