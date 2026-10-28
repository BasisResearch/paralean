// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]
mod common;
#[path = "../../../../../verification/fixtures/ed25519_cases.rs"]
mod vectors;

use paralean_store::*;

fn store_strict_signature_vectors() {
    let signer = Signer::from_seed(std::array::from_fn(|i| i as u8));
    let id = Id([42; 32]);
    for case in vectors::cases(signer.public(), signer.sign(&id)) {
        assert_eq!(sign::verify(&case.public, &id, &case.signature), case.expected, "{}", case.name);
    }
}

#[tokio::main(flavor = "current_thread")]
async fn antientropy_import_strict_signature_vectors() {
    use antientropy::{import, Item, Outcome};
    use common::*;
    let e = Env::new("w2-strict-import", 1);
    let p = e.plain_package(0, "Strict.fixture", "strict");
    let t = fixture::tombstone_of(&p.marker, 2);
    let body = TombstoneCertBody { replica: e.store.replica, tombstone: t.id(), target: t.target, writer: e.w[0].id };
    let (_, signer) = e.kf.workspace("w0").unwrap();
    let cert = TombstoneCert::sign(body, &signer);
    // Import verifies the certificate before looking for the payload. The valid
    // control reaches Deferred; every malformed signature must stop at Rejected.
    for case in vectors::cases(signer.public(), cert.sig) {
        let mut ring = (*e.store.ring).clone();
        ring.writers.insert(e.w[0].id, case.public);
        let st = Store::open(&e.cfg, ring, Faults::none()).unwrap();
        let receiver = Writer::new(st, e.w[0].id, signer.clone());
        let mut c = cert.clone();
        c.sig = case.signature;
        let item = Item::Tombstone { tombstone: t.preimage(), certs: vec![c.to_bytes()], controller_grant: None };
        let outcome = import(&receiver, &item).await.unwrap();
        if case.expected {
            assert!(matches!(outcome, Outcome::Deferred(_)), "{}: {outcome:?}", case.name);
        } else {
            assert!(matches!(outcome, Outcome::Rejected(_)), "{}: {outcome:?}", case.name);
        }
    }
}

#[tokio::main(flavor = "current_thread")]
async fn t1_publication_strict_receipt_signature_vectors() {
    use common::*;
    let e = Env::new("w2-strict-t1", 1);
    let count = vectors::cases(e.validator.public(), [0; 64]).len();
    let mut packages = Vec::new();
    let mut ring = (*e.store.ring).clone();
    for i in 0..count {
        // A fresh group per case, so an accepted case cannot shadow a later one.
        let mut p = e.plain_package(0, &format!("Strict.t1.c{i}"), &format!("strict-t1-{i}"));
        let case = vectors::cases(e.validator.public(), p.receipt.sig).swap_remove(i);
        ring.validators.push(case.public);
        p.receipt = Receipt { body: ReceiptBody { validator_key: case.public, ..p.receipt.body.clone() }, sig: case.signature };
        p.marker.receipt = p.receipt.id();
        packages.push((case, p));
    }
    // The receipt verifier both staging and T1 call: weak keys are trusted here.
    let st = Store::open(&e.cfg, ring, Faults::none()).unwrap();
    let (_, signer) = e.kf.workspace("w0").unwrap();
    let w = Writer::new(st, e.w[0].id, signer);
    for (case, p) in packages {
        let result = w.publish(&p).await;
        if case.expected {
            assert!(result.is_ok(), "{}: {result:?}", case.name);
        } else {
            assert!(matches!(&result, Err(StoreError::Guard(GuardFailure::ReceiptRejected(_)))), "{}: {result:?}", case.name);
        }
    }
}

#[tokio::main(flavor = "current_thread")]
async fn antientropy_group_import_strict_signature_vectors() {
    use antientropy::{export, import, Item, Outcome};
    use common::*;
    let (a, b) = pair("w2-strict-group-import", 1, Faults::none(), Faults::none());
    let p = a.plain_package(0, "Strict.group", "strict-group");
    a.w[0].publish(&p).await.unwrap();
    let item = export(&a.store).await.unwrap().into_iter().find(|i| matches!(i, Item::Group { .. })).unwrap();
    let Item::Group { marker, revisions, receipt, job, certs } = item else { unreachable!() };
    let cert = Cert::from_bytes(&certs[0]).unwrap();
    let (_, signer) = b.kf.workspace("w0").unwrap();
    // The receiver checks the origin's certificate before staging anything; the valid
    // control gets past it, and every malformed signature must stop there.
    for case in vectors::cases(a.store.ring.writers[&a.w[0].id], cert.sig) {
        let mut ring = (*b.store.ring).clone();
        ring.writers.insert(a.w[0].id, case.public);
        let st = Store::open(&b.cfg, ring, Faults::none()).unwrap();
        let receiver = Writer::new(st, b.w[0].id, signer.clone());
        let mut c = cert.clone();
        c.sig = case.signature;
        let item = Item::Group { marker: marker.clone(), revisions: revisions.clone(), receipt: receipt.clone(),
            job: job.clone(), certs: vec![c.to_bytes()] };
        let outcome = import(&receiver, &item).await.unwrap();
        let no_cert = matches!(&outcome, Outcome::Rejected(r) if r.contains("no valid certificate"));
        assert_eq!(!no_cert, case.expected, "{}: {outcome:?}", case.name);
    }
}

/// W3's agent-key registry: a controller-signed grant binds an AgentID to a certificate
/// key. Its signature is checked by `AgentKeyGrant::verify` wherever a grant is admitted;
/// here directly and through FDB registration. Each vector gets its own grant (and so its
/// own registry slot), signed afresh, then has its encoding defect applied.
#[tokio::main(flavor = "current_thread")]
async fn agent_key_grant_strict_signature_vectors() {
    use paralean_store::authority::AgentKeyGrant;
    use common::*;
    let e = Env::new("w2-strict-agent-grant", 1);
    let signer = Signer::from_seed(std::array::from_fn(|i| (i * 3) as u8));
    let count = vectors::cases(signer.public(), [0; 64]).len();
    for i in 0..count {
        let agent = AgentId::derive(&format!("strict-agent-{i}"));
        let key = Signer::derive(&format!("strict-agent-key-{i}")).public();
        let mut grant = AgentKeyGrant::sign(agent, e.w[0].id, key, &signer);
        let genuine: [u8; 64] = hex::decode(&grant.signature).unwrap().try_into().unwrap();
        let case = &vectors::cases(signer.public(), genuine)[i];
        grant.issuer = hex::encode(case.public);
        grant.signature = hex::encode(case.signature);
        assert_eq!(grant.verify(), case.expected, "verify: {}", case.name);
        let registered = e.store.meta.register_agent_key(grant, case.public).await;
        assert_eq!(registered.is_ok(), case.expected, "register: {}: {registered:?}", case.name);
    }
}

/// W3's agent-key revocation: checked under the deployment authority, directly and by
/// the registry write that fences later T1/T8 writes of the key.
#[tokio::main(flavor = "current_thread")]
async fn agent_key_revocation_strict_signature_vectors() {
    use paralean_store::authority::AgentKeyRevocation;
    use common::*;
    let e = Env::new("w2-strict-agent-revoke", 1);
    let signer = Signer::from_seed(std::array::from_fn(|i| (i * 5) as u8));
    let count = vectors::cases(signer.public(), [0; 64]).len();
    for i in 0..count {
        let key = Signer::derive(&format!("strict-revoked-key-{i}")).public();
        let mut revocation = AgentKeyRevocation::sign(key, &signer);
        let genuine: [u8; 64] = hex::decode(&revocation.signature).unwrap().try_into().unwrap();
        let case = &vectors::cases(signer.public(), genuine)[i];
        revocation.issuer = hex::encode(case.public);
        revocation.signature = hex::encode(case.signature);
        assert_eq!(revocation.verify(&case.public), case.expected, "verify: {}", case.name);
        let revoked = e.store.meta.revoke_agent_key(revocation, case.public).await;
        assert_eq!(revoked.is_ok(), case.expected, "revoke: {}: {revoked:?}", case.name);
    }
}

/// W3's controller deletion grant, which T8 checks against the issuing controller key.
/// T12's batch intent check uses W2's strict verifier (a job issuer here; the controller
/// key goes through the same path).
fn batch_intent_strict_signature_vectors() {
    let signer = Signer::from_seed(std::array::from_fn(|i| (i as u8).wrapping_mul(3)));
    let body = BatchIntent { request: b"strict-batch".to_vec(), members: vec![] };
    let genuine = SignedBatch::sign(body.clone(), &signer);
    for case in vectors::cases(signer.public(), genuine.sig) {
        let mut ring = KeyFile::demo(1).ring();
        ring.job_issuers = vec![case.public];
        let intent = SignedBatch { body: body.clone(), sig: case.signature };
        assert_eq!(intent.issued_by(&ring), case.expected, "{}", case.name);
    }
}

fn controller_delete_grant_strict_signature_vectors() {
    use paralean_store::authority::ControllerDeleteGrant;
    let signer = Signer::from_seed(std::array::from_fn(|i| (i * 7) as u8));
    let tombstone = Id([9; 32]);
    let grant = ControllerDeleteGrant::sign(tombstone, 3, &signer);
    let genuine: [u8; 64] = hex::decode(&grant.signature).unwrap().try_into().unwrap();
    for case in vectors::cases(signer.public(), genuine) {
        let mut g = grant.clone();
        g.issuer = hex::encode(case.public);
        g.signature = hex::encode(case.signature);
        assert_eq!(g.verify(&tombstone, &case.public), case.expected, "{}", case.name);
    }
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("batch_intent_strict_signature_vectors", || { batch_intent_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("store_strict_signature_vectors", || { store_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("antientropy_import_strict_signature_vectors", || { antientropy_import_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("t1_publication_strict_receipt_signature_vectors", || { t1_publication_strict_receipt_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("antientropy_group_import_strict_signature_vectors", || { antientropy_group_import_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("agent_key_grant_strict_signature_vectors", || { agent_key_grant_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("agent_key_revocation_strict_signature_vectors", || { agent_key_revocation_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("controller_delete_grant_strict_signature_vectors", || { controller_delete_grant_strict_signature_vectors(); Ok(()) }),
    ]);
}
