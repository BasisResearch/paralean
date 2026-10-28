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
        let item = Item::Tombstone { tombstone: t.preimage(), certs: vec![c.to_bytes()] };
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

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("store_strict_signature_vectors", || { store_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("antientropy_import_strict_signature_vectors", || { antientropy_import_strict_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("t1_publication_strict_receipt_signature_vectors", || { t1_publication_strict_receipt_signature_vectors(); Ok(()) }),
        libtest_mimic::Trial::test("antientropy_group_import_strict_signature_vectors", || { antientropy_group_import_strict_signature_vectors(); Ok(()) }),
    ]);
}
