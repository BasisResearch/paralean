mod common;
#[path = "../../../../../verification/fixtures/ed25519_cases.rs"]
mod vectors;

use paralean_store::*;

#[test]
fn store_strict_signature_vectors() {
    let signer = Signer::from_seed(std::array::from_fn(|i| i as u8));
    let id = Id([42; 32]);
    for case in vectors::cases(signer.public(), signer.sign(&id)) {
        assert_eq!(sign::verify(&case.public, &id, &case.signature), case.expected, "{}", case.name);
    }
}

#[tokio::test]
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
