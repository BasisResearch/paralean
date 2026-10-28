//! Control-plane authentication is checked on real TCP connections. A signed request
//! is bound to the server's fresh challenge, so recording one exchange is insufficient
//! to impersonate its caller later.
// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.
#![deny(dead_code)]

mod common;

use std::time::Duration;

use common::*;
use paralean_control::controller::{ControlRequest, ControlResponse};
use paralean_store::Signer;
use paralean_validator_api::{rpc, ValidatorRequest, ValidatorResponse};
use tokio::net::TcpStream;

async fn replayed_request_is_rejected<Q: serde::Serialize + Clone + rpc::Service>(
    addr: &str,
    request: Q,
    signer: &Signer,
    server: &[u8; 32],
) {
    let mut first = TcpStream::connect(addr).await.unwrap();
    let challenge: rpc::Challenge = rpc::read_frame(&mut first).await.unwrap();
    let captured = rpc::signed_request(request, signer, server, &challenge.nonce).unwrap();
    rpc::write_frame(&mut first, &captured).await.unwrap();
    let _: rpc::SignedResponse<serde_json::Value> = rpc::read_frame(&mut first).await.unwrap();

    let mut second = TcpStream::connect(addr).await.unwrap();
    let next: rpc::Challenge = rpc::read_frame(&mut second).await.unwrap();
    assert_ne!(
        challenge.nonce, next.nonce,
        "server reused an authentication challenge"
    );
    rpc::write_frame(&mut second, &captured).await.unwrap();
    assert!(
        rpc::read_frame::<rpc::SignedResponse<serde_json::Value>>(&mut second)
            .await
            .is_err(),
        "server accepted a replayed request"
    );
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn controller_rejects_unsigned_unknown_and_replayed_rpc() {
    let c = Cluster::start("auth-controller", Opts::default()).await;
    let authority = c.kf.authority_signer().unwrap();
    let status = ControlRequest::Status;
    let mut raw = TcpStream::connect(&c.ctl_addr).await.unwrap();
    let _: rpc::Challenge = rpc::read_frame(&mut raw).await.unwrap();
    rpc::write_frame(&mut raw, &status).await.unwrap();
    assert!(
        rpc::read_frame::<rpc::SignedResponse<ControlResponse>>(&mut raw)
            .await
            .is_err()
    );

    let stranger = Signer::derive("p3-test-unauthorized-caller");
    let result: std::io::Result<ControlResponse> = rpc::call_authenticated(
        &c.ctl_addr,
        &status,
        &stranger,
        &authority.public(),
        Duration::from_secs(3),
    )
    .await;
    assert!(result.is_err(), "unknown signer received {result:?}");
    let (worker, _) = c.kf.workspace("w0").unwrap();
    let spoof: std::io::Result<ControlResponse> = rpc::call_authenticated(
        &c.ctl_addr,
        &ControlRequest::Register {
            worker: worker.hex(),
            capacity_mb: 1,
        },
        &stranger,
        &authority.public(),
        Duration::from_secs(3),
    )
    .await;
    assert!(
        spoof.is_err(),
        "caller impersonated a registered worker: {spoof:?}"
    );

    replayed_request_is_rejected(&c.ctl_addr, status, &authority, &authority.public()).await;
    assert!(matches!(
        c.call(ControlRequest::Status).await,
        ControlResponse::Status { .. }
    ));
}

#[tokio::main(flavor = "multi_thread", worker_threads = 2)]
async fn validator_rejects_unsigned_unknown_and_replayed_rpc() {
    let c = Cluster::start("auth-validator", Opts::default()).await;
    let authority = c.kf.authority_signer().unwrap();
    let status = ValidatorRequest::Status;
    let mut raw = TcpStream::connect(&c.vaddrs[0]).await.unwrap();
    let _: rpc::Challenge = rpc::read_frame(&mut raw).await.unwrap();
    rpc::write_frame(&mut raw, &status).await.unwrap();
    assert!(
        rpc::read_frame::<rpc::SignedResponse<ValidatorResponse>>(&mut raw)
            .await
            .is_err()
    );

    let stranger = Signer::derive("p3-test-unauthorized-caller");
    let result: std::io::Result<ValidatorResponse> = rpc::call_authenticated(
        &c.vaddrs[0],
        &status,
        &stranger,
        &c.vsigners[0].public(),
        Duration::from_secs(3),
    )
    .await;
    assert!(result.is_err(), "unknown signer received {result:?}");

    replayed_request_is_rejected(&c.vaddrs[0], status, &authority, &c.vsigners[0].public()).await;
    let answer: ValidatorResponse = rpc::call_authenticated(
        &c.vaddrs[0],
        &ValidatorRequest::Status,
        &authority,
        &c.vsigners[0].public(),
        Duration::from_secs(3),
    )
    .await
    .unwrap();
    assert!(matches!(answer, ValidatorResponse::Status { .. }));
}

// Own the process lifetime: stop FDB only after every test runtime has dropped.
fn main() {
    common::run_tests(vec![
        libtest_mimic::Trial::test("controller_rejects_unsigned_unknown_and_replayed_rpc", || { controller_rejects_unsigned_unknown_and_replayed_rpc(); Ok(()) }),
        libtest_mimic::Trial::test("validator_rejects_unsigned_unknown_and_replayed_rpc", || { validator_rejects_unsigned_unknown_and_replayed_rpc(); Ok(()) }),
    ]);
}
