#!/usr/bin/env python3
"""Exercise W4's delete boundary against its own Garage with real SigV4."""
import json
import http.client
import os
from pathlib import Path
import secrets
import socket
import subprocess
import time

import boto3
from botocore.auth import S3SigV4Auth
from botocore.awsrequest import AWSRequest
from botocore.config import Config
from botocore.credentials import Credentials
from botocore.exceptions import ClientError
import requests


def main():
    assert os.environ["PARALEAN_INSTANCE"] == "w4-scale"
    root = Path(__file__).resolve().parents[3]
    home = Path(os.environ["PARALEAN_HOME"])
    garage = Path(os.environ["PARALEAN_P2_PREFIX"]) / "bin/garage"
    config = home / "garage/n0/garage.toml"
    gc_key = "GK" + secrets.token_hex(12)
    gc_secret = secrets.token_hex(32)
    bucket = os.environ["PARALEAN_S3_BUCKET"]

    def admin(*args):
        subprocess.run([str(garage), "-c", str(config), *args],
                       check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)

    admin("key", "import", "--yes", "-n", "w4-gc-boundary", gc_key, gc_secret)
    admin("bucket", "allow", "--read", "--write", bucket, "--key", gc_key)
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        port = s.getsockname()[1]
    endpoint = f"http://127.0.0.1:{port}"
    log = root / ".runs/w4/guard-live.log"
    results = {}
    with log.open("w") as output:
        proc = subprocess.Popen([
            str(root / "impl/p2/target/debug/s3-guard"),
            "--listen", f"127.0.0.1:{port}",
            "--upstream", "127.0.0.1:29520",
            "--gc-access-key", gc_key,
        ], stdout=output, stderr=output)
        try:
            for _ in range(100):
                try:
                    requests.get(endpoint, timeout=1)
                    break
                except requests.ConnectionError:
                    time.sleep(.05)
            else:
                raise RuntimeError("W4 test guard did not start")

            def client(key, secret, url=endpoint):
                return boto3.client("s3", endpoint_url=url,
                                    region_name=os.environ["PARALEAN_S3_REGION"],
                                    aws_access_key_id=key, aws_secret_access_key=secret,
                                    config=Config(signature_version="s3v4",
                                                  retries={"max_attempts": 0},
                                                  s3={"addressing_style": "path"}))

            app = client(os.environ["PARALEAN_S3_ACCESS_KEY"], os.environ["PARALEAN_S3_SECRET_KEY"])
            gc = client(gc_key, gc_secret)
            obj = "w4-guard-test/" + secrets.token_hex(16)
            app.put_object(Bucket=bucket, Key=obj, Body=b"unreferenced test bytes")

            def denied(name, action):
                try:
                    action()
                except ClientError as e:
                    assert e.response["ResponseMetadata"]["HTTPStatusCode"] == 403, e
                    results[name] = True
                else:
                    raise AssertionError(f"{name}: destructive request accepted")

            denied("application_delete_denied", lambda: app.delete_object(Bucket=bucket, Key=obj))
            denied("forged_gc_signature_denied",
                   lambda: client(gc_key, "not-the-gc-secret").delete_object(Bucket=bucket, Key=obj))
            denied("gc_denied_by_default",
                   lambda: client(gc_key, gc_secret, os.environ["PARALEAN_S3_ENDPOINT"])
                   .delete_object(Bucket=bucket, Key=obj))
            denied("gc_bucket_delete_denied", lambda: gc.delete_bucket(Bucket=bucket))
            denied("gc_bulk_delete_denied",
                   lambda: gc.delete_objects(Bucket=bucket, Delete={"Objects": [{"Key": obj}]}))
            # Sign the exact encoded query, then send that same raw request path.
            # http.client preserves %64; high-level clients may normalize it.
            payload = f"<Delete><Object><Key>{obj}</Key></Object></Delete>".encode()
            signed = AWSRequest(
                method="POST", url=f"{endpoint}/{bucket}?%64elete", data=payload,
                headers={"Host": f"127.0.0.1:{port}", "Content-Type": "application/xml"},
            )
            S3SigV4Auth(Credentials(gc_key, gc_secret), "s3",
                         os.environ["PARALEAN_S3_REGION"]).add_auth(signed)
            connection = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
            try:
                connection.request("POST", f"/{bucket}?%64elete", body=payload,
                                   headers=dict(signed.headers.items()))
                encoded_response = connection.getresponse()
                encoded_body = encoded_response.read()
                assert encoded_response.status == 403, encoded_response.status
                assert b"DeleteObjects is denied" in encoded_body, encoded_body
                results["gc_encoded_bulk_delete_denied"] = True
            finally:
                connection.close()
            assert app.get_object(Bucket=bucket, Key=obj)["Body"].read() == b"unreferenced test bytes"
            gc.delete_object(Bucket=bucket, Key=obj)
            try:
                app.head_object(Bucket=bucket, Key=obj)
            except ClientError as e:
                assert e.response["ResponseMetadata"]["HTTPStatusCode"] == 404, e
                results["authenticated_gc_object_delete"] = True
            else:
                raise AssertionError("GC delete did not remove object")
        finally:
            proc.terminate()
            proc.wait(timeout=10)
            admin("bucket", "deny", "--read", "--write", bucket, "--key", gc_key)
    report = root / "impl/p3/results/w4-guard.json"
    report.write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, sort_keys=True))


if __name__ == "__main__":
    main()
