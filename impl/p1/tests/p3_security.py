#!/usr/bin/env python3
"""Executable adversarial fixtures for the Lean P3 receipt decoder and trust gate."""

import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization


ROOT = Path(__file__).resolve().parents[1]


def uv(n):
    out = bytearray()
    while n >= 128:
        out.append((n & 127) | 128)
        n >>= 7
    out.append(n)
    return bytes(out)


def blob(b):
    return uv(len(b)) + b


def signed(domain, body, key):
    pre = b"paralean\0" + domain + b"\0" + body
    digest = hashlib.sha256(pre).digest()
    return blob(pre) + blob(key.sign(digest)), digest


def pub(key):
    return key.public_key().public_bytes(serialization.Encoding.Raw,
                                         serialization.PublicFormat.Raw)


def fixture(directory):
    auth, issuer, validator = (Ed25519PrivateKey.generate() for _ in range(3))
    group, capsule, base, policy, checker = (bytes([i]) * 32 for i in range(1, 6))
    worker = bytes([6]) * 16
    name = uv(2) + b"\0" + blob(b"P5") + b"\0" + blob(b"x")
    target = uv(1) + name + uv(1) + blob(bytes([7]) * 32)
    other_target = uv(1) + name + uv(2) + blob(bytes([7]) * 32)

    def job(request, key):
        body = (uv(0) + blob(request) + blob(group) + blob(capsule) + uv(0) +
                blob(base) + blob(policy) + blob(checker) + blob(worker) + target +
                uv(1000) + uv(0))
        return signed(b"v0/job", body, key)

    authority_job, job_id = job(b"authority", auth)
    issuer_job, _ = job(b"authority", issuer)
    replacement_job, _ = job(b"replacement", issuer)

    def receipt(slot):
        body = (uv(0) + blob(group) + blob(base) + blob(pub(validator)) +
                blob(checker) + blob(policy) + b"\1" + blob(job_id) +
                b"\1" + blob(slot) + b"\0" + uv(0))
        return signed(b"v0/receipt", body, validator)

    good, receipt_id = receipt(target)
    wrong, _ = receipt(other_target)
    weak_body = (uv(0) + blob(group) + blob(base) + blob(bytes([1]) + bytes(31)) +
                 blob(checker) + blob(policy) + b"\1" + blob(job_id) +
                 b"\1" + blob(target) + b"\0" + uv(0))
    weak_pre = b"paralean\0v0/receipt\0" + weak_body
    weak_id = hashlib.sha256(weak_pre).digest()
    weak = blob(weak_pre) + blob(bytes([1]) + bytes(63))
    (directory / "authority-job.bin").write_bytes(authority_job)
    (directory / "issuer-job.bin").write_bytes(issuer_job)
    (directory / "replacement-job.bin").write_bytes(replacement_job)
    (directory / "receipt.bin").write_bytes(good)
    (directory / "wrong-target.bin").write_bytes(wrong)
    (directory / "weak-receipt.bin").write_bytes(weak)
    jobs = directory / "p3" / "jobs"
    receipts = directory / "p3" / "receipts"
    jobs.mkdir(parents=True)
    receipts.mkdir(parents=True)
    (jobs / (job_id.hex() + ".bin")).write_bytes(authority_job)
    (receipts / (receipt_id.hex() + ".bin")).write_bytes(good)
    (receipts / (weak_id.hex() + ".bin")).write_bytes(weak)
    trust = {"validators": [pub(validator).hex(), (bytes([1]) + bytes(31)).hex()], "authority": pub(auth).hex(),
             "jobIssuers": [["w0", pub(issuer).hex()]], "policies": [policy.hex()],
             "checkers": [checker.hex()], "base": base.hex(), "allowedAxioms": [],
             "agents": [["w0", worker.hex()]]}
    (directory / "trust.json").write_text(json.dumps(trust))
    vectors = ROOT.parents[1] / "verification" / "fixtures" / "ed25519-strict-vectors.json"
    return [str(directory), pub(auth).hex(), pub(issuer).hex(), pub(validator).hex(),
            group.hex(), capsule.hex(), receipt_id.hex(), job_id.hex(), weak_id.hex(), str(vectors)]


def main():
    with tempfile.TemporaryDirectory() as temp:
        directory = Path(temp)
        args = fixture(directory)
        env = {**os.environ, "PARALEAN_TRUST": str(directory / "trust.json")}
        if custom_path := env.get("PARALEAN_P1_TEST_LEAN_PATH"):
            env["LEAN_PATH"] = custom_path
            command = [env.get("PARALEAN_P1_TEST_LEAN", "lean"), "--run", "tests/P3Security.lean", *args]
        else:
            subprocess.run(["lake", "build", "Paralean.P3"], cwd=ROOT, env=env, check=True)
            command = ["lake", "env", "lean", "--run", "tests/P3Security.lean", *args]
        subprocess.run(command, cwd=ROOT, env=env, check=True)


if __name__ == "__main__":
    main()
