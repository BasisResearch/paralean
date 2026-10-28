#!/usr/bin/env python3
"""W2 Lean security regressions: unit checks and the capsule command gate end to end.

The end-to-end cases publish-looking capsules (a correct package ID, capsule object, a
receipt signed by a trusted validator for a controller-signed job, a publication record)
whose text runs code (`#eval`, `initialize`) or disables kernel checking
(`set_option «debug».skipKernelTC`). Both the validator (`checkGroup`) and a consumer
(`remote_decl%` in a plain Lean file) must refuse them before elaboration, and the
sentinel file the code would write must not exist. A benign capsule must still load.

Environment: PARALEAN_P1_TEST_LEAN_PATH / PARALEAN_P1_TEST_LEAN select a mutated build
(tests/check_security_mutations.py); otherwise the lake build of this checkout is used.
"""

import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

from cryptography.hazmat.primitives import serialization
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey

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
    return key.public_key().public_bytes(serialization.Encoding.Raw, serialization.PublicFormat.Raw)


class Lean:
    def __init__(self):
        self.env = dict(os.environ)
        self.env.pop("PARALEAN_MATHLIB", None)
        if path := self.env.get("PARALEAN_P1_TEST_LEAN_PATH"):
            self.env["LEAN_PATH"] = path
            self.lean = self.env.get("PARALEAN_P1_TEST_LEAN", "lean")
        else:
            subprocess.run(["lake", "build", "Paralean"], cwd=ROOT, env=self.env, check=True,
                           stdout=subprocess.DEVNULL)
            out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT, env=self.env,
                                 check=True, capture_output=True, text=True).stdout.strip()
            self.env["LEAN_PATH"] = out
            # The pinned toolchain's binary: the consumer runs outside this project, where
            # elan would otherwise need a default toolchain.
            self.lean = subprocess.run(["elan", "which", "lean"], cwd=ROOT, env=self.env, check=True,
                                       capture_output=True, text=True).stdout.strip()

    def run(self, args, env=None, cwd=ROOT):
        return subprocess.run([self.lean, *args], cwd=cwd, env={**self.env, **(env or {})},
                              capture_output=True, text=True)

    def helper(self, *args, env=None):
        return self.run(["--run", str(ROOT / "tests" / "LeanSecurity.lean"), *args], env=env)


def publish(store, ids, keys):
    """Receipt, job, trust and publication record for the capsule `ids` names."""
    auth, validator = keys
    group, capsule = bytes.fromhex(ids["declId"]), bytes.fromhex(ids["capsule"])
    base, policy, checker = (bytes([i]) * 32 for i in range(3, 6))
    worker = bytes([6]) * 16
    job_body = (uv(0) + blob(b"req-" + group[:8]) + blob(group) + blob(capsule) + uv(0) +
                blob(base) + blob(policy) + blob(checker) + blob(worker) + uv(0) + uv(1000) + uv(0))
    job, job_id = signed(b"v0/job", job_body, auth)
    receipt_body = (uv(0) + blob(group) + blob(base) + blob(pub(validator)) + blob(checker) +
                    blob(policy) + b"\1" + blob(job_id) + b"\0" + b"\0" + uv(0))
    receipt, receipt_id = signed(b"v0/receipt", receipt_body, validator)
    p3 = store / "p3"
    for d in ("jobs", "receipts", "records"):
        (p3 / d).mkdir(parents=True, exist_ok=True)
    (p3 / "jobs" / (job_id.hex() + ".bin")).write_bytes(job)
    (p3 / "receipts" / (receipt_id.hex() + ".bin")).write_bytes(receipt)
    marker_id = hashlib.sha256(b"marker" + group).hexdigest()
    record = {"kind": "marker", "id": marker_id, "group": ids["declId"], "revisions": [],
              "receipt": receipt_id.hex(), "file": "Test/Evil.lean", "anchor": None, "lamport": 1,
              "author": worker.hex(), "rootPath": [], "lineageKeys": [], "capsule": ids["capsule"],
              "pid": ids["gid"]}
    (p3 / "records" / f"m-{marker_id}.json").write_text(json.dumps(record))
    trust = {"validators": [pub(validator).hex()], "authority": pub(auth).hex(), "jobIssuers": [],
             "policies": [policy.hex()], "checkers": [checker.hex()], "base": base.hex(),
             "allowedAxioms": [], "agents": [["evil", worker.hex()]]}
    (store / "trust.json").write_text(json.dumps(trust))
    # The live consumer check (`plr check-receipt`) admits: only the gate stands in the way.
    plr = store / "fake-plr"
    plr.write_text("#!/usr/bin/env python3\nimport json, sys\n"
                   f"print(json.dumps({{'admits': True, 'receipt': '{receipt_id.hex()}'}}) "
                   "if sys.argv[1:2] == ['check-receipt'] else json.dumps({'error': 'offline'}))\n")
    plr.chmod(0o700)
    return {"PARALEAN_STORE": str(store), "PARALEAN_TRUST": str(store / "trust.json"),
            "PARALEAN_PLR": str(plr)}


def case(lean, temp, variant, keys):
    store = temp / variant / "store"
    sentinel = temp / variant / "SENTINEL"
    store.mkdir(parents=True)
    made = lean.helper("mkcapsule", str(store), variant, str(sentinel))
    assert made.returncode == 0, made.stdout + made.stderr
    ids = json.loads(made.stdout.strip().splitlines()[-1])
    env = publish(store, ids, keys)
    out = {}
    # validator: the job's closure through checkGroup (interpreted)
    v = lean.helper("check-group", str(store), ids["gid"], ids["declId"], env=env)
    out["validator"] = (v.returncode, v.stdout[-3000:] + v.stderr[-3000:], sentinel.exists())
    sentinel.unlink(missing_ok=True)
    # consumer: a working file that loads the published package
    consumer = temp / variant / "consumer"
    consumer.mkdir()
    (consumer / "Consumer.lean").write_text(f"import Paralean.Remote\nremote_decl% \"{ids['declId']}\"\n")
    c = lean.run([str(consumer / "Consumer.lean")], env=env, cwd=consumer)
    out["consumer"] = (c.returncode, c.stdout[-3000:] + c.stderr[-3000:], sentinel.exists())
    return out


def main():
    lean = Lean()
    with tempfile.TemporaryDirectory(prefix="w2-lean-security-") as t:
        temp = Path(t)
        unit = lean.helper("unit", str(temp / "unit"))
        print(unit.stdout, unit.stderr, end="")
        if unit.returncode != 0 or "Lean security checks passed" not in unit.stdout:
            raise SystemExit("unit checks failed")
        keys = (Ed25519PrivateKey.generate(), Ed25519PrivateKey.generate())
        refusals = {
            "eval": ("capsule gate", "refused before elaboration", "Lean.Parser.Command.eval"),
            "init": ("capsule gate", "refused before elaboration", "Lean.Parser.Command.initialize"),
            "init-touched": ("initializer effects", "refused before elaboration", "initialize"),
            "skipkernel": ("capsule gate", "refused before elaboration", "debug.skipKernelTC"),
        }
        for variant, (vneedle, cneedle, what) in refusals.items():
            r = case(lean, temp, variant, keys)
            for side, needle in (("validator", vneedle), ("consumer", cneedle)):
                code, log, wrote = r[side]
                if wrote:
                    raise SystemExit(f"uncaught exception: {variant} {side}: the capsule's code ran (sentinel written)")
                if code == 0 or needle not in log or what not in log:
                    raise SystemExit(f"uncaught exception: {variant} {side}: accepted invalid input\n{log}")
            print(f"{variant}: refused by validator and consumer; sentinel absent")
        r = case(lean, temp, "benign", keys)
        code, log, _ = r["consumer"]
        if code != 0:
            raise SystemExit(f"benign consumer: refused valid input\n{log}")
        print("benign: consumer loads it")
    print("Lean W2 security checks passed")


if __name__ == "__main__":
    main()
