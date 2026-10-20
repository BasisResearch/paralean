#!/usr/bin/env python3
"""Live P5 guarded-fence home check on a fresh deployment of the private P5 instance.

Source impl/p5/scripts/env.sh first. This creates no cluster or coding worker.
It pins a two-member federation before writing metadata, then checks that a
local-home target can be fenced while a foreign-home target is refused.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import time
from pathlib import Path


def call(argv: list[str], env: dict[str, str], *, succeeds: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(argv, env=env, capture_output=True, text=True)
    if succeeds and result.returncode:
        raise AssertionError(f"{Path(argv[0]).name} {argv[1]} failed with status {result.returncode}")
    return result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("run_dir", type=Path)
    ap.add_argument("--repo", type=Path, default=Path.cwd())
    args = ap.parse_args()
    if not os.environ.get("PARALEAN_INSTANCE", "").startswith("p5-"):
        ap.error("source the P5 environment with a private p5-* PARALEAN_INSTANCE")
    repo = args.repo.resolve()
    p2_dir = Path(os.environ.get("PARALEAN_P2_DIR", repo / "impl/p2"))
    p2 = os.environ.get("PARALEAN_P2_CLI", str(p2_dir / "target/release/paralean-p2"))
    bridge = os.environ.get("PARALEAN_P5_BRIDGE", str(repo / "impl/p2/target/release/paralean-p5-store"))
    run_dir = args.run_dir.resolve()
    os.umask(0o077)  # key files and transport seeds stay private to this run
    run_dir.mkdir(parents=True, exist_ok=False)
    deployment = f"p5home-{int(time.time())}-{os.getpid()}"
    peer = deployment + "-peer"
    local_name, foreign_name = "P5Home.local", "P5Home.foreign"
    env = {**os.environ, "PARALEAN_DEPLOYMENT": deployment}
    local_keys, peer_keys = run_dir / "local-keys.json", run_dir / "peer-keys.json"
    local_seed, peer_seed = run_dir / "local-transport.seed", run_dir / "peer-transport.seed"
    call([p2, "keys", "init", str(local_keys), "--workspaces", "1"], env)
    call([p2, "keys", "init", str(peer_keys), "--workspaces", "1"], env)
    local_public = call([p2, "ae-keygen", str(local_seed)], env).stdout.strip()
    peer_public = call([p2, "ae-keygen", str(peer_seed)], env).stdout.strip()
    local_env = {**env, "PARALEAN_KEYS": str(local_keys)}
    peer_env = {**env, "PARALEAN_KEYS": str(peer_keys)}
    members = {
        deployment: json.loads(call([p2, "federation-member", deployment, local_public], local_env).stdout),
        peer: json.loads(call([p2, "federation-member", peer, peer_public], peer_env).stdout),
    }
    config = run_dir / "federation.json"
    config.write_text(json.dumps({"deployment": deployment, "members": members,
                                  "target_homes": {local_name: deployment, foreign_name: peer},
                                  "signing_seed_file": str(local_seed)}, sort_keys=True) + "\n")
    call([p2, "federation-init", str(config)], local_env)

    assigned = json.loads(call([bridge, "assign-target", "--name", local_name,
                                "--ws", "w0", "--request", "p5-home-local-assign"], local_env).stdout)
    fenced = json.loads(call([bridge, "fence-unfinished", "--name", local_name,
                              "--ws", "w0", "--expected-epoch", str(assigned["epoch"]),
                              "--expected-head", "none", "--request", "p5-home-local-fence"], local_env).stdout)
    if fenced.get("outcome") != "fenced" or fenced.get("epoch") != assigned["epoch"] + 1:
        raise AssertionError("local-home target was not fenced")
    refused = call([bridge, "fence-unfinished", "--name", foreign_name,
                    "--ws", "w0", "--expected-epoch", "1",
                    "--expected-head", "none", "--request", "p5-home-foreign-fence"],
                   local_env, succeeds=False)
    if refused.returncode == 0 or "foreign federation home" not in refused.stderr:
        raise AssertionError("foreign-home fence did not fail at the federation guard")
    evidence = {"deployment": deployment, "local_fence_epoch": fenced["epoch"],
                "foreign_guard_rejected": True,
                "git": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()}
    (run_dir / "federation-home-fault.json").write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
