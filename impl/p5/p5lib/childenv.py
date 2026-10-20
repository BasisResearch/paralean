"""Environment filtering for every process the P5 controller starts.

Child programs need ordinary configuration (PATH, HOME, LEAN_PATH, PARALEAN_STORE,
PARALEAN_TRUST, ...), and the set differs between the store bridge, plr, the
Lean binary and arbitrary coding CLIs, so a closed allowlist would break them.
Instead every credential-shaped name is removed unless the caller names it as
one that particular child needs. Controller-only secrets can never be allowed.
"""

from __future__ import annotations

from typing import Iterable, Mapping

# Held only by the controller: deployment recovery and Garage administration.
CONTROLLER_ONLY = frozenset({
    "PARALEAN_P5_RECOVERY_SECRET", "PARALEAN_P5_RECOVERY_SECRET_FILE",
    "PARALEAN_GARAGE_ADMIN_TOKEN", "PARALEAN_GARAGE_RPC_SECRET",
})

# Substrings that mark a variable as a credential for any program.
SENSITIVE_MARKERS = ("SECRET", "TOKEN", "PASSWORD", "PASSWD", "CREDENTIAL", "PRIVATE",
                     "SEED", "API_KEY", "ACCESS_KEY")

# Store credentials the P3/P2 tools use to reach this deployment's own bucket.
STORE_CREDENTIALS = ("PARALEAN_S3_ACCESS_KEY", "PARALEAN_S3_SECRET_KEY")


def is_sensitive(name: str) -> bool:
    upper = name.upper()
    if upper in CONTROLLER_ONLY or upper.startswith("PARALEAN_PEER_"):
        return True
    # PARALEAN_KEYS, PARALEAN_PEER_KEYS and similar name signing-key material.
    if upper.startswith("PARALEAN_") and "KEY" in upper:
        return True
    return any(marker in upper for marker in SENSITIVE_MARKERS)


def filter_env(env: Mapping[str, str], allow: Iterable[str] = ()) -> dict[str, str]:
    """Copy `env` without credentials, except the non-controller names in `allow`."""
    allowed = frozenset(allow) - CONTROLLER_ONLY
    return {key: value for key, value in env.items()
            if key not in CONTROLLER_ONLY and (key in allowed or not is_sensitive(key))}
