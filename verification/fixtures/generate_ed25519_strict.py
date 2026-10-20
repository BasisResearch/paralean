#!/usr/bin/env python3
"""Generate deterministic strict Ed25519 acceptance vectors for Lean and Rust."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization


P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = 37095705934669439343138083508754565189542113879843219016388785533085940283555
IDENTITY = bytes([1]) + bytes(31)
ZERO = (0, 1, 1, 0)
OUT = Path(__file__).with_name("ed25519-strict-vectors.json")


def add(a, b):
    x1, y1, z1, t1 = a
    x2, y2, z2, t2 = b
    aa = (y1 - x1) * (y2 - x2) % P
    bb = (y1 + x1) * (y2 + x2) % P
    cc = 2 * D * t1 * t2 % P
    dd = 2 * z1 * z2 % P
    e, f, g, h = (bb-aa) % P, (dd-cc) % P, (dd+cc) % P, (bb+aa) % P
    return e*f % P, g*h % P, f*g % P, e*h % P


def mul(n, point):
    out = ZERO
    while n:
        if n & 1:
            out = add(out, point)
        point = add(point, point)
        n >>= 1
    return out


def encode(point):
    x, y, z, _ = point
    inverse = pow(z, P-2, P)
    x, y = x*inverse % P, y*inverse % P
    return (y | ((x & 1) << 255)).to_bytes(32, "little")


def decode(y, sign=0):
    y2 = y*y % P
    u, v = (y2-1) % P, (D*y2+1) % P
    x = u * pow(v, 3, P) * pow(u*pow(v, 7, P) % P, (P-5)//8, P) % P
    if v*x*x % P != u:
        x = x * 19681161376707505956807079304988542015446066515923890162744021073123829784752 % P
    if v*x*x % P != u:
        return None
    if x & 1 != sign:
        x = P-x
    return x, y, 1, x*y % P


def torsion_points():
    for y in range(2, 100):
        point = decode(y)
        if point is None:
            continue
        torsion = mul(L, point)
        encodings = [encode(mul(i, torsion)) for i in range(8)]
        if len(set(encodings)) == 8 and encodings[0] == IDENTITY:
            return encodings
    raise RuntimeError("could not derive an order-eight torsion point")


def main():
    key = Ed25519PrivateKey.from_private_bytes(bytes(range(32)))
    public = key.public_key().public_bytes(serialization.Encoding.Raw,
                                            serialization.PublicFormat.Raw)
    controls = [b"", b"paralean-ed25519-strict-v1"]
    vectors = []

    def add_vector(case, message, public_key, signature, expect, kind):
        vectors.append({"case": case, "kind": kind, "message_hex": message.hex(),
                        "public_key_hex": public_key.hex(), "signature_hex": signature.hex(),
                        "expect": expect})

    for index, message in enumerate(controls):
        add_vector(f"valid_{index}", message, public, key.sign(message), True, "valid")
    base_sig = key.sign(controls[1])
    torsion = torsion_points()
    for index, point in enumerate(torsion):
        # With R = identity and S = 0, the non-strict equation succeeds when
        # H(R,A,m) is divisible by eight. This directly checks A rejection.
        counter = next(n for n in range(256) if
                       int.from_bytes(hashlib.sha512(IDENTITY + point + n.to_bytes(2, "little")).digest(),
                                      "little") % 8 == 0)
        message = counter.to_bytes(2, "little")
        add_vector(f"small_order_A_{index}", message, point, IDENTITY + bytes(32), False,
                   "small_order_A")
        add_vector(f"small_order_R_{index}", controls[1], public, point + base_sig[32:], False,
                   "small_order_R")
    # The field element y occupies 255 bits. Every y >= p in that range is
    # noncanonical, with either sign bit; negative zero is separate.
    for offset in range(19):
        for sign in (0, 1):
            encoding = (P + offset | (sign << 255)).to_bytes(32, "little")
            add_vector(f"noncanonical_A_y{offset}_sign{sign}", controls[1], encoding,
                       IDENTITY + bytes(32), False, "noncanonical_A")
            add_vector(f"noncanonical_R_y{offset}_sign{sign}", controls[1], public,
                       encoding + base_sig[32:], False, "noncanonical_R")
    negative_zero = (1 | (1 << 255)).to_bytes(32, "little")
    add_vector("negative_zero_A", controls[1], negative_zero, IDENTITY + bytes(32), False,
               "noncanonical_A")
    add_vector("negative_zero_R", controls[1], public, negative_zero + base_sig[32:], False,
               "noncanonical_R")
    for label, scalar in (("L", L), ("L_plus_1", L+1), ("max_u256", 2**256-1)):
        add_vector(f"S_ge_{label}", controls[1], public,
                   base_sig[:32] + scalar.to_bytes(32, "little"), False, "noncanonical_S")
    OUT.write_text(json.dumps({"format": "ed25519-strict-v1", "torsion_hex": [x.hex() for x in torsion],
                               "vectors": vectors}, indent=2) + "\n")
    print(f"{OUT}: {len(vectors)} vectors")


if __name__ == "__main__":
    main()
