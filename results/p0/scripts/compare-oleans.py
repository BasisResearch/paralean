#!/usr/bin/env python3
"""Compare two Mathlib build trees' .olean* files, ignoring only the olean header's
version-string field (bytes 7..0x28). Usage: compare-oleans.py CACHE_TREE LOCAL_TREE"""
import os, sys
from concurrent.futures import ThreadPoolExecutor
A, B = sys.argv[1], sys.argv[2]
def walk(root):
    out = set()
    for d, _, fs in os.walk(os.path.join(root, '.lake')):
        for f in fs:
            if '.olean' in f and not f.endswith('.hash'):
                out.add(os.path.relpath(os.path.join(d, f), root))
    return out
fa, fb = walk(A), walk(B)
common = sorted(fa & fb)
def cmp(f):
    a = open(os.path.join(A, f), 'rb').read(); b = open(os.path.join(B, f), 'rb').read()
    if a == b: return 'identical'
    if len(a) == len(b) and a[:7] == b[:7] and a[0x28:] == b[0x28:]: return 'version-field-only'
    return 'differs'
with ThreadPoolExecutor(32) as ex: res = list(ex.map(cmp, common))
from collections import Counter
c = Counter(res)
print(f"cache-only={len(fa-fb)} local-only={len(fb-fa)} common={len(common)} {dict(c)}")
for f, r in zip(common, res):
    if r == 'differs': print('DIFF', f)
