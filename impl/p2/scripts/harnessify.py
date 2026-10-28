#!/usr/bin/env python3
"""Convert FDB integration-test files to the explicit libtest-mimic main.

The stock libtest main returns into process exit with the FDB network thread still
running, which can crash in libfdb_c's exit-time destructors (docs/w2-chaos-notes.md).
Each converted file runs its tests from `fn main` through `run_tests`, which stops FDB
before exiting. Usage: harnessify.py RUNNER FILE...  (RUNNER is the Rust path of the
`run_tests` function, e.g. `common::run_tests`).

Rewrites `#[tokio::test]` / `#[tokio::test(flavor = "multi_thread", ...)]` to the same
runtime under `#[tokio::main]`, drops `#[test]` (also inside `proptest!`), maps
`#[ignore]` to an ignored trial and appends the new trials to an existing `fn main`
list, or adds one. `--check FILE...` only reports test attributes left in FILEs.
"""
import re
import sys

ATTR = re.compile(r'^(\s*)#\[(tokio::test(?:\((.*)\))?|test)\]\s*$')
FN = re.compile(r'^\s*(?:pub\s+)?(?:async\s+)?fn\s+([A-Za-z0-9_]+)')
HEADER = ('// Every test is listed in `main`; an unlisted one is dead code, so this refuses it.\n'
          '#![deny(dead_code)]')


def convert(path, runner):
    lines = open(path).read().split('\n')
    out, trials, pending_ignore = [], [], False
    i = 0
    while i < len(lines):
        line = lines[i]
        m = ATTR.match(line)
        if not m:
            out.append(line)
            i += 1
            continue
        indent, attr, args = m.group(1), m.group(2), m.group(3)
        if attr.startswith('tokio::test'):
            args = args or 'flavor = "current_thread"'
            out.append(f'{indent}#[tokio::main({args})]')
        ignored = False
        j = i + 1
        while j < len(lines) and not FN.match(lines[j]):
            if re.match(r'^\s*#\[ignore', lines[j]):
                ignored = True
                j += 1
                continue
            out.append(lines[j])
            j += 1
        trials.append((FN.match(lines[j]).group(1), ignored))
        i = j
    text = '\n'.join(out)
    trials = [(n, ign) for n, ign in trials if f'Trial::test("{n}"' not in text]
    if not trials:
        return 0
    entries = ''.join(
        f'        libtest_mimic::Trial::test("{n}", || {{ {n}(); Ok(()) }})'
        + ('.with_ignored_flag(true)' if ign else '') + ',\n'
        for n, ign in trials)
    call = f'{runner}(vec!['
    if call in text:
        start = text.index(call)
        end = text.index('    ]);', start)
        text = text[:end] + entries + text[end:]
    else:
        if '#![deny(dead_code)]' not in text:
            body = text.split('\n')
            k = 0
            while k < len(body) and body[k].startswith('//!'):
                k += 1
            body.insert(k, HEADER)
            text = '\n'.join(body)
        text = text.rstrip('\n') + (
            '\n\n// Own the process lifetime: stop FDB only after every test runtime has dropped.\n'
            f'fn main() {{\n    {call}\n{entries}    ]);\n}}\n')
    open(path, 'w').write(text)
    return len(trials)


def check(paths):
    bad = 0
    for p in paths:
        for n, line in enumerate(open(p), 1):
            if ATTR.match(line):
                print(f'{p}:{n}: test attribute in an explicit-harness suite (never runs)')
                bad += 1
    return bad


if __name__ == '__main__':
    if sys.argv[1] == '--check':
        sys.exit(1 if check(sys.argv[2:]) else 0)
    runner = sys.argv[1]
    for p in sys.argv[2:]:
        print(f'{p}: {convert(p, runner)} trials added')
