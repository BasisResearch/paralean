#!/usr/bin/env bash
# Archive verification logs into verification/results.
#
#   bash scripts/archive-verification.sh             # TLC and Lean logs
#   bash scripts/archive-verification.sh --tla-only  # TLC logs only; keep Lean logs
#   bash scripts/archive-verification.sh --verify    # only re-check the archive
#
# TLC logs are archived only from complete suite runs (.runs/tla/MANIFEST and
# .runs/tla/negative/MANIFEST). Every log carries the hashes of the files TLC
# parsed; they are checked against the current sources before archiving:
# positive runs must have checked exactly the current files, and negative runs
# must have been derived from the current files. The archived set is exactly
# the manifest: logs of retired cases are deleted. Larger-scope logs
# (check-tla.sh --wide) are archived in verification/results/tlc/wide only from
# a complete wide run (.runs/tla/wide/MANIFEST); without one that directory is
# removed, so archived logs always match the current sources.
set -euo pipefail
cd "$(dirname "$0")/.."
# shellcheck source=scripts/tla-common.sh
source scripts/tla-common.sh

mode="${1:-all}"
case "$mode" in all|--tla-only|--verify) ;; *) echo "usage: $0 [--tla-only|--verify]" >&2; exit 2;; esac

expected_scenarios() { for entry in "${TLA_SCENARIOS[@]}"; do scenario_name "$entry"; done; }
expected_wide() { for entry in "${TLA_WIDE_SCENARIOS[@]}"; do scenario_name "$entry"; done; }

# Wide logs are positive logs with no negative counterpart.
check_wide() {
  : > "$tmp/noneg"
  check_logs "$1" "$2" - "$tmp/noneg" -
}

# check_logs <positive-log-dir> <positive-names-file> <negative-log-dir> <negative-names-file> <run-dirs?>
check_logs() {
  python3 - "$@" <<'PY'
import hashlib, sys
from pathlib import Path

pos_dir, pos_names, neg_dir, neg_names, rundirs = sys.argv[1:]
src = Path('verification/tla')
current = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
           for p in sorted(src.iterdir()) if p.suffix in ('.tla', '.cfg')}
errors = []

def provenance(log):
    text = log.read_text(errors='replace')
    start = text.rfind('==== Paralean TLC provenance ====')
    end = text.rfind('==== end provenance ====')
    if start < 0 or end < start:
        errors.append(f'{log}: no provenance block')
        return text, None
    block = {'source': {}, 'checked': {}}
    for line in text[start:end].splitlines()[1:]:
        key, _, rest = line.partition(' ')
        if key in ('source', 'checked'):
            digest, name = rest.split(None, 1)
            block[key][name.strip()] = digest
        else:
            block[key] = rest
    return text[:start], block

def check(log, positive, rundir):
    if not log.exists():
        errors.append(f'{log}: missing')
        return
    body, block = provenance(log)
    if block is None:
        return
    module, cfg = block['module'] + '.tla', block['config']
    if module not in block['checked'] or cfg not in block['checked']:
        errors.append(f'{log}: module or config missing from checked files')
    expect = block['expect']
    ok = 'Model checking completed. No error has been found.' in body
    if positive:
        if block['source']:
            errors.append(f'{log}: positive run lists mutation sources')
        if expect != 'pass' or not ok:
            errors.append(f'{log}: positive run did not pass')
        for name, digest in block['checked'].items():
            if current.get(name) != digest:
                errors.append(f'{log}: checked {name} differs from verification/tla/{name}')
        return
    if expect.startswith('failure: '):
        if ok or expect[len('failure: '):] not in body:
            errors.append(f'{log}: expected failure not in log')
    elif expect.startswith('pass: '):
        if not ok:
            errors.append(f'{log}: expected pass not in log')
    else:
        errors.append(f'{log}: unknown expectation {expect!r}')
    if block['source'] != current:
        changed = sorted(set(block['source'].items()) ^ set(current.items()))
        errors.append(f'{log}: derived from different sources: {sorted({n for n, _ in changed})}')
    if rundir != '-':
        case = Path(rundir) / log.stem
        for name, digest in block['checked'].items():
            f = case / name
            if not f.exists() or hashlib.sha256(f.read_bytes()).hexdigest() != digest:
                errors.append(f'{log}: checked {name} differs from {f}')

pos = Path(pos_names).read_text().split()
neg = Path(neg_names).read_text().split()
for name in pos:
    check(Path(pos_dir) / f'{name}.log', True, '-')
for label in neg:
    check(Path(neg_dir) / f'{label}.log', False, rundirs)
if errors:
    print('\n'.join(errors), file=sys.stderr)
    sys.exit(1)
print(f'provenance verified: {len(pos)} positive and {len(neg)} negative TLC logs')
PY
}

tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT

if [[ $mode == --verify ]]; then
  expected_scenarios > "$tmp/pos"
  (cd verification/results/tlc/negative && ls -- *.log | sed 's/\.log$//') > "$tmp/neg"
  check_logs verification/results/tlc "$tmp/pos" verification/results/tlc/negative "$tmp/neg" -
  if [[ -d verification/results/tlc/wide ]]; then
    expected_wide > "$tmp/wide"
    check_wide verification/results/tlc/wide "$tmp/wide"
  fi
  exit 0
fi

# Refuse partial suites.
[[ -f .runs/tla/MANIFEST ]] || { echo "No complete positive TLC run (.runs/tla/MANIFEST)" >&2; exit 1; }
[[ -f .runs/tla/negative/MANIFEST ]] || { echo "No complete negative TLC run (.runs/tla/negative/MANIFEST)" >&2; exit 1; }
expected_scenarios > "$tmp/pos"
if ! cmp -s "$tmp/pos" .runs/tla/MANIFEST; then
  echo "Positive TLC manifest does not match the scenario list" >&2
  exit 1
fi
# The negative run's own log copies live in its case directories.
mkdir -p "$tmp/neglogs"
while IFS= read -r label; do
  cp ".runs/tla/negative/$label/result.log" "$tmp/neglogs/$label.log"
done < .runs/tla/negative/MANIFEST
check_logs .runs/tla .runs/tla/MANIFEST "$tmp/neglogs" .runs/tla/negative/MANIFEST .runs/tla/negative
wide=
if [[ -f .runs/tla/wide/MANIFEST ]]; then
  expected_wide > "$tmp/wide"
  if ! cmp -s "$tmp/wide" .runs/tla/wide/MANIFEST; then
    echo "Wide TLC manifest does not match the wide scenario list" >&2
    exit 1
  fi
  check_wide .runs/tla/wide .runs/tla/wide/MANIFEST
  wide=1
fi

mkdir -p verification/results/tlc/negative verification/results/lean
rm -f verification/results/tlc/*.log verification/results/tlc/negative/*.log
while IFS= read -r scenario; do
  cp ".runs/tla/$scenario.log" "verification/results/tlc/$scenario.log"
done < .runs/tla/MANIFEST
cp "$tmp"/neglogs/*.log verification/results/tlc/negative/
rm -rf verification/results/tlc/wide
if [[ -n $wide ]]; then
  mkdir -p verification/results/tlc/wide
  while IFS= read -r scenario; do
    cp ".runs/tla/wide/$scenario.log" "verification/results/tlc/wide/$scenario.log"
  done < .runs/tla/wide/MANIFEST
else
  echo "No complete wide TLC run (.runs/tla/wide/MANIFEST): wide logs not archived" >&2
fi
{
  echo "host: $(uname -srm)"
  java -version 2>&1
  sha256_files .deps/tla2tools.jar
} > verification/results/tlc/toolchain.txt

if [[ $mode == all ]]; then
  for module in Registry Durability Convergence Composition EndToEnd Commit Groups Delivery DeliveryAlternatives Admission AdmissionExecution Recovery RecoveryAncestry RecoveryAdequacy PublicationDiscovery CompletionRecovery Protocol CompletionRecoveryExecution ProtocolExecution ProtocolGuardChecks LeanNames PublicationReceipts TargetNames CatalogFencing AckCertificates CatalogCertificates Hardened HardenedExecution Workspaces Audit; do
    cp ".runs/veil/$module.log" "verification/results/lean/$module.log"
  done
  {
    java -version 2>&1
    sha256_files .deps/tla2tools.jar
    git -C .deps/veil rev-parse HEAD
    (cd .deps/veil && "$HOME/.elan/bin/lake" env lean --version)
  } > verification/results/toolchain.txt
fi

rg --files verification/tla verification/veil scripts verification/README.md \
  verification/PROTOCOL-OBLIGATIONS.md verification/TLA-GUARDS.md \
  -g '*.lean' -g '*.tla' -g '*.cfg' -g '*.md' -g '*.toml' -g 'lean-toolchain' -g '*.sh' -g '!._*' | LC_ALL=C sort |
  while IFS= read -r file; do sha256_files "$file"; done \
  > verification/results/source-sha256.txt

expected_scenarios > "$tmp/pos"
(cd verification/results/tlc/negative && ls -- *.log | sed 's/\.log$//') > "$tmp/neg"
check_logs verification/results/tlc "$tmp/pos" verification/results/tlc/negative "$tmp/neg" -
if [[ -n $wide ]]; then
  check_wide verification/results/tlc/wide "$tmp/wide"
fi
