#!/usr/bin/env bash
set -euo pipefail
source scripts/scaling/env.sh
# Start is idempotent and checks ownership; services remain owned even if a trial fails.
impl/p5/scripts/cluster-up.sh > .runs/scaling/suite-cluster-up.log 2>&1
trap 'impl/p5/scripts/cluster-down.sh > .runs/scaling/cluster-down.log 2>&1' EXIT
python3 - <<'PY'
import sys
sys.path.insert(0,'scripts/scaling')
from study import trial
assert trial('synthetic',8,2,pilot=True,work=100)['ok']
PY
# Require the heavier pilot and its clean export to pass before production sampling.
python3 - <<'PY'
import json
p=json.load(open('results/scaling/pilot-synthetic-p8-r2/result.json'))
assert p['ok'] and p['export']['returncode']==0, p
PY
python3 scripts/scaling/profile.py > .runs/scaling/profile-launch.log 2>&1
python3 scripts/scaling/study.py --work 100 > .runs/scaling/main-launch.jsonl 2>&1
python3 scripts/scaling/study.py --confirm > .runs/scaling/confirm-launch.jsonl 2>&1
