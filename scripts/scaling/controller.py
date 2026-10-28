#!/usr/bin/env python3
"""P5 entry point with opt-in phase timing, leaving scheduling unchanged."""
import functools
import json
import os
from pathlib import Path
import sys
import time
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'impl/p5'))
from p5lib.backend import Backend

out = Path(os.environ['SCALING_PHASES'])
for name in ('setup', 'provision', 'sync', 'assign_target', 'observe_target', 'publish',
             'validate', 'save_state', 'export', '_run', '_ws'):
    original = getattr(Backend, name)
    def instrument(fn, label):
        @functools.wraps(fn)
        def timed(*args, **kwargs):
            start = time.monotonic()
            ok = False
            try:
                result = fn(*args, **kwargs)
                ok = True
                return result
            finally:
                row = {'phase': label, 'start': start, 'wall_s': time.monotonic()-start, 'ok': ok}
                if label == '_run':
                    row['operation'] = Path(args[1][0]).name + ' ' + (args[1][1] if len(args[1]) > 1 else '')
                if label == '_ws':
                    row['operation'] = args[1]
                with out.open('a') as f:
                    f.write(json.dumps(row)+'\n')
        return timed
    setattr(Backend, name, instrument(original, name))
import p5lib.workers as workers
workers.run = instrument(workers.run, "worker_cli")
import runpy
runpy.run_path(str(Path(__file__).resolve().parents[2] / 'impl/p5/paralean.py'), run_name='__main__')
