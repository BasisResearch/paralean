#!/usr/bin/env python3
"""Fixed proof producer; no model calls and no artificial sleeps."""
import json
import os
from pathlib import Path
import subprocess
import time


def body(name, work=0):
    if name == 'P5List.map_length':
        return '  intro α β f xs\n  exact List.length_map f\n'
    if name.startswith('P5List.reverse_map_len_'):
        k = name.rsplit('_', 1)[1]
        return f'  intro xs\n  exact (P5List.map_length Nat Nat (fun n => n + {k}) xs.reverse).trans (List.length_reverse (as := xs))\n'
    if name == 'P5List.reverse_map_lengths':
        return '  intro xs\n  exact ⟨' + ', '.join(f'P5List.reverse_map_len_{i} xs' for i in range(1, 9)) + '⟩\n'
    if name == 'P5.add_comm_general':
        return '  exact Nat.add_comm\n'
    if name == 'P5.add_comm_up_to_eight':
        return '  intro n\n  exact ⟨' + ', '.join(f'P5.add_comm_{i} n' for i in range(1, 9)) + '⟩\n'
    k = name.rsplit('_', 1)[1]
    return (f'  run_tac\n    for _ in [:{work}] do\n'
            '      Lean.Elab.Tactic.evalTactic (← `(tactic| have hscal : (1 : Nat) + 1 = 2 := by decide))\n'
            '      Lean.Elab.Tactic.evalTactic (← `(tactic| clear hscal))\n'
            f'  intro n\n  exact P5.add_comm_general n {k}\n')


def declaration(name, statement, work=0):
    return f'\ntheorem {name} : {statement} := by\n' + body(name, work)


if __name__ == '__main__':
    started = time.monotonic()
    directory = Path(os.environ['PARALEAN_P5_WORKSPACE'])
    path = directory / 'work' / os.environ['PARALEAN_P5_FILE']
    with path.open('a') as out:
        out.write(declaration(os.environ['PARALEAN_P5_TARGET'], os.environ['PARALEAN_P5_STATEMENT'], int(os.environ.get('SCALING_WORK', '2000'))))
    result = subprocess.run([os.environ['PARALEAN_BIN'], 'ws-check', '--dir', str(directory), os.environ['PARALEAN_P5_FILE']], check=True, capture_output=True, text=True)
    print(result.stdout, end='')
    verdict = json.loads(result.stdout.strip().splitlines()[-1])
    if verdict.get('errors'): raise RuntimeError('scripted proof failed ws-check')
    if os.environ.get('SCALING_PHASES'):
        with open(os.environ['SCALING_PHASES'], 'a') as f:
            f.write(json.dumps({'phase':'scripted_worker', 'start':started, 'wall_s':time.monotonic()-started,
                                'target':os.environ['PARALEAN_P5_TARGET'], 'ok':True})+'\n')
