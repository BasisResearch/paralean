#!/usr/bin/env python3
"""Load-gated scaling runner. No secrets or full environments are archived."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import tomllib
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'impl/p5/scripts'))
from benchmark import workspace_transfer
from worker import declaration
ROOT = Path(__file__).resolve().parents[2]
RAW = ROOT / 'results/scaling'
RUN = ROOT / '.runs/scaling'


def load_gate():
    while os.getloadavg()[0] > 24:
        print('waiting for load <24:', os.getloadavg(), flush=True)
        time.sleep(30)


def service_cpu():
    result = {}
    for p in (RUN/'cluster/run').glob('*.pid'):
        try:
            pid = int(p.read_text())
            stat = Path(f'/proc/{pid}/stat').read_text().split(') ',1)[1].split()
            result[p.stem] = (int(stat[11])+int(stat[12]))/os.sysconf('SC_CLK_TCK')
        except (OSError, ValueError):
            pass
    return result


def command(cmd, log, env):
    load_gate()
    services0 = service_cpu()
    cpu0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    load = os.getloadavg()
    start = time.monotonic()
    with log.open('w') as f:
        p = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT, env=env)
    cpu1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {'command': cmd, 'returncode': p.returncode, 'wall_s': time.monotonic()-start,
            'cpu_s': cpu1.ru_utime+cpu1.ru_stime-cpu0.ru_utime-cpu0.ru_stime,
            'load_start': load, 'load_end': os.getloadavg(),
            'service_cpu_s': {k:v-services0.get(k,v) for k,v in service_cpu().items()}}


def trial(workload, n, rep, stock=False, sync=False, pilot=False, work=2000, agent=False):
    name = f'{"pilot" if pilot else "main"}-{workload}-{"stock-sync" if sync else "stock" if stock else "p"+str(n)}-r{rep}'
    if agent: name = 'confirm-agent-' + name
    evidence = RAW / name
    evidence.mkdir(parents=True, exist_ok=False)
    directory = RUN / name
    directory.mkdir(parents=True, exist_ok=False)
    template = ROOT / 'impl/p5/tasks' / ('list_reverse_map_lengths.toml' if workload == 'list' else 'add_comm_eight.toml')
    text = template.read_text().replace('kind = "codex"', 'kind = "command"\ncommand = '+json.dumps([sys.executable, str(ROOT/'scripts/scaling/worker.py')]))
    taskdata = tomllib.loads(text)
    text = text.replace('id = "'+taskdata['task']['id']+'"', 'id = "scal-'+name+'"')
    text = text.replace('max_attempts = 3', 'max_attempts = 1')
    text = text.replace('kind = "command"', 'kind = "command"\ntimeout_s = 180')
    if workload == 'synthetic':
        text += '\n[sources]\n' + '\n'.join(json.dumps(t['file'])+' = "import Lean\\n"' for t in taskdata['targets'])+'\n'
    task = evidence / 'task.toml'
    task.write_text(text)
    env = dict(os.environ, SCALING_WORK=str(work), PARALEAN_DEPLOYMENT='scal-'+name,
               SCALING_PHASES=str(evidence/'phases.jsonl'), PARALEAN_SCALING_PROFILE='1')
    row = {'name': name, 'workload': workload, 'n': n, 'rep': rep, 'stock': stock,
           'sync': sync, 'work': work, 'agent': agent, 'git': subprocess.check_output(['git','rev-parse','HEAD'], text=True).strip(),
           'task_sha256': hashlib.sha256(text.encode()).hexdigest(),
           'started_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
    if stock:
        source = ('import Lean\n' if workload == 'synthetic' else 'import Init\n') + ('set_option Elab.async false\n' if sync else '')
        source += ''.join(declaration(t['name'],t['statement'],work) for t in taskdata['targets'])
        path = evidence/'Stock.lean'
        path.write_text(source)
        lean = str(Path(env['PARALEAN_STOCK_LAKE']).with_name('lean'))
        row.update(command([lean, str(path)], evidence/'stock.log', env))
        row['ok'] = row['returncode'] == 0
    else:
        cmd = [sys.executable, str(ROOT/'scripts/scaling/controller.py'), 'run', str(task), '--state', str(directory), '--workers', str(n), '--parallelism', str(n), '--worker', 'claude' if agent else 'command', '--no-export']
        row.update(command(cmd, evidence/'controller.log', env))
        statepath = directory/'run.json'
        state = json.loads(statepath.read_text()) if statepath.exists() else {}
        # run.json contains no private signing keys; retain exact contracts/events.
        (evidence/'run.json').write_text(json.dumps(state,indent=2)+'\n')
        row['ok'] = row['returncode'] == 0 and state.get('phase') == 'targets_validated' and state.get('contract_validation',{}).get('ok') is True
        row['metrics'] = state.get('metrics',{})
        row['transfer'] = workspace_transfer(directory)
        vl = directory/'validator.log'
        if vl.exists():
            (evidence/'validator.log').write_bytes(vl.read_bytes())
        for logname in ('backend.log',):
            p = directory/logname
            if p.exists(): (evidence/logname).write_bytes(p.read_bytes())
        for p in directory.glob('w*/remote.log'):
            (evidence/(p.parent.name+'-remote.jsonl')).write_bytes(p.read_bytes())
        # The representative pilot includes clean export, separately timed.
        if pilot and row['ok']:
            exportcmd = [sys.executable, str(ROOT/'scripts/scaling/controller.py'), 'export', state.get('task_id',''), '--state', str(directory), '--out', str(directory/'export')]
            row['export'] = command(exportcmd, evidence/'export.log', env)
    (evidence/'result.json').write_text(json.dumps(row,indent=2)+'\n')
    print(json.dumps(row), flush=True)
    return row


if __name__ == '__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--pilot',action='store_true')
    ap.add_argument('--confirm',action='store_true')
    ap.add_argument('--workload',choices=['list','synthetic'],default='list')
    ap.add_argument('--work',type=int,default=2000)
    ap.add_argument('--n',type=int,default=1)
    args=ap.parse_args()
    if args.confirm:
        trial('list',2,1,agent=True)
    elif args.pilot:
        trial(args.workload,args.n,0,pilot=True,work=args.work)
    else:
        for rep in range(1,4):
            for workload in ('list','synthetic'):
                configs=[('stock',1),('sync',1),('p',1),('p',2),('p',4),('p',8)]
                if rep==2: configs.reverse()
                for kind,n in configs:
                    trial(workload,n,rep,stock=kind!='p',sync=kind=='sync',work=args.work)
