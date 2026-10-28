#!/usr/bin/env python3
"""Profile already validated List pilot without modifying its source/cache."""
import json
import os
from pathlib import Path
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from study import RAW, RUN, ROOT, command
from worker import declaration
import tomllib
out=RAW/'profile-list'
out.mkdir(exist_ok=True)
state=RUN/'pilot-list-p1-r0'
ws=state/'w0'
env=dict(os.environ,PARALEAN_STORE=str(ws/'cache'),PARALEAN_KEYS=str(ws/'keys.json'),
         PARALEAN_TRUST=str(ws/'trust.json'),PARALEAN_VISIBILITY='1',PARALEAN_DEPLOYMENT='scal-pilot-list-p1-r0',
         PARALEAN_SCALING_PROFILE='1',PARALEAN_REMOTE_LOG=str(out/'remote.log'))
task=tomllib.loads((RAW/'pilot-list-p1-r0/task.toml').read_text())
local=RUN/'profile-list-local'
(local/'work').mkdir(parents=True,exist_ok=True)
(local/'cache/p3/records').mkdir(parents=True,exist_ok=True)
(local/'work/All.lean').write_text('import Init\n'+''.join(declaration(t['name'],t['statement']) for t in task['targets']))
rows=[]
for label,cmd in [
 ('remote',[env['PARALEAN_BIN'],'ws-check','--dir',str(ws),'Final.lean']),
 ('local',[env['PARALEAN_BIN'],'ws-check','--dir',str(local),'All.lean']),
 ('replay',[env['PARALEAN_BIN'],'replay','--store',str(ws/'cache')])]:
 rows.append({'label':label,**command(cmd,out/(label+'.log'),env)})
# Profile the exact validator check-group path using a staged cache with its dependency closure.
caps={json.loads(p.read_text())['gid']:json.loads(p.read_text()) for p in (ws/'cache/meta').glob('*.json')}
if caps:
 root=next((g for g in caps.values() if 'P5List.reverse_map_lengths' in str(g.get('publicNames',[]))),None)
 if root:
  gids=','.join(caps)
  rows.append({'label':'check-group',**command([env['PARALEAN_BIN'],'check-group','--store',str(ws/'cache'),'--gids',gids,'--decl',root['declId']],out/'check-group.log',env)})
(out/'result.json').write_text(json.dumps(rows,indent=2)+'\n')
