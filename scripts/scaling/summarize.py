#!/usr/bin/env python3
"""Summaries retain failures; t intervals require three successful samples."""
import json
from pathlib import Path
import re
import statistics
ROOT=Path(__file__).resolve().parents[2]
RAW=ROOT/'results/scaling'
rows=[json.loads(p.read_text()) for p in sorted(RAW.glob('main-*/result.json'))]
summary=[]
for workload in ('list','synthetic'):
 for kind,n in [('stock',1),('stock-sync',1),('p',1),('p',2),('p',4),('p',8)]:
  selected=[r for r in rows if r['workload']==workload and r['n']==n and
            r['stock']==(kind!='p') and (kind=='p' or r['sync']==(kind=='stock-sync'))]
  good=[r for r in selected if r['ok']]
  def stats(key):
   values=[r[key] for r in good]
   if not values:return None
   mean=statistics.mean(values)
   sd=statistics.stdev(values) if len(values)>1 else None
   half=4.302652729911275*sd/len(values)**0.5 if len(values)==3 else None
   return {'samples':values,'mean':mean,'sd':sd,'ci95':[mean-half,mean+half] if half is not None else None}
  item={'workload':workload,'kind':kind,'n':n,'successes':len(good),'attempts':len(selected),
        'wall_s':stats('wall_s'),'cpu_s':stats('cpu_s')}
  if kind=='p' and good:
   item['transfer_bytes_mean']=statistics.mean(r['transfer']['bytes'] for r in good)
   item['validator_rpc_s_mean']=statistics.mean(r['metrics']['check_ms']/1000 for r in good)
   queue=[];fetch=[];checker=[];peaks=[]
   for r in good:
    path=RAW/r['name']
    log=(path/'validator.log').read_text()
    for label,values in [('queue',queue),('fetch',fetch),('checker',checker)]:
     values.append(sum(int(x) for x in re.findall(r'scaling_'+label+r'_us=(\d+)',log))/1e6)
    events=[]
    for line in (path/'phases.jsonl').read_text().splitlines():
     p=json.loads(line)
     if p['phase']=='scripted_worker':
      events.extend([(p['start'],1),(p['start']+p['wall_s'],-1)])
    active=peak=0
    for _,delta in sorted(events):
     active+=delta;peak=max(peak,active)
    peaks.append(peak)
   item.update(queue_s_mean=statistics.mean(queue),fetch_s_mean=statistics.mean(fetch),
               checker_s_mean=statistics.mean(checker),observed_worker_peak=peaks)
  summary.append(item)
for item in summary:
 base=next(x for x in summary if x['workload']==item['workload'] and x['kind']=='stock')
 one=next(x for x in summary if x['workload']==item['workload'] and x['kind']=='p' and x['n']==1)
 for label,b in [('stock_speedup',base),('paralean_speedup',one)]:
  if b['wall_s'] and item['wall_s']:
   a,z=b['wall_s'],item['wall_s'];ci=None
   if a['ci95'] and z['ci95'] and min(a['ci95']+z['ci95'])>0:
    ci=[a['ci95'][0]/z['ci95'][1],a['ci95'][1]/z['ci95'][0]]
   item[label]={'ratio':a['mean']/z['mean'],'endpoint_interval':ci}
result={'method':'Mean; t(2) 95% CI for exactly three successes; conservative endpoint ratios, not a jointly calibrated ratio CI.',
        'summary':summary,'all_successful':len(rows)==36 and all(r['ok'] for r in rows)}
(RAW/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
for r in summary:
 w=r['wall_s'];print(r['workload'],r['kind'],r['n'],r['successes'], '%.3f'%w['mean'] if w else '-',w['ci95'] if w else None)
