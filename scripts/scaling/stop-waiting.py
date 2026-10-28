"""Stop only the owned suite's waiting Python child; let its EXIT trap stop storage."""
from pathlib import Path
import os
import signal
rows={}
for p in Path('/proc').glob('[0-9]*'):
 try:
  args=[x.decode(errors='replace') for x in (p/'cmdline').read_bytes().split(b'\0') if x]
  stat=(p/'stat').read_text().split(') ',1)[1].split()
  rows[int(p.name)]=(int(stat[1]),args)
 except (OSError,ValueError):pass
suites=[pid for pid,(_,a) in rows.items() if a==['bash','scripts/scaling/run.sh']]
assert len(suites)==1,suites
children=[pid for pid,(parent,a) in rows.items() if parent==suites[0] and a[:2]==['python3','-']]
assert len(children)==1,children
# The child is waiting before a measured subprocess: refuse to interrupt a live run.
assert not any(parent==children[0] for parent,_ in rows.values()),'measured child already running'
print('Waiting suite PID',suites[0],'waiting Python PID',children[0],flush=True)
os.kill(children[0],signal.SIGTERM)
