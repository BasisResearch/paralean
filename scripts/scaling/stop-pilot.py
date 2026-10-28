"""Stop only the exact synthetic pilot controller and its descendants."""
import os
from pathlib import Path
import signal
import time
root=Path(__file__).resolve().parents[2]
state=str(root/'.runs/scaling/pilot-synthetic-p8-r0')
procs={}
for p in Path('/proc').glob('[0-9]*'):
 try:
  cmd=(p/'cmdline').read_bytes().split(b'\0')
  stat=(p/'stat').read_text().split(') ',1)[1].split()
  procs[int(p.name)]=(int(stat[1]),[a.decode(errors='replace') for a in cmd if a])
 except (OSError,ValueError):pass
controllers=[pid for pid,(_,args) in procs.items() if str(root/'scripts/scaling/controller.py') in args and state in args and 'run' in args]
assert len(controllers)==1,controllers
owned=set(controllers)
while True:
 more={pid for pid,(ppid,_) in procs.items() if ppid in owned}
 if more<=owned:break
 owned|=more
print('Stopping exact owned PIDs:', sorted(owned),flush=True)
for pid in sorted(owned- set(controllers), reverse=True)+controllers:
 try:os.kill(pid,signal.SIGTERM)
 except ProcessLookupError:pass
time.sleep(2)
for pid in owned:
 try:os.kill(pid,signal.SIGKILL)
 except ProcessLookupError:pass
