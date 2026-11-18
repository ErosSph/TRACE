"""Linux subreaper resource measurement, following only actual descendants.

Do not use concurrently for multiple subprocesses in one Python process: wait4
reaps every child. Run separate coordinators or one sequential task worker.
"""
import ctypes,os,time,signal,subprocess,json
from pathlib import Path

def run(cmd,cwd,log,timeout,observer=None):
 ctypes.CDLL(None,use_errno=True).prctl(36,1,0,0,0)
 controller_start=time.process_time()
 t=time.monotonic();cpu=0;rss=0;sample_peak=0;reaped=[];expired=False;rootstatus=None
 with open(log,'w') as f:
  p=subprocess.Popen(cmd,cwd=cwd,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  while True:
   if observer is not None:observer(time.monotonic()-t)
   total=0;descendants=set();queue=[]
   def children(pid):
    found=set()
    try:
     for thread in (Path('/proc')/str(pid)/'task').iterdir():
      try:found.update(map(int,(thread/'children').read_text().split()))
      except (OSError,ValueError):pass
    except OSError:pass
    return found
   queue.extend(children(os.getpid()))
   if rootstatus is None:queue.append(p.pid)
   while queue:
    pid_to_read=queue.pop()
    if pid_to_read in descendants:continue
    try:
     fields=(Path('/proc')/str(pid_to_read)/'stat').read_text().rsplit(')',1)[1].split()
     total+=int(fields[21])*os.sysconf('SC_PAGE_SIZE')//1024
     descendants.add(pid_to_read);queue.extend(children(pid_to_read))
    except (OSError,ValueError,IndexError):pass
   sample_peak=max(sample_peak,total)
   while True:
    try:pid,status,u=os.wait4(-1,os.WNOHANG)
    except ChildProcessError:pid=-1;break
    if pid==0:break
    cpu+=u.ru_utime+u.ru_stime;rss=max(rss,u.ru_maxrss);reaped.append(dict(pid=pid,exit=os.waitstatus_to_exitcode(status),cpu_seconds=u.ru_utime+u.ru_stime,peak_rss_kib=u.ru_maxrss))
    if pid==p.pid:rootstatus=os.waitstatus_to_exitcode(status);p.returncode=rootstatus
   if pid==-1:break
   if time.monotonic()-t>=timeout and not expired:
    expired=True
    for target in descendants:
     try:os.kill(target,signal.SIGTERM)
     except ProcessLookupError:pass
   if expired and time.monotonic()-t>=timeout+2:
    for target in descendants:
     try:os.kill(target,signal.SIGKILL)
     except ProcessLookupError:pass
   time.sleep(.05)
 return dict(sampling_controller_cpu_seconds=time.process_time()-controller_start,command=cmd,cwd=str(cwd),wall_seconds=time.monotonic()-t,timeout_seconds=timeout,timed_out=expired,exit=rootstatus,cpu_seconds_including_reaped_descendants=cpu,peak_process_rss_kib=rss,sampled_process_tree_peak_rss_kib=sample_peak,sampling_interval_seconds=.05,reaped=reaped)
