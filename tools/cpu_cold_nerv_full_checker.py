#!/usr/bin/env python3
"""Trusted compile broker for newly authored NERV full-stage Coq scripts."""
import argparse,hashlib,json,os,re,resource,signal,subprocess,time,uuid
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];BASE=ROOT/'framework/cold-library-nerv-20261109';FULL=BASE;PUB=FULL/'public';EV=FULL/'evaluator'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def compile_one(cmd,out,tag,env,timeout):
 t=time.time();wrapped=['/usr/bin/time','-f','{"wall_s":%e,"user_s":%U,"system_s":%S,"peak_rss_kib":%M,"exit":%x}','-o',str(out/(tag+'-resources.json'))]+cmd;dump(out/(tag+'-command.json'),wrapped)
 with (out/(tag+'.log')).open('w') as log:
  p=subprocess.Popen(wrapped,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_STACK,(64*1024*1024,resource.getrlimit(resource.RLIMIT_STACK)[1])))
  try:p.communicate(timeout=timeout);status='finished'
  except subprocess.TimeoutExpired:
   children=Path('/proc/'+str(p.pid)+'/task/'+str(p.pid)+'/children')
   for child in children.read_text().split() if children.exists() else []:
    try:os.kill(int(child),signal.SIGTERM)
    except ProcessLookupError:pass
   try:p.communicate(timeout=10)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.communicate()
   status='timeout'
 r={'stack_limit_bytes':64*1024*1024,'started_unix':t,'finished_unix':time.time(),'status':status,'exit_code':p.returncode,'elapsed_s':time.time()-t}
 try:r.update(json.loads((out/(tag+'-resources.json')).read_text().splitlines()[-1]))
 except (ValueError,IndexError,FileNotFoundError):pass
 return r
def check_script(s):
 # Protocol guard only; normal Coq syntax/tactics are otherwise unrestricted.
 plain=re.sub(r'\(\*.*?\*\)',' ',s,flags=re.S)
 forbidden=[r'\b(?:Admitted|admit|Axiom|Axioms|Parameter|Parameters)\b',r'\b(?:Load|Extraction)\b',r'\bDeclare\s+ML\b',r'\bUnset\s+(?:Guard|Positivity|Universe)\s+Checking\b',r'\bbypass_check\b']
 for pat in forbidden:
  if re.search(pat,plain):raise ValueError('Source contains forbidden admission, new axiom, external code, or unsafe typing directive: '+pat)
def main():
 p=argparse.ArgumentParser();sub=p.add_subparsers(dest='cmd',required=True)
 s=sub.add_parser('start');s.add_argument('--author',required=True);s.add_argument('--started-unix',type=float)
 c=sub.add_parser('check');c.add_argument('--session',required=True);c.add_argument('--source',type=Path,required=True);c.add_argument('--helper');c.add_argument('--progress',action='store_true');c.add_argument('--timeout',type=int,default=600)
 a=p.parse_args();EV.mkdir(parents=True,exist_ok=True)
 if a.cmd=='start':
  d=EV/'sessions'/str(uuid.uuid4());d.mkdir(parents=True)
  r={'id':d.name,'author':a.author,'started_unix':a.started_unix or time.time(),'manifest_sha256':sha(PUB/'full-manifest.json'),'plugin_sha256':sha(EV/'cold_full_audit.cmxs'),'coqc_sha256':sha(ROOT/'_opam/bin/coqc'),'status':'open'};dump(d/'session.json',r);print(json.dumps(r));return
 if not re.fullmatch('[a-f0-9-]{36}',a.session):raise ValueError('invalid session')
 d=EV/'sessions'/a.session;r=json.loads((d/'session.json').read_text())
 for k,f in [('manifest_sha256',PUB/'full-manifest.json'),('plugin_sha256',EV/'cold_full_audit.cmxs'),('coqc_sha256',ROOT/'_opam/bin/coqc')]:
  if r[k]!=sha(f):raise ValueError('Frozen evaluator changed: '+k)
 for lib in json.loads((EV/'fixed-full-input-objects.json').read_text()):
  f=Path(lib['object']);f=f if f.is_absolute() else ROOT/f
  if sha(f)!=lib['sha256']:raise ValueError('Fixed original input object changed: '+lib['module'])
 attempts=sorted(d.glob('attempt-*/receipt.json'));number=1
 while True:
  out=d/f'attempt-{number:03d}'
  try:out.mkdir();break
  except FileExistsError:number+=1
 text=a.source.read_text();(out/'authored.v').write_text(text);t=time.time();previous=json.loads(attempts[-1].read_text()) if attempts else None
 receipt={'submitted_unix':t,'audit_plugin_sha256':r['plugin_sha256'],'source_sha256':sha(out/'authored.v'),'source_origin':str(a.source),'source_mtime_unix':a.source.stat().st_mtime,'generation_or_repair_wall_interval_s':t-(previous['finished_unix'] if previous else r['started_unix']),'interval_includes_idle':True,'selftest':r['author'].startswith('evaluator-selftest'),'mode':'progress' if a.progress else ('helper' if a.helper else 'final'),'accepted':False,'full_final_verified':False}
 try:check_script(text)
 except ValueError as e:
  receipt.update(status='rejected_protocol_guard',error=str(e),finished_unix=time.time());dump(out/'receipt.json',receipt);print(json.dumps(receipt));return
 if a.helper and not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.,]*',a.helper):raise ValueError('invalid helper name')
 source='Require Import SeedNervAllOutcome.NervAllOutcome IntegratedNervBootRefinement.NervBootRefinement.\n'+text+'\n'
 if not a.progress:
  if a.helper:source+='Definition cold_checked_final := '+('('+', '.join('@'+x for x in a.helper.split(','))+')' if ',' in a.helper else '@'+a.helper)+'.\n'
  else:source+='Definition cold_checked_final : '+(PUB/'final-target.out').read_text().split(':',1)[1].strip()+' := @cold_nerv_refinement.\n'
 (out/'FullCandidate.v').write_text(source)
 flags=json.loads((EV/'coqc-flags.json').read_text());flags[0]=str(ROOT/flags[0]);flags+=['-time'];flags+=['-Q',str(out),'']
 env=os.environ.copy();env['OCAMLPATH']=str(ROOT/'_opam/lib')
 receipt['compile']=compile_one(flags+[str(out/'FullCandidate.v')],out,'compile',env,a.timeout)
 if receipt['compile']['exit_code']==0 and not a.progress:
  (out/'allowed.txt').write_text('\n'.join(json.loads((PUB/'full-manifest.json').read_text())['allowed_direct_references'])+'\n')
  (out/'Audit.v').write_text('Require Import FullCandidate.\nDeclare ML Module "cold_full_audit:cold.full_audit".\nColdFullAudit.\n')
  env.update(COLD_ALLOWED_REFS=str(out/'allowed.txt'),COLD_AUDIT_OUTPUT=str(out/'audit.json'))
  receipt['audit']=compile_one(flags+['-I',str(EV),str(out/'Audit.v')],out,'audit',env,a.timeout)
  receipt['accepted']=receipt['audit']['exit_code']==0 and (out/'audit.json').exists()
  receipt['full_final_verified']=receipt['accepted'] and not a.helper
 receipt['status']='final_verified' if receipt['full_final_verified'] else ('helper_verified' if receipt['accepted'] else ('progress_compiled' if a.progress and receipt['compile']['exit_code']==0 else 'rejected_compile_or_audit'))
 receipt['finished_unix']=time.time();receipt['object_sha256']=sha(out/'FullCandidate.vo') if (out/'FullCandidate.vo').exists() else None;dump(out/'receipt.json',receipt)
 feedback='\n'.join((out/(tag+'.log')).read_text() for tag in ['compile','audit'] if (out/(tag+'.log')).exists());feedback=re.sub(r'File "[^"]+"','File "<private-evaluator>"',feedback);(out/'public-feedback.txt').write_text(feedback);print(json.dumps(receipt))
if __name__=='__main__':main()
