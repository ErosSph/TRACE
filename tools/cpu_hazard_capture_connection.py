"""Connect an original-LFP hazard certificate to actual invalid-slot capture."""
import argparse,json,hashlib,time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage


def checked(directory,file,ast_sha):
    directory=Path(directory)
    report=json.loads((directory/'report.json').read_text())
    plan=json.loads((directory/'plan.json').read_text())
    if not(report.get('accepted') is True and report.get('coqc_exit')==report.get('coqchk_exit')==0 and
        report.get('assumptions_closed') is True and plan['ast_sha256']==ast_sha and
        hashlib.sha256((directory/(file+'.v')).read_bytes()).hexdigest()==report['source_sha256'] and
        (directory/(file+'.vo')).is_file()):
        raise ValueError('unchanged checked same-configuration provider required')
    return plan


def check(ast,module,hazard,valid,output):
    raw,profile,paths=origin.raw_binding(ast,module)
    hp=checked(hazard,'GuardedClear',raw['source_sha256'])
    vp=checked(valid,'ValidGate',raw['source_sha256'])
    if hp['root']!=vp['control']['terminal']:raise ValueError('hazard/valid control mismatch')
    p=profile['ast']['program'];am=raw['module'];root=vp['valid'];proc=vp['process']
    source=f'''From Coq Require Import ZArith.
Require Import {module} Lang.ExtendedSV
 GeneratedGuardedClear.GuardedClear GeneratedValidGate.ValidGate.
Import ExtendedSV.
Module G:=GeneratedGuardedClear.GuardedClear.
Module V:=GeneratedValidGate.ValidGate.
Theorem actual_hazard_blocks_valid seed ev pre:
 CombLFP {p} seed(phase_driven_state {p} ev pre) ->changed_signal ev<>{root}%nat ->
 process_matches_states pre(phase_driven_state {p} ev pre){am}.{proc}=true ->
 norm 1(eval_expr(phase_driven_state {p} ev pre)G.guard)<>0%Z ->
 norm 1(read_signal(PhaseSemantics {p} ev pre){root})=0%Z.
Proof. intros HL HE HM HH.
 exact(V.blocked_actual_capture seed ev pre HL HE HM(G.actual_lfp_guard_clears seed _ HL HH)). Qed.
Print Assumptions actual_hazard_blocks_valid.
'''
    out=Path(output);out.mkdir(parents=True,exist_ok=False);file=out/'HazardCapture.v';file.write_text(source)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for path in paths:flags+=['-R',path['directory'],path['namespace']]
    flags+=['-R',str(Path(hazard).resolve()),'GeneratedGuardedClear','-R',str(Path(valid).resolve()),'GeneratedValidGate',
            '-R',str(out.resolve()),'GeneratedHazardCapture']
    start=time.monotonic()
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],complete_R_generated=False,operand_freshness_proved=False,
        actual_rtl_hazard_blocks_valid_proved=False)
    if c.returncode==0 and time.monotonic()-start<1200:
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedHazardCapture.HazardCapture'],out/'coqchk.log',1200-(time.monotonic()-start))
        closed=c.stdout.count('Closed under the global context')==1 and 'Axioms:'not in c.stdout
        report.update(coqchk_exit=k.returncode,assumptions_closed=closed,accepted=closed and k.returncode==0,
                      actual_rtl_hazard_blocks_valid_proved=closed and k.returncode==0)
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','hazard','valid','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.hazard,a.valid,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
