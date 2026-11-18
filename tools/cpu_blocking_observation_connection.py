"""Connect a checked, generated blocking observation to the original CombLFP.

The kernel checks process registration and ordering/frame conditions. This is
not an ISA identity theorem and does not import a manually supplied CPU INV.
"""
import argparse, hashlib, json, time
from pathlib import Path
import cpu_blocking_observation as observation
from cpu_certificate_acceptance import run_stage

def verified_input(directory):
    directory=Path(directory)
    report=json.loads((directory/'report.json').read_text())
    if not report.get('accepted') or report.get('coqc_exit')!=0 or report.get('coqchk_exit')!=0:
        raise ValueError('upstream observation has not passed native verification')
    source=(directory/'Observation.v').read_bytes()
    if hashlib.sha256(source).hexdigest()!=report.get('source_sha256'):
        raise ValueError('upstream source changed after verification')
    if not (directory/'Observation.vo').is_file():raise ValueError('missing upstream compiled proof')
    if report.get('old_inv_read') is not False:raise ValueError('not a raw-generated observation')
    return report

def render(ast_path,module,upstream):
    report=verified_input(upstream)
    ast,profile,paths=observation.origin.raw_binding(ast_path,module)
    if ast['source_sha256']!=report['ast_sha256']:raise ValueError('original AST hash mismatch')
    proc=next(p for p in ast['processes'] if p['name']==report['process'])
    if proc['kind']!='Combinational':raise ValueError('not a combinational process')
    # Reproduce generated names from raw input, never infer roles from a CPU INV.
    source,_,fresh=observation.render(ast_path,module,report['process'],report['root'],report['width'])
    if hashlib.sha256(source.encode()).hexdigest()!=report['source_sha256']:
        raise ValueError('generator/source mismatch; regenerate and verify explicitly')
    expr='GeneratedBlockingObservation.Observation.expr_'+str(fresh['rules']-1)
    program=profile['ast']['program'];pn=ast['module']+'.'+proc['name']
    index=[p['name'] for p in ast['processes'] if p['kind']=='Combinational'].index(proc['name'])
    w,r=report['width'],report['root']
    text=f'''From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVExpressionBinding {module}
 GeneratedBlockingObservation.Observation.
Import ListNotations ExtendedSV ExtendedSVExpressionBinding.
Definition original_combs := filter is_comb(processes {program}).
Lemma registered : nth_error original_combs {index} = Some {pn}.
Proof. vm_compute;reflexivity. Qed.
Lemma connected : expression_bindingb original_combs {index} {r} {expr}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_lfp_observation seed fixed : CombLFP {program} seed fixed ->
 norm {w}(read_signal fixed {r})=norm {w}(eval_expr fixed {expr}).
Proof. exact(checked_expression_binding {program} original_combs {index} {pn}
 {w} {r} {expr} seed fixed eq_refl registered
 GeneratedBlockingObservation.Observation.actual_observation connected). Qed.
Print Assumptions actual_lfp_observation.
'''
    return text,paths,dict(process=proc['name'],root=r,width=w,ast_sha256=ast['source_sha256'],
      upstream_source_sha256=report['source_sha256'],upstream=str(Path(upstream).resolve()))

def check(ast_path,module,upstream,output):
    source,paths,report=render(ast_path,module,upstream)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);path=out/'Connection.v';path.write_text(source)
    flags=list(observation.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(Path(upstream).resolve()),'GeneratedBlockingObservation',
      '-R',str(out.resolve()),'GeneratedBlockingConnection']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(observation.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',deadline-time.monotonic())
    report.update(accepted=False,complete_R_generated=False,isa_identity_proved=False,old_inv_read=False,
      coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0:
        k,t=run_stage([str(observation.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedBlockingConnection.Connection'],out/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
          accepted=k.returncode==0 and c.stdout.count('Closed under the global context')==1 and 'Axioms:'not in c.stdout)
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','upstream','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.upstream,a.output),indent=2))
