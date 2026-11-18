"""Generate checked output expressions for whole-scalar blocking case muxes.
No branch is assumed; the default is the prior output when RTL has no default.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage
rtl = origin.pending.rtl


def unwrap(st):
    while st.name == 'SSeq' and len(st.args[0].args)==1:
        st=st.args[0].args[0]
    return st


def case_plan(proc):
    body=unwrap(proc['body'])
    if proc['kind']!='Combinational' or body.name!='SCase':
        return None
    arms=[]; destinations=set()
    for arm in body.args[1].args:
        key, child=arm.args
        child=unwrap(child)
        if child.name!='SAssign' or child.args[0].name!='false' or child.args[2].name!='LVar':
            return None
        _,rhs,lhs=child.args
        destinations.add((int(lhs.args[0].name),int(lhs.args[1].name)))
        arms.append((key,rhs))
    if len(destinations)!=1:return None
    width,root=next(iter(destinations))
    seed=rtl.Term('EVar',(rtl.Term(str(width)),rtl.Term(str(root))))
    return width,root,origin.expressions.case_expression(width,body.args[0],arms,seed)


def render(ast_path,ast_module,process,structural=False):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    proc=next(p for p in ast['processes'] if p['name']==process)
    plan=case_plan(proc)
    if plan is None:raise ValueError('not a whole-scalar blocking case mux')
    width,root,expression=plan
    effect=rtl.effect_of(proc['body']);p=profile['ast']['program'];pn=ast['module']+'.'+process
    combs=[x for x in ast['processes'] if x['kind']=='Combinational'];index=combs.index(proc)
    source=f'''From Coq Require Import ZArith List.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVExpressionBinding
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVAssignment {ast_module}.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVExpressionBinding ExtendedSVWordInvariant ExtendedSVAssignment.
Definition case_effect:EffectPlan:={rtl.render(effect)}.
Definition case_expression:Expr:={rtl.render(expression)}.
Lemma case_compiled:compile_effect(statement_fuel {p})(process_body {pn})=Some case_effect.
Proof. vm_compute. reflexivity. Qed.
Local Opaque eval_expr norm.
Lemma case_local s:norm {width}(read_signal(run_process {p} s {pn}){root})=
 norm {width}(eval_expr s case_expression).
Proof.
 rewrite(checked_effect_run {p} {pn} case_effect case_compiled).
 unfold case_effect,case_expression.
 cbn [eval_effect initial_exec fold_left blocking_state pending_nba apply_nba].
 Local Transparent eval_expr.
 cbn [eval_expr].
 repeat rewrite norm_one_boolz.
 repeat match goal with |- context[Z.eqb ?a ?b] => destruct(Z.eqb a b) eqn:? end;
 cbn [boolz Z.eqb blocking_state pending_nba apply_nba] in *; try discriminate;
 unfold apply_update,resolve_update;
 cbn [resolve_lvalue update_signal update_offset update_width update_value];
 repeat rewrite read_signal_write_same;
 repeat rewrite norm_full_low_write;
 repeat rewrite norm_idempotent;reflexivity.
Qed.
Definition case_combs:=filter is_comb(processes {p}).
Lemma case_registered:nth_error case_combs {index}=Some {pn}.
Proof. vm_compute. reflexivity. Qed.
Lemma case_binding:expression_bindingb case_combs {index} {root} case_expression=true.
Proof. vm_compute. reflexivity. Qed.
Theorem case_actual_lfp seed fixed:CombLFP {p} seed fixed ->
 norm {width}(read_signal fixed {root})=norm {width}(eval_expr fixed case_expression).
Proof. exact(checked_expression_binding {p} case_combs {index} {pn} {width} {root}
 case_expression seed fixed eq_refl case_registered case_local case_binding). Qed.
Print Assumptions case_actual_lfp.
'''
    if structural:
        arms=[]
        for arm in unwrap(proc['body']).args[1].args:
            key,child=arm.args
            arms.append('('+rtl.render(key)+','+rtl.render(unwrap(child).args[1])+')')
        scr=rtl.render(unwrap(proc['body']).args[0])
        metadata=f'''Require Import Lang.ExtendedSVScalarCase.
Import ExtendedSVScalarCase.
Definition scalar_arms:list(option Expr*Expr):=[{';'.join(arms)}].
Lemma case_normalized s:eval_effect case_effect(initial_exec s)=
 eval_effect(FCase {scr}(scalar_case_arms {width} {root} scalar_arms))(initial_exec s).
Proof. reflexivity. Qed.
Lemma case_expression_matches:case_expression=
 scalar_case_expression {width} {scr} scalar_arms(EVar {width} {root}).
Proof. vm_compute. reflexivity. Qed.
'''
        source=source.replace('Lemma case_local s:',metadata+'Lemma case_local s:',1)
        start=source.index('Proof.\n rewrite(checked_effect_run')
        end=source.index('Qed.\nDefinition case_combs',start)
        source=source[:start]+f'''Proof.
 rewrite(checked_effect_run {p} {pn} case_effect case_compiled).
 change(output {width} {root}(eval_effect case_effect(initial_exec s))=
   norm {width}(eval_expr s case_expression)).
 rewrite case_normalized,case_expression_matches.
 apply scalar_case_output.
'''+source[end:]
    return source,paths


def check(ast_path, ast_module, process, output,structural=False,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    source,paths=render(ast_path,ast_module,process,structural)
    path=output/'CaseBinding.v';path.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedCaseBinding']
    report=dict(accepted=False,process=process,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        scope='one actual blocking case output at the original LFP',complete_R_generated=False)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
        output/'coqc.log',deadline-time.monotonic())
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0 and time.monotonic()<deadline:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==1 and 'Axioms:' not in c.stdout
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedCaseBinding.CaseBinding'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
            accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','process','output']:p.add_argument('--'+name,required=True)
    p.add_argument('--check',action='store_true')
    p.add_argument('--structural',action='store_true')
    p.add_argument('--timeout',type=float,default=1200)
    a=p.parse_args()
    if a.check:
        result=check(a.ast,a.ast_module,a.process,a.output,a.structural,a.timeout)
        print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
    source,_=render(a.ast,a.ast_module,a.process,a.structural)
    with Path(a.output).open('x') as f:f.write(source)
