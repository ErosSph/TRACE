"""Consume an invalid-fetch bubble to discharge real controller conditions.

Recognize controller input fields by their graph/AST dependency on the paired
captured word/valid state, not by their names. Remaining inputs are kept open.
Every substitution and the whole blocking-process observation is Coq checked.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_cdfg_invalid_fetch as invalid
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage


def discover(c,raw,profile,graph):
    plan=invalid.discover(c,raw,profile,graph);pc=invalid.fetch.pc
    root=plan['chains']['enable']['terminal'];proc=plan['flush_process']
    _,_,report=invalid.fetch.obs.render(c['ast'],c['ast_module'],proc,root,1)
    known={(32,plan['pair']['carrier']),(1,plan['pair']['valid_root'])}
    symbols=pc.unique_symbols(graph);fields=[];open_inputs=[]
    for width,signal in report['dependencies']:
        cone=pc.admission.fetch.cdfg.cone.cone(raw,width,signal)
        query=pc.admission.fetch.cdfg.backward_slice(graph,symbols[signal]['path'])
        if (not cone['nodes']or not cone['boundaries'] or
                any((b['width'],b['root'])not in known or b['reason']!='sequential'for b in cone['boundaries'])):
            open_inputs.append(dict(width=width,root=signal,cone=cone,query=query));continue
        pc.admission.fetch.cdfg.agree(graph,query,cone)
        fields.append(dict(width=width,root=signal,cone=cone,query=query))
    if not fields:raise ValueError('no controller input fields depend on the paired capture')
    query=pc.admission.fetch.cdfg.backward_slice(graph,symbols[root]['path'])
    body=next(p['body']for p in raw['processes']if p['name']==proc)
    direct_guards=sorted({int(n.args[0].args[1].name)for n in pc.rtl.walk(body)
        if n.name=='SIf'and n.args[0].name=='EVar'and n.args[0].args[0].name=='1'})
    plan.update(enable_process=proc,enable_root=root,enable_observation=report,fields=fields,
        open_controller_inputs=open_inputs,enable_query=query,direct_boolean_guards=direct_guards)
    return plan


def render(c,raw,profile,plan):
    pc=invalid.fetch.pc;p,am=profile['ast']['program'],raw['module'];pair=plan['pair']
    text,_,report=invalid.fetch.obs.render(c['ast'],c['ast_module'],plan['enable_process'],plan['enable_root'],1)
    source='Module Enable.\n'+text+'\nEnd Enable.\n'
    for i,row in enumerate(plan['fields']):
        cone=pc.admission.fetch.cdfg.cone.render(c['ast'],c['ast_module'],raw,profile,row['cone'])
        source+=f'Module Field{i}.\n'+cone+f'\nEnd Field{i}.\n'
    source+=f'''From Coq Require Import List ZArith Bool.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVProjectionConnection Lang.ExtendedSVExpressionFold Lang.ExtendedSVExpressionBinding
 GeneratedPCControl.PCControl GeneratedFetchAdmission.FetchAdmission.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVProjectionConnection ExtendedSVExpressionFold ExtendedSVExpressionBinding.
Local Open Scope Z_scope.
Local Opaque {p} PhaseSemantics.
Definition captured_bindings:list Binding:=[
 {{|binding_width:=32;binding_root:={pair['carrier']}%nat;binding_expr:=EConst 32 {plan['bubble']}|}};
 {{|binding_width:=1;binding_root:={pair['valid_root']}%nat;binding_expr:=EConst 1 0|}}].
Lemma captured_agree fixed:
 norm 32(read_signal fixed {pair['carrier']}%nat)=norm 32 {plan['bubble']} ->
 norm 1(read_signal fixed {pair['valid_root']}%nat)=0 ->BindingsAgree fixed captured_bindings.
Proof. intros HW HV;constructor;[cbn[binding_width binding_root binding_expr eval_expr];rewrite norm_idempotent;exact HW|].
 constructor;[exact HV|constructor]. Qed.
'''
    for i,row in enumerate(plan['fields']):
        w,r=row['width'],row['root'];e=f'Field{i}.cone_{r}'
        source+=f'''Definition field_{i}_value:Z:=Eval vm_compute in eval_expr(write_signal(write_signal [] {pair['carrier']}%nat {plan['bubble']}){pair['valid_root']}%nat 0){e}.
Definition field_{i}_specialized:=fold_expression(substitute(lookup_binding captured_bindings){e}).
Lemma field_{i}_checked:field_{i}_specialized=EConst {w} field_{i}_value.
Proof. vm_compute;reflexivity. Qed.
Theorem field_{i}_actual seed fixed:CombLFP {p} seed fixed ->
 norm 32(read_signal fixed {pair['carrier']}%nat)=norm 32 {plan['bubble']} ->
 norm 1(read_signal fixed {pair['valid_root']}%nat)=0 ->
 norm {w}(read_signal fixed {r}%nat)=norm {w} field_{i}_value.
Proof. intros HL HW HV;rewrite(Field{i}.cone_{r}_actual seed fixed HL).
 pose proof(bindings_substitute_sound captured_bindings {e} fixed(captured_agree fixed HW HV))as HS.
 rewrite <-HS,<-(fold_expression_sound(substitute(lookup_binding captured_bindings){e})fixed).
 change(norm {w}(eval_expr fixed field_{i}_specialized)=norm {w} field_{i}_value).
 rewrite field_{i}_checked;cbn[eval_expr];apply norm_idempotent. Qed.
'''
    entries=[f'{{|binding_width:={row["width"]};binding_root:={row["root"]}%nat;binding_expr:=EConst {row["width"]} field_{i}_value|}}'
        for i,row in enumerate(plan['fields'])]
    source+='Definition field_bindings:list Binding:=['+';'.join(entries)+'].\n'
    source+=f'''Lemma fields_agree seed fixed:CombLFP {p} seed fixed ->
 norm 32(read_signal fixed {pair['carrier']}%nat)=norm 32 {plan['bubble']} ->
 norm 1(read_signal fixed {pair['valid_root']}%nat)=0 ->BindingsAgree fixed field_bindings.
Proof. intros HL HW HV;unfold field_bindings.
'''
    for i,row in enumerate(plan['fields']):
        source+=f'constructor;[cbn[binding_width binding_root binding_expr eval_expr];rewrite norm_idempotent;exact(field_{i}_actual seed fixed HL HW HV)|].\n'
    source+='constructor. Qed.\n'
    pcreport=json.loads((Path(c['pc_control'])/'providers.json').read_text())
    oldobs=next(r['directory']for r in pcreport if r['namespace']=='GeneratedBlockingObservation')
    pc_rules=json.loads((Path(oldobs)/'report.json').read_text())['rules']
    # Both existing observations are of this same original blocking controller.
    source+=f'''Definition original_combs:=filter is_comb(processes {p}).
Lemma enable_registered:nth_error original_combs {[p['name']for p in raw['processes']if p['kind']=='Combinational'].index(plan['enable_process'])}%nat=Some {am}.{plan['enable_process']}.
Proof. vm_compute;reflexivity. Qed.
Lemma enable_connected:expression_bindingb original_combs {[p['name']for p in raw['processes']if p['kind']=='Combinational'].index(plan['enable_process'])}%nat {plan['enable_root']}%nat Enable.expr_{report['rules']-1}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_enable_lfp seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {plan['enable_root']}%nat)=norm 1(eval_expr fixed Enable.expr_{report['rules']-1}).
Proof. exact(checked_expression_binding {p} original_combs {[p['name']for p in raw['processes']if p['kind']=='Combinational'].index(plan['enable_process'])}%nat {am}.{plan['enable_process']}
 1 {plan['enable_root']}%nat Enable.expr_{report['rules']-1} seed fixed eq_refl enable_registered Enable.actual_observation enable_connected). Qed.
Definition pc_specialized:=fold_expression(substitute(lookup_binding field_bindings)GeneratedBlockingObservation.Observation.expr_{pc_rules-1}).
Definition flush_specialized:=fold_expression(substitute(lookup_binding field_bindings)GeneratedFetchAdmission.FetchAdmission.Flush.expr_{pc_rules-1}).
Definition enable_specialized:=fold_expression(substitute(lookup_binding field_bindings)Enable.expr_{report['rules']-1}).
Lemma pc_checked:pc_specialized=EConst 2 0.
Proof. vm_compute;reflexivity. Qed.
Lemma flush_checked:flush_specialized=EConst 1 0.
Proof. vm_compute;reflexivity. Qed.
Eval vm_compute in enable_specialized.
Lemma enable_value fixed:norm 1(eval_expr fixed enable_specialized)=1.
Proof. let expression:=eval vm_compute in enable_specialized in change(norm 1(eval_expr fixed expression)=1).
 assert(HZero:norm 1 0=0)by reflexivity.
 assert(HOne:norm 1 1=1)by reflexivity.
 cbn[eval_expr].
'''
    dynamic=[r['root']for r in plan['open_controller_inputs']if r['width']==5]
    for r in dynamic:source+=f'destruct(norm 5(read_signal fixed {r}%nat))eqn:HR{r};\n'
    alternatives=['progress cbn[eval_expr boolz]','progress rewrite norm_idempotent',
        'progress rewrite HZero','progress rewrite HOne']
    alternatives += [f'progress rewrite HR{r}'for r in dynamic]
    alternatives += ['rewrite Z.land_0_l','rewrite Z.land_0_r',
        'match goal with|-context[if ?flag then _ else _]=>destruct flag eqn:? end']
    source+='repeat first['+'|'.join(alternatives)+'];try congruence;try discriminate;reflexivity. Qed.\n'
    for name,w,root,expr,theorem in [
        ('pcsource',2,plan['pc_plan']['chains']['select']['terminal'],f'GeneratedBlockingObservation.Observation.expr_{pc_rules-1}','GeneratedBlockingConnection.Connection.actual_lfp_observation'),
        ('flush',1,plan['flush_root'],f'GeneratedFetchAdmission.FetchAdmission.Flush.expr_{pc_rules-1}','GeneratedFetchAdmission.FetchAdmission.actual_flush_lfp'),
        ('enable',1,plan['enable_root'],f'Enable.expr_{report["rules"]-1}','actual_enable_lfp')]:
        expected=1 if name=='enable'else 0
        special='pc'if name=='pcsource'else name
        source+=f'''Theorem actual_bubble_{name} seed fixed:CombLFP {p} seed fixed ->
 norm 32(read_signal fixed {pair['carrier']}%nat)=norm 32 {plan['bubble']} ->
 norm 1(read_signal fixed {pair['valid_root']}%nat)=0 ->norm {w}(read_signal fixed {root}%nat)={expected}.
Proof. intros HL HW HV;rewrite({theorem} seed fixed HL).
 pose proof(bindings_substitute_sound field_bindings {expr} fixed(fields_agree seed fixed HL HW HV))as HS.
 rewrite <-HS,<-(fold_expression_sound(substitute(lookup_binding field_bindings){expr})fixed).
 change(norm {w}(eval_expr fixed {special}_specialized)={expected}).
'''
        source+=('apply enable_value. Qed.\n'if name=='enable'else f'rewrite {special}_checked;reflexivity. Qed.\n')
    source+='Goal True. idtac "BUBBLE_CONTROL_AUDIT". exact I. Qed.\n'
    exports=['actual_enable_lfp','pc_checked','flush_checked','enable_value','actual_bubble_pcsource','actual_bubble_flush','actual_bubble_enable']
    source+=''.join(f'Print Assumptions {target}.\n'for target in exports)
    return source,len(exports)


def check(c,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);pc=invalid.fetch.pc
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module']);plan=discover(c,raw,profile,graph)
    paths=checked_provider(c['normal_write'],'NormalWrite.v',raw['source_sha256'],['all_normal_ADD_RF_phase_branches_proved'])
    paths +=[dict(namespace='GeneratedNormalWrite',directory=str(Path(c['normal_write']).resolve()))]
    source,count=render(c,raw,profile,plan);file=out/'BubbleControl.v';file.write_text(source)
    for name,data in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedBubbleControl'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqc'),
        '-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        invalid_payload_implies_pcsource_flush_enable_proved=False,caller_controller_conditions_required=False,
        full_R_generated=False,full_cycle_preservation_proved=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('BUBBLE_CONTROL_AUDIT')[-1];closed=audit.count('Closed under the global context')==count and'Axioms:'not in audit
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),str(pc.rtl.ROOT/'_opam/bin/coqchk'),
            '-silent',*flags,'-norec','GeneratedBubbleControl.BubbleControl'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=closed and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,assumptions_closed=closed,
            invalid_payload_implies_pcsource_flush_enable_proved=ok)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.output)
    except Exception as exc:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
