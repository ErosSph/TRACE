"""Discharge the actual PC selector from the original ADD decode.

The blocking observation preserves all statement ordering, including controller
read-after-write. Its expression is specialized only under a proved opcode.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import cpu_cdfg_pc_step as pc
import cpu_blocking_observation_connection as connection
from cpu_certificate_acceptance import run_stage


def discover(c, raw, profile, graph, observation_report):
    p=pc.discover(c,raw,profile,graph)
    root=p['chains']['select']['terminal']
    report=observation_report
    if report['root']!=root or report['width']!=2 or report['ast_sha256']!=raw['source_sha256']:
        raise ValueError('PC selector observation does not match original cone')
    proc=next(x for x in raw['processes']if x['name']==report['process'])
    if root not in proc['writers']or proc['kind']!='Combinational':
        raise ValueError('not the actual combinational PC selector writer')
    selectors={int(n.args[0].args[1].name)for n in pc.rtl.walk(proc['body'])
        if n.name=='SCase'and n.args[0].name=='EVar'and n.args[0].args[0].name=='7'}
    if len(selectors)!=1:
        raise ValueError('ambiguous instruction opcode case; requires another rule')
    opcode=next(iter(selectors));cone=pc.admission.fetch.cdfg.cone.cone(raw,7,opcode)
    by=pc.unique_symbols(graph)
    query=pc.admission.fetch.cdfg.backward_slice(graph,by[opcode]['path'])
    pc.admission.fetch.cdfg.agree(graph,query,cone)
    word=pc.admission.discover(c,raw,profile,graph)['pair']['carrier']
    if cone['boundaries']!=[dict(width=32,root=word,reason='sequential')]:
        raise ValueError('opcode does not come only from the actual captured instruction')
    # Check the field shape, not just its 7-bit output width or signal name.
    node=next((n for n in cone['nodes']if n['expression'].startswith('(ESel 7 ')),None)
    if not node or not node['expression'].endswith('(EConst 5 0))'):
        raise ValueError('not an original RV32 opcode bit field')
    return dict(pc_plan=p,root=root,opcode=opcode,word=word,process=proc['name'],
        opcode_cone=cone,opcode_query=query,ast_sha256=raw['source_sha256'])


def render(c, raw, profile, plan, observation_report):
    opcode,root,word=plan['opcode'],plan['root'],plan['word'];p=profile['ast']['program']
    expr='GeneratedBlockingObservation.Observation.expr_'+str(observation_report['rules']-1)
    cone_source=pc.admission.fetch.cdfg.cone.render(c['ast'],c['ast_module'],raw,profile,plan['opcode_cone'])
    return f'''Require Import {c['ast_module']}.
Module Opcode.
{cone_source}
End Opcode.
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionConnection
 Lang.ExtendedSVExpressionFold Lang.ExtendedSVTwoInputExpression Ex.External.CPUInstructionFields
 Ex.External.CPUISAAddControlFields GeneratedBlockingObservation.Observation GeneratedBlockingConnection.Connection.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVProjectionConnection ExtendedSVExpressionFold
 CPUInstructionFields CPUISAAddControlFields.
Local Open Scope Z_scope.
Definition opcode_binding w x:option Expr:=
 if Nat.eqb w 7 && Nat.eqb x {opcode} then Some(EConst 7 51)else None.
Definition selected_expression:=fold_expression(substitute opcode_binding {expr}).
Lemma selected_expression_checked:selected_expression=EConst 2 0.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_opcode51_pcsource seed fixed:CombLFP {p} seed fixed ->
 norm 7(read_signal fixed {opcode}%nat)=51 ->norm 2(read_signal fixed {root}%nat)=0.
Proof. intros HL HO;rewrite(GeneratedBlockingConnection.Connection.actual_lfp_observation seed fixed HL).
 assert(HS:eval_expr fixed(substitute opcode_binding {expr})=eval_expr fixed {expr}).
 {{ apply substitute_sound;intros w x rhs HB;unfold opcode_binding in HB.
    destruct(Nat.eqb w 7 && Nat.eqb x {opcode})eqn:HC;[|discriminate].
    apply andb_true_iff in HC as[HW HX];apply Nat.eqb_eq in HW,HX;subst w x.
    inversion HB;subst rhs;cbn[eval_expr];change(norm 7(read_signal fixed {opcode}%nat)=51);exact HO. }}
 rewrite <-HS,<-(fold_expression_sound(substitute opcode_binding {expr})fixed).
 change(norm 2(eval_expr fixed selected_expression)=0);rewrite selected_expression_checked;reflexivity. Qed.
Definition word_state code:=write_signal [] {word}%nat code.
Lemma state_word code:read_signal(word_state code){word}%nat=code.
Proof. apply read_signal_write_same. Qed.
Lemma original_ADD_opcode code rd rs1 rs2:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 norm 7(Z.shiftr(norm 32 code)(norm 5 0))=51.
Proof. intro HD;destruct(original_decode_add_fields code rd rs1 rs2 HD)as[HO _].
 pose proof(native_field_reference(word_state code){word}%nat Opcode)as HF.
 unfold field_expr in HF;cbn[field_width field_offset eval_expr]in HF.
 rewrite state_word in HF;repeat rewrite norm_idempotent in HF;rewrite HO in HF;exact HF. Qed.
Theorem actual_original_ADD_pcsource seed fixed code rd rs1 rs2:
 CombLFP {p} seed fixed ->norm 32(read_signal fixed {word}%nat)=norm 32 code ->
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 norm 2(read_signal fixed {root}%nat)=0.
Proof. intros HL HW HD;apply(actual_opcode51_pcsource seed fixed HL).
 pose proof(Opcode.cone_{opcode}_actual seed fixed HL)as HO.
 let expression:=eval cbv in Opcode.cone_{opcode} in
 change(norm 7(read_signal fixed {opcode}%nat)=norm 7(eval_expr fixed expression))in HO.
 cbn[eval_expr]in HO;rewrite HW in HO;repeat rewrite norm_idempotent in HO.
 exact(eq_trans HO(original_ADD_opcode code rd rs1 rs2 HD)). Qed.
Goal True. idtac "PC_CONTROL_AUDIT". exact I. Qed.
Print Assumptions selected_expression_checked.
Print Assumptions actual_opcode51_pcsource.
Print Assumptions original_ADD_opcode.
Print Assumptions actual_original_ADD_pcsource.
'''


def check(c, observation, connected, output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,paths=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module'])
    report=connection.verified_input(observation)
    cp=Path(connected);cr=json.loads((cp/'report.json').read_text())
    expected,_,_=connection.render(c['ast'],c['ast_module'],observation)
    if not(cr.get('accepted')and cr['coqc_exit']==cr['coqchk_exit']==0
            and cr['ast_sha256']==raw['source_sha256']and cr['upstream_source_sha256']==report['source_sha256']
            and(cp/'Connection.v').read_text()==expected and(cp/'Connection.vo').is_file()):
        raise ValueError('same-source checked original LFP controller connection required')
    plan=discover(c,raw,profile,graph,report);text=render(c,raw,profile,plan,report)
    file=out/'PCControl.v';file.write_text(text)
    paths += [dict(directory=str(Path(observation).resolve()),namespace='GeneratedBlockingObservation'),
        dict(directory=str(cp.resolve()),namespace='GeneratedBlockingConnection')]
    for name,value in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedPCControl']
    start=time.monotonic();cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(pc.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,
        source_sha256=hashlib.sha256(text.encode()).hexdigest(),ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        original_ADD_pc_selector_proved=False,pc_write_enable_proved=False,frontier_relation_restored=False,
        full_R_generated=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('PC_CONTROL_AUDIT')[-1];closed=audit.count('Closed under the global context')==4 and 'Axioms:'not in cc.stdout
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(pc.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedPCControl.PCControl'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=closed and kk.returncode==0
        result.update(accepted=ok,assumptions_closed=closed,coqchk_exit=kk.returncode,
            coqchk_timed_out=timed,original_ADD_pc_selector_proved=ok)
    result['seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','observation','connection','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.observation,a.connection,a.output)
    except Exception as exc:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
