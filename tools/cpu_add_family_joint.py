"""Generate one ADD/ADDI current-data relation and actual result phase rule.

Semantic clauses come from original ISA reads/execution; physical bindings come
from the checked ready/read/capture plans. No prior CPU INV is inspected.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_add_derived_sources as derived
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def inputs(base='framework/bzeeno-cdfg-add-inputs.json', addi='framework/bzeeno-cdfg-addi-inputs.json'):
    c=json.loads(Path(base).read_text());c.update(json.loads(Path(addi).read_text()))
    c['addi_result_phase']=c['result_phase']
    return c


def discover(c,raw):
    providers=json.loads((Path(c['derived_sources'])/'providers.json').read_text())
    queue=[r for r in providers if r['namespace']=='GeneratedPhasePendingCommit']
    operands=[r for r in providers if r['namespace']=='GeneratedOperandResultJoint']
    if len(queue)!=1 or len(operands)!=1:raise ValueError('one physical pending/operand provider required')
    qp=json.loads((Path(queue[0]['directory'])/'plan.json').read_text())
    rp=json.loads((Path(c['ready_controls'])/'plan.json').read_text())
    plan=derived.discover(raw,rp,qp,c)
    role={r['field']:r['operand'] for r in plan['ports']}
    if set(role)!={'Rs1','Rs2'}:raise ValueError('ISA source roles must be physically distinguished')
    plan.update(queue_context=queue[0]['directory'],operand_provider=operands[0]['directory'],
        left=role['Rs1'],right=role['Rs2'])
    return plan


def render(c,raw,profile,plan):
    p=profile['ast']['program'];sample=f'(phase_driven_state {p} ev pre)'
    controls=json.loads((Path(c['controls'])/'plan.json').read_text())['rows']
    left,right,valid,bank=plan['left'],plan['right'],plan['head']['valid'],plan['bank']
    source=f'''From Coq Require Import List ZArith.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVCompanionField Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVRegisterBank
 Ex.External.CPUComputedResultCut Ex.External.CPUComputedReferenceCut Ex.External.CPUOriginalISAReference
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects Ex.External.CPUISAAddiEffects
 Ex.External.CPUISAAddFamilyReferenceValues Ex.External.CPUGeneratedJointTemplate Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility
 GeneratedValidResult.ValidResult GeneratedOperandResultJoint.OperandResultJoint
 GeneratedAddiResultPhase.AddiResultPhase GeneratedAddiEvidence.AddiEvidence GeneratedAddControl.AddControl
 GeneratedAddResult.AddResult GeneratedPhasePendingCommit.PhasePendingCommit.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVProjectionOrigin ExtendedSVCompanionField ExtendedSVCaptureBirth ExtendedSVCapturedPending ExtendedSVRegisterBank
 CPUComputedResultCut CPUComputedReferenceCut CPUOriginalISAReference CPUISAInstructionExecution
 CPUISAExecutionEffects CPUISAAddiEffects CPUGeneratedJointTemplate CPURegisterEffectRelation.
Module V:=GeneratedValidResult.ValidResult. Module H:=V.H. Module C:=H.C.
Module O:=GeneratedOperandResultJoint.OperandResultJoint.
Module I:=GeneratedAddiResultPhase.AddiResultPhase. Module A:=GeneratedAddiEvidence.AddiEvidence.
Module AC:=GeneratedAddControl.AddControl. Module AR:=GeneratedAddResult.AddResult.
Module Q:=GeneratedPhasePendingCommit.PhasePendingCommit.
Module F:=CPUISAAddFamilyReferenceValues.
Local Opaque {p} PhaseSemantics.
Theorem sampled_add_controls image events ev token rd rs1 rs2:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 C.C.chain_tag0(snd(H.boot_history image events))=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
'''+ ' /\\\n'.join(f'norm {r["width"]}(read_signal {sample} {r["root"]})=0%Z' for r in controls)+'.\n'
    source+='Proof. intros pre HE HEv HT HD.\n'
    pattern='HC'+str(controls[-1]['root'])
    for row in reversed(controls[:-1]):pattern=f'[HC{row["root"]} {pattern}]'
    source+=f'destruct(AC.actual_stored_add_controls image events token rd rs1 rs2 HE HT HD)as{pattern}.\n'
    for j,row in enumerate(controls):
        r=row['root']
        if j<len(controls)-1:source+='split.\n{ '
        source+=f'''rewrite(sampled_root_preserved {p} ev pre {r} A.G.ControlScalars.root_{r}_comb_frame
 (A.H.protect ev {r} HEv ltac:(simpl;tauto)));exact HC{r}.'''
        source+=' }\n' if j<len(controls)-1 else '\n'
    source+=f'''Qed.
Section ISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.
Definition OperandProjection token pre(before after:FormalSpec.State):Prop:=
 O.OperandProjection token pre before after \/ I.OperandProjection token pre before after.
Definition OperandClause(reference_pc:Token->Z)(initial:FormalSpec.State)ledger pre(packed:C.Packed):Prop:=
 norm 1(read_signal pre {valid})<>0%Z ->forall token,C.C.chain_tag0(snd packed)=Some token ->
 computed_result_R(instruction_effect reference_pc token_word)token_eq_dec
  (OperandProjection token pre)token initial ledger.
Definition ledger(retired:list Token)pre packed:=retired++Q.actual_pending pre packed.
Definition ResultJoint(reference_pc:Token->Z)(initial:FormalSpec.State)ledger pre packed:Prop:=
 V.Joint(F.values reference_pc token_word token_id initial ledger)pre packed.
Record Current(reference_pc:Token->Z)(initial:FormalSpec.State)(retired:list Token)
 (current:FormalSpec.State)(pre:State)(packed:C.Packed):Prop:={{
 current_unique:NoDup(map token_id(ledger retired pre packed));
 current_retired:EffectChain(instruction_effect reference_pc token_word)initial retired current;
 current_RF:RegisterRelated(lane_read 32(read_signal pre {bank}))current;
 current_results:ResultJoint reference_pc initial(ledger retired pre packed)pre packed;
 current_operands:OperandClause reference_pc initial(ledger retired pre packed)pre packed;
 current_pending:exists frontier,EffectChain(instruction_effect reference_pc token_word)
  current(Q.actual_pending pre packed)frontier
}}.
Theorem head_from_operand_clause(reference_pc:Token->Z)initial ledger image events ev:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->NoDup(map token_id ledger) ->
 OperandClause reference_pc initial ledger pre(H.boot_history image events) ->
 V.Head(F.values reference_pc token_word token_id initial ledger)ev pre(H.boot_history image events).
Proof. intros pre HE HEv HN HC HV token HT.
 destruct(proj1(computed_result_R_exact(instruction_effect reference_pc token_word)token_eq_dec
 (OperandProjection token pre)token initial ledger)(HC HV token HT))
 as[index[before[after[HLookup[HStep[HAdd|HAddi]]]]]].
 all:pose proof(lookup_before_sound(instruction_effect reference_pc token_word)token_eq_dec
 token ledger initial index before HLookup)as HBefore.
 all:destruct(A.H.G.sample_evidence image events ev HE HEv)as[seed HL].
 - destruct HAdd as[rd[rs1[rs2[HD HSource]]]].
   destruct(token_execute reference_pc token_word token before after _ HStep HD)as[middle[HEX HEND]].
   destruct(original_add_effect before middle rd rs1 rs2 HEX)as[x[y[HX[HY HREG]]]].
   destruct(HSource x y HX HY)as[HLeft HRight].
   assert(HS1:norm 32(read_signal {sample} {left})=word.unsigned x).
   {{ rewrite(sampled_root_preserved {p} ev pre {left}
     (history_comb_frame _ _ _ _ _ O.O.scalar_{left})(O.protect ev {left} HEv ltac:(simpl;tauto)));exact HLeft. }}
   assert(HS2:norm 32(read_signal {sample} {right})=word.unsigned y).
   {{ rewrite(sampled_root_preserved {p} ev pre {right}
     (history_comb_frame _ _ _ _ _ O.O.scalar_{right})(O.protect ev {right} HEv ltac:(simpl;tauto)));exact HRight. }}
   destruct(sampled_add_controls image events ev token rd rs1 rs2 HE HEv HT HD)as
'''
    pattern='HZ'+str(controls[-1]['root'])
    for row in reversed(controls[:-1]):pattern=f'[HZ{row["root"]} {pattern}]'
    source+=pattern+f'''.
   pose proof(eq_trans(AR.actual_lfp_add seed {sample} _ _ HL
    {' '.join('HZ'+str(r['root']) for r in controls)} HS1 HS2)(AR.unsigned_original_add x y))as HResult.
   rewrite(F.at_cut reference_pc token_word token_id initial ledger index token before HN HBefore),
    (F.computed_add token_word token before rd rs1 rs2 x y HD HX HY).
   exact(f_equal Some(eq_sym HResult)).
 - destruct HAddi as[rd[rs[imm[HD HSource]]]].
   destruct(token_execute reference_pc token_word token before after _ HStep HD)as[middle[HEX HEND]].
   destruct(original_addi_effect before middle rd rs imm HEX)as[x[HX HREG]].
   assert(HS:norm 32(read_signal {sample} {left})=word.unsigned x).
   {{ rewrite(sampled_root_preserved {p} ev pre {left}
     (history_comb_frame _ _ _ _ _ O.O.scalar_{left})(O.protect ev {left} HEv ltac:(simpl;tauto)));exact(HSource x HX). }}
   destruct(I.actual_sampled_addi_inputs image events ev token rd rs imm HE HEv HT HD)as
'''
    pattern='HImm'
    for row in reversed(controls):pattern=f'[HZ{row["root"]} {pattern}]'
    source+=pattern+f'''.
   pose proof(eq_trans(A.actual_lfp_addi seed {sample} _ imm HL
     {' '.join('HZ'+str(r['root']) for r in controls)} HS HImm)(A.unsigned_original_addi x imm))as HResult.
   exact(eq_trans(F.addi_at_cut reference_pc token_word token_id initial ledger index token before
    rd rs imm x HN HBefore HD HX)(f_equal Some(eq_sym HResult))).
Qed.
Theorem actual_result_phase(reference_pc:Token->Z)initial ledger image events ev:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->NoDup(map token_id ledger) ->
 OperandClause reference_pc initial ledger pre(H.boot_history image events) ->
 ResultJoint reference_pc initial ledger pre(H.boot_history image events) ->
 ResultJoint reference_pc initial ledger(PhaseSemantics {p} ev pre)
  (C.advance_capture_fields ev pre(H.boot_history image events)tt).
Proof. intros pre HE HEv HN HO HJ;destruct(A.H.G.sample_evidence image events ev HE HEv)as[seed HL].
 exact(V.phase _ seed ev pre _ HEv HL HJ
 (head_from_operand_clause reference_pc initial ledger image events ev HE HEv HN HO)). Qed.
End ISA.
Goal True. idtac "FAMILY_JOINT_AUDIT". exact I. Qed.
Print Assumptions sampled_add_controls.
Print Assumptions head_from_operand_clause.
Print Assumptions actual_result_phase.
'''
    return source,['sampled_add_controls','head_from_operand_clause','actual_result_phase']


def check(c,output):
    raw,profile,_=derived.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    plan=discover(c,raw);paths=[]
    for key,file,namespace in [
        ('addi_result_phase','AddiResultPhase','GeneratedAddiResultPhase'),
        ('derived_sources','DerivedSources','GeneratedDerivedSources')]:
        verified(c[key],file)
        paths+=json.loads((Path(c[key])/'providers.json').read_text())
        paths.append(dict(namespace=namespace,directory=str(Path(c[key]).resolve())))
    for key,file,ns in [('add_control','AddControl','GeneratedAddControl'),('add_result','AddResult','GeneratedAddResult')]:
        verified(c[key],file);paths.append(dict(namespace=ns,directory=str(Path(c[key]).resolve())))
    paths.append(dict(namespace='GeneratedPhasePendingCommit',directory=plan['queue_context']))
    paths.append(dict(namespace='GeneratedOperandResultJoint',directory=plan['operand_provider']))
    unique={}
    for row in paths:
        if row['namespace'] in unique and unique[row['namespace']]!=row['directory']:
            raise ValueError('conflicting physical family provider')
        unique[row['namespace']]=row['directory']
    paths=[dict(namespace=k,directory=v) for k,v in unique.items()]
    source,exports=render(c,raw,profile,plan)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);path=out/'AddFamilyJoint.v';path.write_text(source)
    for name,data in [('providers',paths),('exports',exports),('plan',plan),('inputs',c)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(derived.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedAddFamilyJoint'];start=time.monotonic()
    root=derived.controls.history.admission.observation.origin.ROOT
    cc,t=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),str(root/'_opam/bin/coqc'),
        '-time',*flags,str(path.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=t,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=raw['source_sha256'],
        old_inv_read=False,complete_R_generated=False,source_clause_preserved=False,exports=exports,
        external_llm_api_calls=0)
    if cc.returncode==0:
        ax=audit_all_exports(cc.stdout.split('FAMILY_JOINT_AUDIT')[-1],len(exports))
        allowed=set(json.loads((Path(c['addi_result_phase'])/'report.json').read_text())['baseline_assumptions'])
        audit=not(ax-allowed)and not(ax-ALLOWED_AXIOMS)
        kk,t=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),str(root/'_opam/bin/coqchk'),
            '-silent',*flags,'-norec','GeneratedAddFamilyJoint.AddFamilyJoint'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(coqchk_exit=kk.returncode,coqchk_timed_out=t,assumptions=sorted(ax),
            baseline_assumptions=sorted(allowed),assumptions_audit_passed=audit,accepted=audit and kk.returncode==0)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True)
    p.add_argument('--base',default='framework/bzeeno-cdfg-add-inputs.json')
    p.add_argument('--addi',default='framework/bzeeno-cdfg-addi-inputs.json')
    a=p.parse_args();r=check(inputs(a.base,a.addi),a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
