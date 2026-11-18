"""Consume the same ADD/ADDI Current to derive batches and operand capture.

The old generator is a syntax template only: the emitted relation is J.Current,
and no old queue invariant is read or accepted as a premise.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_derived_sources as base
import cpu_add_family_joint as joint
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS, parse_assumptions
from check_reference_value_rules import audit_all_exports


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('unrecognized source template: ' + old[:100])
    return source.replace(old, new)


def render(c, raw, profile, plan, cov):
    source, _ = base.render(c, raw, profile, plan, cov)
    p, am = profile['ast']['program'], raw['module']
    sample = f'(phase_driven_state {p} ev pre)'
    post = f'(PhaseSemantics {p} ev pre)'
    packed = '(Runtime.boot_history image events)'
    q = 'GeneratedPhasePendingCommit.PhasePendingCommit'
    o = 'GeneratedOperandResultJoint.OperandResultJoint'
    v = 'GeneratedValidResult.ValidResult'
    hv = plan['head']['valid']
    process = plan['head']['process']
    source = replace_once(source, 'GeneratedReadyCapture.ReadyCapture GeneratedAdmissionWrite.AdmissionWrite.',
        'GeneratedReadyCapture.ReadyCapture GeneratedAdmissionWrite.AdmissionWrite\n'
        ' GeneratedAddFamilyJoint.AddFamilyJoint GeneratedAddiCapture.AddiCapture\n'
        ' GeneratedAddiReadyControls.AddiReadyControls Ex.External.CPUReferenceAddFamilyProducers\n'
        ' Ex.External.CPUISAAddiEffects Ex.External.CPUISAAddFamilyReferenceValues.')
    source = replace_once(source, 'Module Ref:=CPUReferenceProducerBatches.',
        'Module Ref:=CPUReferenceProducerBatches.\nModule Family:=CPUReferenceAddFamilyProducers.\n'
        'Module J:=GeneratedAddFamilyJoint.AddFamilyJoint.\n'
        'Module AI:=GeneratedAddiReadyControls.AddiReadyControls.\nImport CPUISAAddiEffects.')
    source = replace_once(source, f'{q}.QueueRegisterInv token_pc initial retired current pre packed.',
        'J.Current token_pc initial retired current pre packed.')
    source = source.replace('[[HN[[HC[HR[HCov[HMem HWb]]]]HOp]][frontier HChain]]',
        '[HN HC HR [HCov[HMem HWb]] HOp [frontier HChain]]')
    source = source.replace('CPUISAAddReferenceValues.values', 'CPUISAAddFamilyReferenceValues.values')
    source = source.replace('Ref.AddCompatible', 'Family.FamilyCompatible')
    source = source.replace('Ref.reference_result_add_compatible', 'Family.reference_result_family_compatible')
    source = source.replace('Ref.certify_reference_producers', 'Family.certify_reference_producers')
    source = replace_once(source,
        f'pose proof({o}.head_from_operand_clause token_pc initial(ledger retired pre {packed})image events ev HE HEv HN HOp)as HH.\n exact({v}.Previous.head_from_original_ISA token_pc _ image events ev HE HEv(HH HV)token HT). Qed.',
        f'pose proof(J.head_from_operand_clause token_pc initial(ledger retired pre {packed})image events ev HE HEv HN HOp)as HH.\n exact(HH HV token HT). Qed.')
    for row in plan['rows']:
        i, rd = row['stage'], row['routes']['rd']['input']
        old = f''' - intros token HV HT;pose proof(compatible_{i} token_pc initial retired current image events ev token HE HEv HJ HClock HV HT)as[[rs1[rs2 HD]]HValue].
   destruct(GeneratedReadyControls.ReadyControls.actual_add_sampled_controls_{i} image events ev token _ rs1 rs2 HE HEv HV HT HD)as[HWrite[HLoad HRd]].
'''
        new = f''' - intros token HV HT;pose proof(compatible_{i} token_pc initial retired current image events ev token HE HEv HJ HClock HV HT)as[HDecode HValue].
   assert(HControls:GeneratedReadySelector.ReadySelector.bit {sample}{row['routes']['write']['input']}=true /\\
     GeneratedReadySelector.ReadySelector.bit {sample}{row['routes']['load']['input']}=false /\\
     norm 5(read_signal {sample}{rd})=norm 5(read_signal {sample}{rd})).
   {{ destruct HDecode as[[rs1[rs2 HD]]|[rs[imm HD]]].
      - exact(GeneratedReadyControls.ReadyControls.actual_add_sampled_controls_{i} image events ev token _ rs1 rs2 HE HEv HV HT HD).
      - exact(AI.actual_addi_sampled_controls_{i} image events ev token _ rs imm HE HEv HV HT HD). }}
   destruct HControls as[HWrite[HLoad HRd]].
'''
        source = replace_once(source, old, new)
    # Replace the ADD-only admission proof with two proofs sharing the same R cut.
    start = source.index('Theorem actual_admitted_add_operand_relation')
    stop = source.index('Lemma actual_admitted_tag', start)
    add = source[start:stop]
    add = add.replace(f'{o}.OperandProjection', 'J.OperandProjection')
    add = replace_once(add, '- split;[exact HStep|];exists dest,rs1,rs2;',
        '- split;[exact HStep|];left;exists dest,rs1,rs2;')
    addi = add.replace('actual_admitted_add_operand_relation', 'actual_admitted_addi_operand_relation')
    addi = addi.replace('dest rs1 rs2', 'dest rs imm').replace('dest,rs1,rs2', 'dest,rs,imm').replace('Decode.Add dest rs imm', 'Decode.Addi dest rs imm')
    addi = replace_once(addi,
        'destruct(original_add_effect before middle dest rs imm HExec)as[x[y[HX[HY HEffect]]]].',
        'destruct(original_addi_effect before middle dest rs imm HExec)as[x[HX HEffect]].')
    captures = re.findall(r'pose proof\(GeneratedReadyCapture\.ReadyCapture\.captured_source_add_.*?fold pre in HCaptured\d+\.\n', addi, re.S)
    if len(captures) != 2:
        raise ValueError('exactly two ADD captures required')
    left = next(x for x in plan['ports'] if x['field'] == 'Rs1')
    for old in captures:
        addi = replace_once(addi, old, '')
    capture = f'''pose proof(GeneratedAddiCapture.AddiCapture.captured_source_addi_{left['selector']} token_pc image events ev token dest rs imm
 current(map Ref.batch ps)before x HE HEv HT(protect ev {hv} HEv ltac:(simpl;tauto))HM HV HD HB HR HX
 (HRelated(norm 5(read_signal {sample}{left['source']}))))as HCaptured;fold pre in HCaptured.
'''
    addi = replace_once(addi, 'assert(HLedger:', capture + 'assert(HLedger:')
    tail = addi.index(' - split;[exact HStep|];left;exists dest,rs,imm;')
    addi = addi[:tail] + ''' - split;[exact HStep|];right;exists dest,rs,imm;split;[exact HD|].
   intros x' HX';assert(x'=x)by congruence;subst;exact HCaptured.
Qed.
'''
    source = source[:start] + add + addi + source[stop:]
    phase = source.index('Theorem actual_add_operand_clause_phase')
    source = source[:phase]
    source += f'''Lemma operand_clause_idle token_pc initial ledger image events ev:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Runtime.W.Environment ev ->process_matches_states pre {sample}{am}.{process}=false ->
 J.OperandClause token_pc initial ledger pre {packed} ->
 J.OperandClause token_pc initial ledger {post}(Captured.advance_capture_fields ev pre {packed} tt).
Proof. intros pre HE HP HO HV token HT.
 rewrite(history_phase_projection _ _ _ _ _ Captured.V.root_{hv}_valid_certificate ev pre
 (protect ev {hv} HE ltac:(simpl;tauto))),HP in HV.
 cbn[Captured.advance_capture_fields snd Captured.C.advance_tags Captured.C.chain_tag0]in HT.
 unfold Captured.C.projection_0_origin,projection_phase_origin in HT;rewrite HP in HT.
 destruct(proj1(computed_result_R_exact(instruction_effect token_pc token_word)token_eq_dec
 (J.OperandProjection token pre)token initial ledger)(HO HV token HT))as[index[before[after[HL[HS HProjection]]]]].
 apply(proj2(computed_result_R_exact(instruction_effect token_pc token_word)token_eq_dec
 (J.OperandProjection token {post})token initial ledger)).
 exists index,before,after;split;[exact HL|];split;[exact HS|].
 destruct HProjection as[[rd[rs1[rs2[HD HReads]]]]|[rd[rs[imm[HD HReads]]]]].
 - left;exists rd,rs1,rs2;split;[exact HD|];intros x y HX HY;destruct(HReads x y HX HY)as[HLeft HRight];split.
'''
    for port, proof in zip(sorted(plan['ports'], key=lambda x:x['field']), ['HLeft','HRight']):
        root=port['operand']
        source += f'''   + rewrite(history_phase_projection _ _ _ _ _ {o}.O.scalar_{root} ev pre
 ({o}.protect ev {root} HE ltac:(simpl;tauto))),HP;exact {proof}.
'''
    root=left['operand']
    source += f''' - right;exists rd,rs,imm;split;[exact HD|];intros x HX.
   rewrite(history_phase_projection _ _ _ _ _ {o}.O.scalar_{root} ev pre
   ({o}.protect ev {root} HE ltac:(simpl;tauto))),HP;exact(HReads x HX).
Qed.
Theorem actual_family_operand_clause_phase token_pc initial retired current_state image events ev:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->
  (exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
  (exists rd rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm))) ->
 Current token_pc initial retired current_state pre {packed} ->
 J.OperandClause token_pc initial(ledger retired pre {packed})
 {post}(Captured.advance_capture_fields ev pre {packed} tt).
Proof. intros pre HE HEv HClass HJ.
 destruct(process_matches_states pre {sample}{am}.{process})eqn:HM.
 - intros HV token HT.
   pose proof(actual_admitted_tag ev pre {packed} HEv HM HV)as HTag;rewrite HT in HTag.
   destruct(HClass token(eq_sym HTag))as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].
   + exact(actual_admitted_add_operand_relation token_pc initial retired current_state image events ev token rd rs1 rs2 HE HEv(eq_sym HTag)HM HV HD HJ).
   + exact(actual_admitted_addi_operand_relation token_pc initial retired current_state image events ev token rd rs imm HE HEv(eq_sym HTag)HM HV HD HJ).
 - destruct HJ as[HN HC HR HResult HOp HChain].
   exact(operand_clause_idle token_pc initial(ledger retired pre {packed})image events ev HEv HM HOp).
Qed.
Theorem actual_family_operand_clause_with_new_tokens token_pc initial retired current_state image events ev added:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->
  (exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
  (exists rd rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm))) ->
 Current token_pc initial retired current_state pre {packed} ->
 J.OperandClause token_pc initial(ledger retired pre {packed}++added)
 {post}(Captured.advance_capture_fields ev pre {packed} tt).
Proof. intros pre HE HEv HClass HJ HV token HT;apply Ref.computed_result_append.
 exact(actual_family_operand_clause_phase token_pc initial retired current_state image events ev HE HEv HClass HJ HV token HT).
Qed.
End OriginalISA.
'''
    if 'QueueRegisterInv' in source:
        raise ValueError('old complete relation escaped template replacement')
    exports=[f'{name}_{i}'for i in [0,1]for name in ['reference','compatible']]
    exports += [f'collect_{i}_{name}'for i in [0,1]for name in ['compatible','slots']]
    exports += ['actual_producer_bundle','actual_admitted_add_operand_relation','actual_admitted_addi_operand_relation',
        'actual_admitted_tag','operand_clause_idle','actual_family_operand_clause_phase','actual_family_operand_clause_with_new_tokens']
    source += 'Goal True. idtac "FAMILY_SOURCES_AUDIT". exact I. Qed.\n'
    source += ''.join(f'Print Assumptions {name}.\n' for name in exports)
    return source,exports


def check(c, family, addi_controls, addi_capture, output, optimization_from=None, optimization_spent_from=None):
    for folder,name in [(family,'AddFamilyJoint'),(addi_controls,'AddiReadyControls'),(addi_capture,'AddiCapture')]:
        verified(folder,name)
    raw,profile,_=base.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    for folder in [family,addi_controls,addi_capture]:
        receipt=json.loads((Path(folder)/'plan.json').read_text())
        if receipt.get('ast_sha256')!=raw['source_sha256']:
            raise ValueError('family consumer provider AST mismatch: '+str(folder))
    plan=joint.discover(c,raw)
    paths=json.loads((Path(family)/'providers.json').read_text())
    for folder,ns in [(family,'GeneratedAddFamilyJoint'),(addi_controls,'GeneratedAddiReadyControls'),(addi_capture,'GeneratedAddiCapture')]:
        paths+=json.loads((Path(folder)/'providers.json').read_text())
        paths.append(dict(directory=str(Path(folder).resolve()),namespace=ns))
    unique={}
    for row in paths:
        if row['namespace']in unique and unique[row['namespace']]!=row['directory']:
            raise ValueError('conflicting family sources provider')
        unique[row['namespace']]=row['directory']
    paths=[dict(namespace=k,directory=v)for k,v in unique.items()]
    covpath=next(r['directory']for r in paths if r['namespace']=='GeneratedCoveredCapture')
    cov=json.loads((Path(covpath)/'plan.json').read_text())
    source,exports=render(c,raw,profile,plan,cov)
    normalization=None
    if optimization_from:
        prior=Path(optimization_from)
        receipt=json.loads((prior/'report.json').read_text())
        original=(prior/'AddFamilySources.v').read_text()
        if not(receipt.get('coqchk_timed_out') and receipt['coqchk_exit']==124 and
               receipt['coqc_exit']==receipt['target_types_exit']==0 and receipt['seconds']>=1200 and
               original==source and hashlib.sha256(original.encode()).hexdigest()==receipt['source_sha256']):
            raise ValueError('one equivalent naming attempt requires the actual timed-out identical proposition')
        optimized=replace_once(source,'Module J:=GeneratedAddFamilyJoint.AddFamilyJoint.\n','')
        optimized=re.sub(r"(?<![A-Za-z0-9_'])J\.",'GeneratedAddFamilyJoint.AddFamilyJoint.',optimized)
        normalization=dict(prior=str(prior.resolve()),kind='only_module_J_qualified_name_expansion',
            original_source_sha256=receipt['source_sha256'],
            normalized_original_sha256=hashlib.sha256(optimized.encode()).hexdigest(),
            normalized_candidate_sha256=hashlib.sha256(optimized.encode()).hexdigest(),
            identical_after_module_alias_expansion=True)
        source=optimized
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    file=out/'AddFamilySources.v';file.write_text(source)
    for name,data in [('providers',paths),('plan',plan),('exports',exports),('inputs',c)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    if normalization:
        (out/'equivalent-naming.json').write_text(json.dumps(normalization,indent=2)+'\n')
    flags=list(base.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedAddFamilySources']
    root=base.controls.history.admission.observation.origin.ROOT
    budget=1200
    if optimization_spent_from:
        if not optimization_from:raise ValueError('cannot debit an unrelated attempt')
        spent=json.loads((Path(optimization_spent_from)/'report.json').read_text())
        if spent.get('accepted')or spent['coqc_exit']!=1:
            raise ValueError('only the recorded naming syntax failure may be repaired')
        budget-=spent['seconds']
    start=time.monotonic()
    baseline_file=out/'Baseline.v'
    baseline_file.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
        'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
        'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
    bc,bt=run_stage([str(root/'_opam/bin/coqc'),*flags,str(baseline_file.resolve())],out/'baseline.log',budget)
    baseline=parse_assumptions(bc.stdout)
    cc,t=run_stage([str(root/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',max(.1,budget-(time.monotonic()-start)))
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=t,exports=exports,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=raw['source_sha256'],old_inv_read=False,complete_R_generated=False,
        infinite_itree_refinement_proved=False,caller_batch_correctness_eliminated=False,
        caller_slot_correspondence_eliminated=False)
    if cc.returncode==0:
        axioms=audit_all_exports(cc.stdout.split('FAMILY_SOURCES_AUDIT')[-1],len(exports))
        audit=bc.returncode==0 and not(axioms-baseline)and not(axioms-ALLOWED_AXIOMS)
        types=source[:source.index('Lemma protect')]
        types+='\nRequire Import GeneratedAddFamilySources.AddFamilySources.\nImport GeneratedAddFamilySources.AddFamilySources.\n'
        types+='Section Types.\nContext {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}\n {word_ok:word.ok word}{registers_ok:map.ok Registers}.\n'
        for name in ['actual_producer_bundle','actual_admitted_add_operand_relation','actual_admitted_addi_operand_relation',
                     'actual_family_operand_clause_phase','actual_family_operand_clause_with_new_tokens']:
            match=re.search(r'Theorem '+name+r' ([^:]+):(.*?)\nProof\.',source,re.S)
            if not match:raise ValueError('cannot independently restate consumer type')
            binders,statement=match.groups()
            types+=f'Definition checked_{name} {binders}:{statement}\nProof. exact({name} {binders}). Qed.\n'
        types+='End Types.\n'
        type_file=out/'TargetTypes.v';type_file.write_text(types)
        tc,tt=run_stage([str(root/'_opam/bin/coqc'),*flags,str(type_file.resolve())],out/'target-types.log',max(.1,budget-(time.monotonic()-start)))
        audit=audit and tc.returncode==0
        kk,kt=run_stage([str(root/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAddFamilySources.AddFamilySources'],out/'coqchk.log',max(.1,budget-(time.monotonic()-start)))
        report.update(coqchk_exit=kk.returncode,coqchk_timed_out=kt,assumptions=sorted(axioms),baseline_assumptions=sorted(baseline),baseline_exit=bc.returncode,target_types_exit=tc.returncode,
            assumptions_audit_passed=audit,accepted=audit and kk.returncode==0,
            caller_batch_correctness_eliminated=audit and kk.returncode==0,caller_slot_correspondence_eliminated=audit and kk.returncode==0)
    report['seconds']=time.monotonic()-start
    report['budget_seconds']=budget
    report['optimization_spent_from']=optimization_spent_from
    if report['accepted']:
        report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['family','addi-controls','addi-capture','output']:p.add_argument('--'+key,required=True)
    p.add_argument('--optimization-from')
    p.add_argument('--optimization-spent-from')
    a=p.parse_args();r=check(joint.inputs(),a.family,a.addi_controls,a.addi_capture,a.output,a.optimization_from,a.optimization_spent_from)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
