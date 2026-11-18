"""Actual guarded RF write commits ADD/ADDI from the unified Current relation.

Only physical pending transport, selector history, destination identity and bank
transport are reused. No old CPU/register/queue invariant is consumed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_joint as joint
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def render(c, raw, profile, plan, selector):
    p, am = profile['ast']['program'], raw['module']
    sample = f'(phase_driven_state {p} ev pre)'
    post = f'(PhaseSemantics {p} ev pre)'
    packed = '(H.boot_history image events)'
    nextpacked = f'(C.advance_capture_fields ev pre{packed}tt)'
    write = selector['write']
    bank, total, process = [write[k] for k in ['bank', 'total', 'process']]
    result, data, endpoint = [selector[k] for k in ['result', 'write_data', 'endpoint']]
    head = selector['head']
    valid = plan['head']['valid']
    left, right = plan['left'], plan['right']
    capture = plan['head']['process']
    capture_idle_index = plan.get('capture_idle_index', 1)
    guards = [f'Z.eqb(eval_expr {sample}{g})0%Z={str(not taken).lower()}' for g, taken in write['guards']]
    guard_arguments = ' '.join('HG' + str(i) for i in range(len(guards)))
    prerequisites = '\n'.join(g + ' ->' for g in guards)
    source = f'''From Coq Require Import List ZArith.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVRegisterBank
 Lang.ExtendedSVBankPlan Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVCompanionField
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVTwoInputExpression
 Ex.External.CPUOriginalISAReference Ex.External.CPUReferenceValues Ex.External.CPUReferenceCuts
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUComputedResultCut
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects Ex.External.CPUISAAddiEffects
 Ex.External.CPUISAAddiFields Ex.External.CPUISAAddFamilyReferenceValues
 Ex.External.CPUReferenceAddFamilyProducers Ex.External.CPUReferenceProducerBatches
 Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterWritebackValue
 Ex.External.CPURegisterEffectRelation Ex.External.CPUInstructionFields
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility
 GeneratedAddFamilyJoint.AddFamilyJoint GeneratedWritebackSelector.WritebackSelector
 GeneratedWritebackRF.WritebackRF GeneratedCoveredDestination.CoveredDestination GeneratedBank.AutoBank
 GeneratedAddiReadyControls.AddiReadyControls.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVScalarExpression
 ExtendedSVRegisterBank ExtendedSVBankPlan ExtendedSVProjectionOrigin ExtendedSVCompanionField
 ExtendedSVCaptureBirth ExtendedSVCapturedPending CPUOriginalISAReference CPUReferenceCuts
 CPUGeneratedJointTemplate CPUComputedResultCut CPUISAInstructionExecution CPUISAExecutionEffects
 CPUISAAddiEffects CPUISAAddiFields CPUISARegisterUpdate CPURegisterWritebackValue
 CPURegisterEffectRelation CPUInstructionFields.
Module J:=GeneratedAddFamilyJoint.AddFamilyJoint.
Module H:=J.H. Module C:=J.C. Module Q:=J.Q. Module V:=J.V.
Module F:=CPUISAAddFamilyReferenceValues.
Module S:=GeneratedWritebackSelector.WritebackSelector.
Module R:=GeneratedWritebackRF.WritebackRF.
Module Destination:=GeneratedCoveredDestination.CoveredDestination.
Module Bank:=GeneratedBank.AutoBank.
Local Opaque {p} PhaseSemantics.

Lemma addi_load_zero code rd rs imm:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Addi rd rs imm) ->
 S.Head.G.decoder_{head['root']} code 1%Z=0%Z.
Proof. exact(GeneratedAddiReadyControls.AddiReadyControls.CheckedAddiDecoder.head_addi_zero code rd rs imm). Qed.

Theorem addi_selects_alu image events token rd rs imm:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->C.C.chain_tag2(snd{packed})=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm) ->
 norm 1(read_signal pre {endpoint})=0%Z.
Proof. intros pre HE HT HD;pose proof(S.boot image events HE)as HJ;unfold S.Joint in HJ.
'''
    source += 'destruct HJ as[_ HJ].\n' * (len(selector['rows']) - 1)
    source += f''' specialize(HJ token HT);unfold S.Head.reference_{head['root']} in HJ;injection HJ as HJ.
 exact(eq_trans(eq_sym HJ)(addi_load_zero _ _ _ _ HD)). Qed.

Theorem actual_addi_write_data image events ev token rd rs imm:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 C.C.chain_tag2(snd{packed})=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm) ->
 norm 32(read_signal {sample}{data})=norm 32(read_signal pre {result}).
Proof. intros pre HE HEv HT HD;destruct(S.Head.G.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(addi_selects_alu image events token rd rs imm HE HT HD)as HZero;fold pre in HZero.
 rewrite(S.WritebackDataCone.cone_{data}_actual seed _ HL).
 let e:=eval cbv in S.WritebackDataCone.cone_{data} in
 change(norm 32(eval_expr {sample} e)=norm 32(read_signal pre {result})).
 cbn[eval_expr];rewrite !norm_idempotent.
 rewrite(sampled_root_preserved {p} ev pre {endpoint}
 (history_comb_frame _ _ _ _ _ S.scalar_{endpoint})(S.protect ev {endpoint} HEv ltac:(simpl;tauto))),HZero.
 rewrite(sampled_root_preserved {p} ev pre {result}
 (history_comb_frame _ _ _ _ _ S.Results.scalar_{result})(S.protect_result ev HEv)).
 rewrite Z.eqb_refl;apply norm_idempotent. Qed.

Section ISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.

Theorem operand_clause_idle reference_pc initial ledger image events ev:
 let pre:=phase_run {p} events(H.F.boot image)in
 H.W.Environment ev ->process_matches_states pre {sample}{am}.{capture}=false ->
 J.OperandClause reference_pc initial ledger pre{packed} ->
 J.OperandClause reference_pc initial ledger {post}{nextpacked}.
Proof. intros pre HE HP HO HV token HT.
 rewrite(history_phase_projection _ _ _ _ _ C.V.root_{valid}_valid_certificate ev pre
 (J.O.protect ev {valid} HE ltac:(simpl;tauto))),HP in HV.
 cbn[C.advance_capture_fields snd C.C.advance_tags C.C.chain_tag0]in HT.
 unfold C.C.projection_0_origin,projection_phase_origin in HT;rewrite HP in HT.
 destruct(proj1(computed_result_R_exact(instruction_effect reference_pc token_word)token_eq_dec
 (J.OperandProjection token pre)token initial ledger)(HO HV token HT))as[index[before[after[HL[HS HProjection]]]]].
 apply(proj2(computed_result_R_exact(instruction_effect reference_pc token_word)token_eq_dec
 (J.OperandProjection token {post})token initial ledger)).
 exists index,before,after;split;[exact HL|];split;[exact HS|].
 destruct HProjection as[HAdd|HAddi].
 - left;destruct HAdd as[rd[rs1[rs2[HD HReads]]]];exists rd,rs1,rs2;split;[exact HD|].
   intros x y HX HY;destruct(HReads x y HX HY)as[HLeft HRight];split.
   + rewrite(history_phase_projection _ _ _ _ _ J.O.O.scalar_{left} ev pre(J.O.protect ev {left} HE ltac:(simpl;tauto))),HP;exact HLeft.
   + rewrite(history_phase_projection _ _ _ _ _ J.O.O.scalar_{right} ev pre(J.O.protect ev {right} HE ltac:(simpl;tauto))),HP;exact HRight.
 - right;destruct HAddi as[rd[rs[imm[HD HReads]]]];exists rd,rs,imm;split;[exact HD|].
   intros x HX;rewrite(history_phase_projection _ _ _ _ _ J.O.O.scalar_{left} ev pre
   (J.O.protect ev {left} HE ltac:(simpl;tauto))),HP;exact(HReads x HX).
Qed.

Theorem actual_family_writeback_restores_RF(reference_pc:Token->Z)image events ev token before after:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 C.C.chain_tag2(snd{packed})=Some token ->
 instruction_effect reference_pc token_word token before=Some after ->
 process_matches_states pre {sample}{am}.{process}=true ->
{prerequisites}
 RegisterRelated(lane_read 32(read_signal pre {bank}))before ->
 F.computed_value token_word token before=Some(norm 32(read_signal pre {result})) ->
 FormalSpec.run1 before=(Some tt,after) /\\
 RegisterRelated(lane_read 32(read_signal {post}{bank}))after.
Proof. intros pre HE HEv HT HSTEP HP {guard_arguments} HR HValue.
 destruct(CPUReferenceAddFamilyProducers.computed_value_implies_family token_word token before _ HValue)
 as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].
 - destruct(Destination.actual_write_destination_from_boot image events ev HE HEv HP {guard_arguments})as[actual[HActual HOperations]].
   assert(actual=token)by congruence;subst actual.
   specialize(HOperations(Decode.Add rd rs1 rs2)rd [] HD eq_refl).
   pose proof(S.actual_add_write_data image events ev token rd rs1 rs2 HE HEv HT HD)as HData;fold pre in HData,HOperations.
   destruct(token_execute reference_pc token_word token before after _ HSTEP HD)as[middle[HExec HEnd]].
   destruct(original_add_effect before middle rd rs1 rs2 HExec)as[x[y[HX[HY HREG]]]].
   unfold F.computed_value in HValue;rewrite HD,HX,HY in HValue;injection HValue as HValue.
   assert(HOriginal:ISAProjectedRegisterEffects before after(register_operations rd(Utility.add x y))).
   {{ intros address Haddr;unfold ISAView;rewrite(end_cycle_register_frame middle after HEnd);exact(HREG address Haddr). }}
   split;[exact(proj2(proj2(instruction_effect_sound reference_pc token_word token before after HSTEP)))|].
   apply(actual_phase_register_transport {p} {bank} {total} Bank.bank_{bank}_entries Bank.bank_{bank}_certificate ev pre before after
   (R.protect_bank ev HEv)HR).
   rewrite HOperations;apply(register_operations_as_lane before after rd(Utility.add x y) _ HOriginal).
   cbn[eval_expr];rewrite !norm_idempotent;exact(eq_trans HData(eq_sym HValue)).
 - destruct(Destination.actual_write_destination_from_boot image events ev HE HEv HP {guard_arguments})as[actual[HActual HOperations]].
   assert(actual=token)by congruence;subst actual.
   specialize(HOperations(Decode.Addi rd rs imm)rd [] HD eq_refl).
   pose proof(actual_addi_write_data image events ev token rd rs imm HE HEv HT HD)as HData;fold pre in HData,HOperations.
   destruct(token_execute reference_pc token_word token before after _ HSTEP HD)as[middle[HExec HEnd]].
   destruct(original_addi_effect before middle rd rs imm HExec)as[x[HX HREG]].
   unfold F.computed_value in HValue;rewrite HD,HX in HValue;injection HValue as HValue.
   assert(HOriginal:ISAProjectedRegisterEffects before after(register_operations rd(Utility.add x(Utility.ZToReg imm)))).
   {{ intros address Haddr;unfold ISAView;rewrite(end_cycle_register_frame middle after HEnd);exact(HREG address Haddr). }}
   split;[exact(proj2(proj2(instruction_effect_sound reference_pc token_word token before after HSTEP)))|].
   apply(actual_phase_register_transport {p} {bank} {total} Bank.bank_{bank}_entries Bank.bank_{bank}_certificate ev pre before after
   (R.protect_bank ev HEv)HR).
   rewrite HOperations;apply(register_operations_as_lane before after rd(Utility.add x(Utility.ZToReg imm)) _ HOriginal).
   cbn[eval_expr];rewrite !norm_idempotent;exact(eq_trans HData(eq_sym HValue)).
Qed.

Theorem actual_family_write_preserves_Current(reference_pc:Token->Z)initial retired current image events ev:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->H.W.Environment ev ->
 process_matches_states pre {sample}{am}.{process}=true ->
{prerequisites}
 J.Current reference_pc initial retired current pre{packed} ->
 exists token after,
 Q.actual_pending pre{packed}=token::Q.actual_pending {post}{nextpacked} /\\
 instruction_effect reference_pc token_word token current=Some after /\\
 FormalSpec.run1 current=(Some tt,after) /\\
 J.Current reference_pc initial(retired++[token])after {post}{nextpacked}.
Proof. intros pre HE HEv HP {guard_arguments} HCurrent.
 destruct(Q.actual_write_pending_transfer image events ev HE HEv HG0 HP HG{len(guards)-1})as[token[HT[HOld HNew]]].
 change(Q.actual_pending pre{packed}=token::Q.lower_pending pre{packed})in HOld.
 change(Q.actual_pending {post}{nextpacked}=Q.lower_pending pre{packed})in HNew.
 destruct HCurrent as[HN HC HR HResults HOp [frontier HChain]].
 change(NoDup(map token_id(retired++Q.actual_pending pre{packed})))in HN.
 change(J.OperandClause reference_pc initial(retired++Q.actual_pending pre{packed})pre{packed})in HOp.
 change(V.Joint(F.values reference_pc token_word token_id initial(retired++Q.actual_pending pre{packed}))pre{packed})in HResults.
 change(EffectChain(instruction_effect reference_pc token_word)current(Q.actual_pending pre{packed})frontier)in HChain.
 rewrite HOld in HN,HOp,HResults.
 destruct HResults as[HCov[HMem HWb]].
 pose proof(HWb(V.actual_write_is_valid image events ev HE HEv HG{len(guards)-1})token HT)as HValue.
 pose proof(CPUReferenceProducerBatches.prefix_key_fresh token_id retired token
 (Q.lower_pending pre{packed})HN)as HFresh.
 unfold F.values in HValue.
 rewrite(CPUReferenceValues.committed_prefix(instruction_effect reference_pc token_word)token_id
 (F.computed_value token_word)initial retired current(token::Q.lower_pending pre{packed})token HC HFresh),
 CPUReferenceValues.at_head in HValue.
 rewrite HOld in HChain;inversion HChain as[|a t after rest final HSTEP HRest];subst.
 destruct(actual_family_writeback_restores_RF reference_pc image events ev token current after
 HE HEv HT HSTEP HP {guard_arguments} HR HValue)as[HRun HRNext].
 assert(HResult:J.ResultJoint reference_pc initial(retired++token::Q.lower_pending pre{packed}){post}{nextpacked}).
 {{ apply(J.actual_result_phase reference_pc initial _ image events ev HE HEv HN HOp).
   unfold J.ResultJoint;split;[exact HCov|];split;[exact HMem|exact HWb]. }}
 assert(HOperand:J.OperandClause reference_pc initial(retired++token::Q.lower_pending pre{packed}){post}{nextpacked}).
 {{ exact(operand_clause_idle reference_pc initial _ image events ev HEv
    (Q.stage_{capture_idle_index}_idle image events ev HE HEv HG0 HP)HOp). }}
 assert(HLedger:(retired++[token])++Q.actual_pending {post}{nextpacked}=
 retired++token::Q.lower_pending pre{packed}).
 {{ rewrite HNew,<-app_assoc;reflexivity. }}
 exists token,after;split;[rewrite HNew;exact HOld|];split;[exact HSTEP|];split;[exact HRun|].
 constructor.
 - change(NoDup(map token_id((retired++[token])++Q.actual_pending {post}{nextpacked}))).
   rewrite HLedger;exact HN.
 - eapply chain_append;[exact HC|];econstructor;[exact HSTEP|constructor].
 - exact HRNext.
 - change(J.ResultJoint reference_pc initial((retired++[token])++Q.actual_pending {post}{nextpacked}){post}{nextpacked}).
   rewrite HLedger;exact HResult.
 - change(J.OperandClause reference_pc initial((retired++[token])++Q.actual_pending {post}{nextpacked}){post}{nextpacked}).
   rewrite HLedger;exact HOperand.
 - exists frontier;rewrite HNew;exact HRest.
Qed.
End ISA.
Goal True. idtac "FAMILY_WRITEBACK_AUDIT". exact I. Qed.
'''
    exports = ['addi_load_zero', 'addi_selects_alu', 'actual_addi_write_data', 'operand_clause_idle',
               'actual_family_writeback_restores_RF', 'actual_family_write_preserves_Current']
    source += ''.join('Print Assumptions ' + name + '.\n' for name in exports)
    return source, exports


def inline_module_aliases(source):
    """One same-target optimization: avoid copying imported module signatures."""
    declaration = re.compile(r'\bModule\s+([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*'
                             r'([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\s*\.\s*')
    aliases = {}
    for match in declaration.finditer(source):
        name, target = match.groups()
        first, *rest = target.split('.')
        aliases[name] = '.'.join([aliases.get(first, first), *rest])
    if set(aliases) != {'J', 'H', 'C', 'Q', 'V', 'F', 'S', 'R', 'Destination', 'Bank'}:
        raise ValueError('unexpected module alias set; refuse unrelated source rewrite')
    qualifier = re.compile(r'(?<![A-Za-z0-9_.])(' + '|'.join(aliases) + r')\.(?=[A-Za-z_])')
    return qualifier.sub(lambda match: aliases[match.group(1)] + '.', declaration.sub('', source)), aliases


def same_target_evidence(before, after, exports, aliases):
    normalized, check_aliases = inline_module_aliases(before)
    if check_aliases != aliases or normalized != after:
        raise ValueError('same-target normalized full source differs')
    proofs = {}
    for name in exports:
        pattern = r'(?:Lemma|Theorem) ' + name + r'\b.*?\nProof\..*?Qed\.'
        old = re.search(pattern, before, re.S).group(0)
        new = re.search(pattern, after, re.S).group(0)
        qualifier = re.compile(r'(?<![A-Za-z0-9_.])(' + '|'.join(aliases) + r')\.(?=[A-Za-z_])')
        old_normal = qualifier.sub(lambda match: aliases[match.group(1)] + '.', old)
        if old_normal != new:
            raise ValueError('same-target statement or proof differs: ' + name)
        old_head, old_proof = old_normal.split('\nProof.', 1)
        new_head, new_proof = new.split('\nProof.', 1)
        digest = lambda value: hashlib.sha256(value.encode()).hexdigest()
        proofs[name] = dict(normalized_original_declaration_sha256=digest(old_head),
                            new_declaration_sha256=digest(new_head),
                            normalized_original_proof_sha256=digest(old_proof),
                            new_proof_sha256=digest(new_proof), exact_equal=True)
    return dict(alias_mapping=aliases, normalized_original_source_sha256=hashlib.sha256(normalized.encode()).hexdigest(),
                new_source_sha256=hashlib.sha256(after.encode()).hexdigest(),
                full_normalized_source_exact_equal=True, proofs=proofs)


def check(c, family_folder, output, optimize_after_timeout=None):
    verified(family_folder, 'AddFamilyJoint')
    addi_ready = c['addi_ready']
    verified(addi_ready, 'AddiReadyControls')
    raw, profile, _ = joint.derived.controls.history.admission.observation.origin.raw_binding(c['ast'], c['ast_module'])
    plan = joint.discover(c, raw)
    paths = json.loads((Path(family_folder) / 'providers.json').read_text())
    paths += [dict(namespace='GeneratedAddFamilyJoint', directory=str(Path(family_folder).resolve()))]
    paths += [dict(namespace='GeneratedAddiReadyControls', directory=str(Path(addi_ready).resolve()))]
    bindings = {row['namespace']: row['directory'] for row in paths}
    selector = json.loads((Path(bindings['GeneratedWritebackSelector']) / 'plan.json').read_text())
    if selector['ast_sha256'] != raw['source_sha256']:
        raise ValueError('physical selector configuration differs')
    ready_plan = json.loads((Path(addi_ready) / 'plan.json').read_text())
    head_loads = [(row['selection']['root'], row['selection']['capture'])
                  for row in ready_plan['rows'] if row['stage'] == 0]
    if head_loads != [(selector['head']['root'], selector['head']['capture'])]:
        raise ValueError('ADDI decoder provider is not bound to the same physical head selector')
    pending_plan = json.loads((Path(plan['queue_context']) / 'plan.json').read_text())
    idle_indexes = [i for i, node in enumerate(pending_plan['nodes'][:-1])
                    if node['index'] == plan['head']['index'] and node['process'] == plan['head']['process']]
    if len(idle_indexes) != 1:
        raise ValueError('physical pending capture-idle rule does not uniquely bind the operand process')
    plan['capture_idle_index'] = idle_indexes[0]
    source, exports = render(c, raw, profile, plan, selector)
    optimization = None
    if optimize_after_timeout:
        previous = Path(optimize_after_timeout)
        failure = json.loads((previous / 'report.json').read_text())
        original = (previous / 'AddFamilyWriteback.v').read_text()
        if not(failure['seconds'] >= 1200 and
               (failure.get('coqc_timed_out') or failure.get('coqchk_timed_out') or failure.get('exact_type_audit_timed_out'))
               and not failure.get('performance_attempt') and original == source
               and hashlib.sha256(original.encode()).hexdigest() == failure['source_sha256']):
            raise ValueError('first same-target optimization requires the unchanged actual timed-out point')
        source, aliases = inline_module_aliases(source)
        optimization = same_target_evidence(original, source, exports, aliases)
    out = Path(output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    target = out / 'AddFamilyWriteback.v'
    target.write_text(source)
    if optimization:
        (out / 'same-target-normalization.json').write_text(json.dumps(optimization, indent=2) + '\n')
    (out / 'providers.json').write_text(json.dumps(paths, indent=2) + '\n')
    (out / 'plan.json').write_text(json.dumps(dict(operands=plan, selector=selector), indent=2) + '\n')
    (out / 'exports.json').write_text(json.dumps(exports, indent=2) + '\n')
    flags = list(joint.derived.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out), 'GeneratedAddFamilyWriteback']
    root = joint.derived.controls.history.admission.observation.origin.ROOT
    start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'coqc.resources'),
        str(root / '_opam/bin/coqc'), '-time', *flags, str(target)], out / 'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), old_inv_read=False,
                  ast_sha256=raw['source_sha256'], family_joint_source_sha256=hashlib.sha256(
                      (Path(family_folder) / 'AddFamilyJoint.v').read_bytes()).hexdigest(),
                  complete_R_generated=False, PC_RAM_relation_preserved=False,
                  conditional_scope=['checked external-event environment', 'actual RF process matches',
                                     'original inactive-reset and effective-write guards'],
                  actual_family_Current_commit_proved=False, external_llm_api_calls=0)
    if optimization:
        report.update(performance_attempt=1, actual_timeout_evidence=str(Path(optimize_after_timeout).resolve()),
                      same_target_normalized_exact_equal=True)
    if cc.returncode == 0:
        axioms = audit_all_exports(cc.stdout.split('FAMILY_WRITEBACK_AUDIT')[-1], len(exports))
        baseline = out / 'Baseline.v'
        baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
            'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
            'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
        bc, bt = run_stage([str(root / '_opam/bin/coqc'), *flags, str(baseline)], out / 'baseline.log',
                           max(.1, 1200 - (time.monotonic() - start)))
        allowed = parse_assumptions(bc.stdout) if bc.returncode == 0 else set()
        kk, kt = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'coqchk.resources'),
                           str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec',
                           'GeneratedAddFamilyWriteback.AddFamilyWriteback'], out / 'coqchk.log',
                           max(.1, 1200 - (time.monotonic() - start)))
        audit = bc.returncode == 0 and not(axioms - allowed) and not(allowed - ALLOWED_AXIOMS)
        # Reimport the exact written declarations, not inferred Check output.
        audit_source = source[:source.index('Lemma addi_load_zero')]
        audit_source += 'Require Import GeneratedAddFamilyWriteback.AddFamilyWriteback.\n'
        argument_lists = [
            'code rd rs imm', 'image events token rd rs imm',
            'image events ev token rd rs imm', 'reference_pc initial ledger image events ev',
            'reference_pc image events ev token before after',
            'reference_pc initial retired current image events ev']
        for index, (name, arguments) in enumerate(zip(exports, argument_lists)):
            if index == 3:
                audit_source += source[source.index('Section ISA.'):source.index('Theorem operand_clause_idle')]
            declaration = re.search(r'(?:Lemma|Theorem) ' + name + r'\b.*?(?=\nProof\.)', source, re.S).group(0)
            audit_source += declaration.replace(name, 'audit_' + name, 1)
            audit_source += '\nProof. exact (GeneratedAddFamilyWriteback.AddFamilyWriteback.' + name + ' ' + arguments + '). Qed.\n'
        audit_source += 'End ISA.\n'
        for name in exports:
            audit_source += 'Print Assumptions audit_' + name + '.\n'
        audit_path = out / 'ExactTypeAudit.v'
        audit_path.write_text(audit_source)
        ac, at = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'exact-type-coqc.resources'),
                          str(root / '_opam/bin/coqc'), '-time', *flags, str(audit_path)],
                          out / 'exact-type-audit.log', max(.1, 1200 - (time.monotonic() - start)))
        exact_axioms = audit_all_exports(ac.stdout, len(exports)) if ac.returncode == 0 else set()
        ek, et = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'exact-type-coqchk.resources'),
                           str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec',
                           'GeneratedAddFamilyWriteback.ExactTypeAudit'], out / 'exact-type-coqchk.log',
                           max(.1, 1200 - (time.monotonic() - start))) if ac.returncode == 0 else (None, False)
        exact_ok = ac.returncode == 0 and ek.returncode == 0 and not(exact_axioms - allowed)
        accepted = audit and kk.returncode == 0 and exact_ok
        report.update(baseline_coqc_exit=bc.returncode, baseline_timed_out=bt,
                      baseline_assumptions=sorted(allowed), assumptions=sorted(axioms),
                      assumptions_audit_passed=audit, coqchk_exit=kk.returncode, coqchk_timed_out=kt,
                      exact_type_audit_exit=ac.returncode, exact_type_audit_timed_out=at,
                      exact_type_coqchk_exit=ek.returncode if ek else None, exact_type_coqchk_timed_out=et,
                      exact_type_assumptions=sorted(exact_axioms), accepted=accepted,
                      actual_family_Current_commit_proved=accepted)
    report['seconds'] = time.monotonic() - start
    if report['accepted']:
        report['object_sha256'] = hashlib.sha256(target.with_suffix('.vo').read_bytes()).hexdigest()
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--base', default='framework/bzeeno-cdfg-add-inputs.json')
    parser.add_argument('--addi', default='framework/bzeeno-cdfg-addi-inputs.json')
    parser.add_argument('--addi-ready', default='results/r-addi-ready-controls-20261027-a10')
    parser.add_argument('--optimize-after-timeout')
    args = parser.parse_args()
    config = joint.inputs(args.base, args.addi)
    config['addi_ready'] = args.addi_ready
    result = check(config, args.family, args.output, args.optimize_after_timeout)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
