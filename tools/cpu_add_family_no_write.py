"""Commit valid ADD/ADDI-to-x0 on the real falling RF/no-write branch.

An empty physical write list is not an empty ISA commit. This consumes the same
FamilyJoint.Current as effective writeback and includes ADDI x0,x0,0 (NOP).
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_joint as family
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def render(c, raw, profile, plan, selector, pending):
    p, am = profile['ast']['program'], raw['module']
    j = 'GeneratedAddFamilyJoint.AddFamilyJoint'
    h, cap, q, v = [j + '.' + name for name in ['H', 'C', 'Q', 'V']]
    f = 'CPUISAAddFamilyReferenceValues'
    wb = 'GeneratedAddFamilyWriteback.AddFamilyWriteback'
    dest = 'GeneratedCoveredDestination.CoveredDestination'
    isa_dest = 'GeneratedISADestinations.ISADestinations'
    wr = 'GeneratedWritebackRF.WritebackRF'
    wb_node = pending['nodes'][-1]
    valid, rd_root = wb_node['valid'], wb_node['root']
    address = selector['write']['index_root']
    bank = selector['write']['bank']
    rf = pending['rf']
    packed = f'({h}.boot_history image events)'
    sample = f'(phase_driven_state {p} ev pre)'
    post = f'(PhaseSemantics {p} ev pre)'
    after = f'({cap}.advance_capture_fields ev pre{packed}tt)'
    pre = f'phase_run {p} events({h}.F.boot image)'
    fired = f'process_matches_states pre {sample}{am}.{rf["process"]}=true'
    reset = f'Z.eqb(eval_expr {sample}(EVar 1 {rf["reset"]}))0%Z=false'
    is_valid = f'norm 1(read_signal pre {valid})<>0%Z'
    zero = f'norm 5(read_signal {sample}{address})=0%Z'
    guard = selector['write']['guards'][-1][0]
    source = f'''From Coq Require Import List ZArith.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVScalarHistory Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending
 Lang.ExtendedSVRegisterBank Ex.External.CPUGeneratedJointTemplate Ex.External.CPUReferenceValues
 Ex.External.CPUOriginalISAReference Ex.External.CPURegisterEffectRelation
 Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects Ex.External.CPUISAAddiEffects
 Ex.External.CPUISARegisterUpdate Ex.External.CPUReferenceProducerBatches
 Ex.External.CPUReferenceAddFamilyProducers Ex.External.CPUISAAddFamilyReferenceValues
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedAddFamilyJoint.AddFamilyJoint GeneratedAddFamilyWriteback.AddFamilyWriteback
 GeneratedCoveredDestination.CoveredDestination GeneratedISADestinations.ISADestinations
 GeneratedWritebackRF.WritebackRF.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory
 ExtendedSVCaptureBirth ExtendedSVCapturedPending ExtendedSVRegisterBank
 CPUGeneratedJointTemplate CPUOriginalISAReference CPURegisterEffectRelation
 CPUISAInstructionExecution CPUISAExecutionEffects CPUISAAddiEffects CPUISARegisterUpdate.
Local Opaque {p} PhaseSemantics.

Lemma original_NOP_decode:
 Decode.decode Decode.RV32I 19%Z=Decode.IInstruction(Decode.Addi 0%Z 0%Z 0%Z).
Proof. vm_compute;reflexivity. Qed.

Lemma actual_zero_guard ev pre:
 {zero} ->Z.eqb(eval_expr {sample}{guard})0%Z=true.
Proof. intro H;cbn[eval_expr];rewrite H;rewrite Z.land_0_r;reflexivity. Qed.

Lemma protect_WB_destination ev:{h}.W.Environment ev ->changed_signal ev<>{rd_root}%nat.
Proof. intros[_ HE];unfold {h}.W.ExternalEvent in HE;apply existsb_exists in HE;
 destruct HE as[x[HX HE]];apply Nat.eqb_eq in HE;rewrite HE;unfold {h}.W.external_roots in HX;
 cbn in HX;repeat destruct HX as[<-|HX];try contradiction;discriminate. Qed.

Theorem actual_valid_WB_pending_transfer image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{reset} ->{fired} ->{is_valid} ->
 exists token,{cap}.C.chain_tag2(snd{packed})=Some token /\\
 {q}.actual_pending pre{packed}=token::{q}.lower_pending pre{packed} /\\
 {q}.actual_pending {post}{after}={q}.lower_pending pre{packed}.
Proof. intros pre HE HEv HR HF HV.
 destruct({cap}.valid_field_2_has_value pre{packed}(proj1({h}.boot_and_runtime_related image events HE))HV)
 as[token[HT HValue]].
 destruct({q}.actual_write_clock_boundaries image events ev HE HEv HR HF)as[HO HN].
 change(Z.eqb(norm 1(read_signal pre {pending['capture_clock']}))0%Z=false)in HO.
 change(norm 1(read_signal {sample}{pending['capture_clock']})=0%Z)in HN.
 exists token;split;[exact HT|];split.
 - exact({q}.pending_high pre{packed}token HO HV HT).
 - exact(eq_trans({q}.pending_low {post}{after}
   (eq_trans({q}.clock_post_eq_sample image events ev HE HEv)HN))
   ({q}.lower_pending_write_frame image events ev{packed}HE HEv HR HF)).
Qed.

Theorem actual_valid_WB_destination image events ev token instruction rd rest:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{is_valid} ->
 {cap}.C.chain_tag2(snd{packed})=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction instruction ->
 destination_registers instruction=rd::rest ->
 norm 5(read_signal {sample}{address})=rd.
Proof. intros pre HE HEv HV HT HD HRegs.
 destruct({j}.A.H.G.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 destruct({cap}.valid_field_2_has_value pre{packed}(proj1({h}.boot_and_runtime_related image events HE))HV)
 as[actual[HActual HField]].
 assert(actual=token)by congruence;subst actual.
 rewrite({dest}.sampled_endpoint seed ev pre(protect_WB_destination ev HEv)HL),HField,{dest}.captured_head_rd.
 exact(eq_sym({isa_dest}.original_destination_address(token_word token)instruction rd rest HD HRegs)).
Qed.

Section ISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.

Theorem original_family_x0_RF_frame(reference_pc:Token->Z)token(before after:FormalSpec.State):
 instruction_effect reference_pc token_word token before=Some after ->
 ((exists rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add 0%Z rs1 rs2)) \\/
 (exists rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi 0%Z rs imm))) ->
 forall address,(0<=address<32)%Z ->ISAView after address=ISAView before address.
Proof. intros HS HD address HA.
 assert(HProject:ISAProjectedRegisterEffects before after []).
 {{ destruct HD as[[rs1[rs2 HD]]|[rs[imm HD]]].
   - destruct(token_execute reference_pc token_word token before after _ HS HD)as[middle[HX HE]].
     destruct(original_add_effect before middle 0%Z rs1 rs2 HX)as[x[y[HLeft[HRight HR]]]].
     change(ISAProjectedRegisterEffects before middle [])in HR.
     intros i HI;unfold ISAView;rewrite(end_cycle_register_frame middle after HE);exact(HR i HI).
   - destruct(token_execute reference_pc token_word token before after _ HS HD)as[middle[HX HE]].
     destruct(original_addi_effect before middle 0%Z rs imm HX)as[x[HLeft HR]].
     change(ISAProjectedRegisterEffects before middle [])in HR.
     intros i HI;unfold ISAView;rewrite(end_cycle_register_frame middle after HE);exact(HR i HI). }}
 specialize(HProject address HA);change(ISAView after address=project_x0(ISAView before)address)in HProject.
 rewrite HProject;unfold project_x0;destruct(Z.eqb address 0%Z)eqn:HZ;[|reflexivity].
 apply Z.eqb_eq in HZ;subst address;reflexivity.
Qed.

Theorem actual_zero_destination_preserves_Current(reference_pc:Token->Z)initial retired current image events ev:
 let pre:={pre}in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->{fired} ->{reset} ->{is_valid} ->{zero} ->
 {j}.Current reference_pc initial retired current pre{packed} ->
 exists token next,
 {q}.actual_pending pre{packed}=token::{q}.actual_pending {post}{after} /\\
 instruction_effect reference_pc token_word token current=Some next /\\
 FormalSpec.run1 current=(Some tt,next) /\\
 {j}.Current reference_pc initial(retired++[token])next {post}{after}.
Proof. intros pre HE HEv HF HR HV HZero HCurrent.
 destruct(actual_valid_WB_pending_transfer image events ev HE HEv HR HF HV)as[token[HT[HOld HNew]]].
 change({q}.actual_pending pre{packed}=token::{q}.lower_pending pre{packed})in HOld.
 change({q}.actual_pending {post}{after}={q}.lower_pending pre{packed})in HNew.
 destruct HCurrent as[HN HC HRF HResults HOp [frontier HChain]].
 change(NoDup(map token_id(retired++{q}.actual_pending pre{packed})))in HN.
 change({j}.OperandClause reference_pc initial(retired++{q}.actual_pending pre{packed})pre{packed})in HOp.
 change({v}.Joint({f}.values reference_pc token_word token_id initial(retired++{q}.actual_pending pre{packed}))pre{packed})in HResults.
 change(EffectChain(instruction_effect reference_pc token_word)current({q}.actual_pending pre{packed})frontier)in HChain.
 rewrite HOld in HN,HOp,HResults,HChain.
 pose proof(proj2(proj2 HResults)HV token HT)as HValue.
 pose proof(CPUReferenceProducerBatches.prefix_key_fresh token_id retired token({q}.lower_pending pre{packed})HN)as HFresh.
 unfold {f}.values in HValue.
 rewrite(CPUReferenceValues.committed_prefix(instruction_effect reference_pc token_word)token_id
 ({f}.computed_value token_word)initial retired current(token::{q}.lower_pending pre{packed})token HC HFresh),
 CPUReferenceValues.at_head in HValue.
 assert(HDecoded:(exists rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add 0%Z rs1 rs2)) \\/
 (exists rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi 0%Z rs imm))).
 {{ destruct(CPUReferenceAddFamilyProducers.computed_value_implies_family token_word token current _ HValue)
   as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].
   - pose proof(actual_valid_WB_destination image events ev token(Decode.Add rd rs1 rs2)rd [] HE HEv HV HT HD eq_refl)as HDest.
     change(norm 5(read_signal {sample}{address})=rd)in HDest;assert(Hrd:rd=0%Z)by congruence;rewrite Hrd in HD.
     left;exists rs1,rs2;exact HD.
   - pose proof(actual_valid_WB_destination image events ev token(Decode.Addi rd rs imm)rd [] HE HEv HV HT HD eq_refl)as HDest.
     change(norm 5(read_signal {sample}{address})=rd)in HDest;assert(Hrd:rd=0%Z)by congruence;rewrite Hrd in HD.
     right;exists rs,imm;exact HD. }}
 inversion HChain as[|a t next rest final HStep HTail];subst.
 pose proof(proj2(proj2(instruction_effect_sound reference_pc token_word token current next HStep)))as HRun.
 pose proof({j}.actual_result_phase reference_pc initial _ image events ev HE HEv HN HOp HResults)as HResultPost.
 pose proof({wb}.operand_clause_idle reference_pc initial _ image events ev HEv
 ({q}.stage_{plan['capture_idle_index']}_idle image events ev HE HEv HR HF)HOp)as HOperandPost.
 pose proof({wr}.actual_no_write_preserves_RF image events ev current HEv
 (or_intror(conj HF(conj HR(actual_zero_guard ev pre HZero))))HRF)as HRFIdle.
 assert(HRFPost:RegisterRelated(lane_read 32(read_signal {post}{bank}))next).
 {{ exact(related_frame _ current next HRFIdle(original_family_x0_RF_frame reference_pc token current next HStep HDecoded)). }}
 assert(HLedger:(retired++[token])++{q}.actual_pending {post}{after}=
 retired++token::{q}.lower_pending pre{packed}).
 {{ rewrite HNew,<-app_assoc;reflexivity. }}
 exists token,next;split;[rewrite HNew;exact HOld|];split;[exact HStep|];split;[exact HRun|].
 constructor.
 - change(NoDup(map token_id((retired++[token])++{q}.actual_pending {post}{after}))).
   rewrite HLedger;exact HN.
 - eapply chain_append;[exact HC|];econstructor;[exact HStep|constructor].
 - exact HRFPost.
 - change({j}.ResultJoint reference_pc initial((retired++[token])++{q}.actual_pending {post}{after}){post}{after}).
   rewrite HLedger;exact HResultPost.
 - change({j}.OperandClause reference_pc initial((retired++[token])++{q}.actual_pending {post}{after}){post}{after}).
   rewrite HLedger;exact HOperandPost.
 - exists frontier;rewrite HNew;exact HTail.
Qed.
End ISA.
Goal True. idtac "FAMILY_ZERO_AUDIT". exact I. Qed.
'''
    exports = ['original_NOP_decode', 'actual_zero_guard', 'protect_WB_destination',
               'actual_valid_WB_pending_transfer', 'actual_valid_WB_destination',
               'original_family_x0_RF_frame', 'actual_zero_destination_preserves_Current']
    source += ''.join('Print Assumptions ' + name + '.\n' for name in exports)
    return source, exports


def check(c, family_folder, writeback_folder, output):
    verified(family_folder, 'AddFamilyJoint')
    verified(writeback_folder, 'AddFamilyWriteback')
    root = family.derived.controls.history.admission.observation.origin.ROOT
    raw, profile, _ = family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'], c['ast_module'])
    wb_plan = json.loads((Path(writeback_folder) / 'plan.json').read_text())
    plan, selector = wb_plan['operands'], wb_plan['selector']
    pending = json.loads((Path(plan['queue_context']) / 'plan.json').read_text())
    if selector['ast_sha256'] != raw['source_sha256'] or pending['ast_sha256'] != raw['source_sha256']:
        raise ValueError('physical no-write providers have different configurations')
    if len(selector['write']['guards']) != 2:
        raise ValueError('unrecognized original RF guard family')
    paths = json.loads((Path(writeback_folder) / 'providers.json').read_text())
    paths += [dict(namespace='GeneratedAddFamilyWriteback', directory=str(Path(writeback_folder).resolve()))]
    source, exports = render(c, raw, profile, plan, selector, pending)
    out = Path(output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    target = out / 'AddFamilyNoWrite.v'
    target.write_text(source)
    for name, value in [('providers', paths), ('exports', exports), ('plan', wb_plan)]:
        (out / (name + '.json')).write_text(json.dumps(value, indent=2) + '\n')
    flags = list(family.derived.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out), 'GeneratedAddFamilyNoWrite']
    start = time.monotonic()
    remaining = lambda: max(.1, 1200 - (time.monotonic() - start))
    cc, ct = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'coqc.resources'),
                       str(root / '_opam/bin/coqc'), '-time', *flags, str(target)], out / 'coqc.log', remaining())
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=ct,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'],
                  old_inv_read=False, complete_R_generated=False, PC_RAM_relation_preserved=False,
                  actual_x0_Current_commit_proved=False, NOP_included=True, external_llm_api_calls=0,
                  conditional_scope=['checked external-event environment', 'actual falling RF process matches',
                                     'original inactive reset', 'valid WB', 'physical sampled destination x0'])
    if cc.returncode == 0:
        axioms = audit_all_exports(cc.stdout.split('FAMILY_ZERO_AUDIT')[-1], len(exports))
        baseline = out / 'Baseline.v'
        baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
                            'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
                            'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
        bc, bt = run_stage([str(root / '_opam/bin/coqc'), *flags, str(baseline)], out / 'baseline.log', remaining())
        allowed = parse_assumptions(bc.stdout) if bc.returncode == 0 else set()
        audit_source = source[:source.index('Lemma original_NOP_decode')]
        audit_source += 'Require Import GeneratedAddFamilyNoWrite.AddFamilyNoWrite.\n'
        arguments = ['', 'ev pre', 'ev', 'image events ev', 'image events ev token instruction rd rest',
                     'reference_pc token before after', 'reference_pc initial retired current image events ev']
        for index, (name, args) in enumerate(zip(exports, arguments)):
            if index == 5:
                audit_source += source[source.index('Section ISA.'):source.index('Theorem original_family_x0_RF_frame')]
            declaration = re.search(r'(?:Lemma|Theorem) ' + name + r'\b.*?(?=\nProof\.)', source, re.S).group(0)
            audit_source += declaration.replace(name, 'audit_' + name, 1)
            audit_source += '\nProof. exact (GeneratedAddFamilyNoWrite.AddFamilyNoWrite.' + name + ' ' + args + '). Qed.\n'
        audit_source += 'End ISA.\n' + ''.join('Print Assumptions audit_' + name + '.\n' for name in exports)
        audit_path = out / 'ExactTypeAudit.v'
        audit_path.write_text(audit_source)
        ac, at = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'exact-type-coqc.resources'),
                           str(root / '_opam/bin/coqc'), '-time', *flags, str(audit_path)], out / 'exact-type-audit.log', remaining())
        audit_axioms = audit_all_exports(ac.stdout, len(exports)) if ac.returncode == 0 else set()
        kk, kt = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'coqchk.resources'),
                           str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec',
                           'GeneratedAddFamilyNoWrite.AddFamilyNoWrite'], out / 'coqchk.log', remaining())
        ek, et = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'exact-type-coqchk.resources'),
                           str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec',
                           'GeneratedAddFamilyNoWrite.ExactTypeAudit'], out / 'exact-type-coqchk.log', remaining()) if ac.returncode == 0 else (None, False)
        audit = bc.returncode == 0 and not(axioms - allowed) and not(audit_axioms - allowed) and not(allowed - ALLOWED_AXIOMS)
        accepted = audit and ac.returncode == 0 and kk.returncode == 0 and ek.returncode == 0
        report.update(baseline_coqc_exit=bc.returncode, baseline_timed_out=bt, baseline_assumptions=sorted(allowed),
                      assumptions=sorted(axioms), exact_type_assumptions=sorted(audit_axioms), assumptions_audit_passed=audit,
                      exact_type_audit_exit=ac.returncode, exact_type_audit_timed_out=at,
                      coqchk_exit=kk.returncode, coqchk_timed_out=kt,
                      exact_type_coqchk_exit=ek.returncode if ek else None, exact_type_coqchk_timed_out=et,
                      accepted=accepted, actual_x0_Current_commit_proved=accepted)
    report['seconds'] = time.monotonic() - start
    if report['accepted']:
        report['object_sha256'] = hashlib.sha256(target.with_suffix('.vo').read_bytes()).hexdigest()
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', required=True)
    parser.add_argument('--writeback', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--base', default='framework/bzeeno-cdfg-add-inputs.json')
    parser.add_argument('--addi', default='framework/bzeeno-cdfg-addi-inputs.json')
    args = parser.parse_args()
    result = check(family.inputs(args.base, args.addi), args.family, args.writeback, args.output)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
