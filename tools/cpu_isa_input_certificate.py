"""Generate a Coq-checked register-input manifest from original ExecuteI.

Parameter/PC proposals remain separate; this certifies register arguments and
actual successful reads, not complete RTL/ISA input correspondence.
"""
import argparse
import hashlib
import json
import re
import time
from pathlib import Path
import cpu_r_synthesis as synthesis
import cpu_instruction_scope as scopes
from cpu_certificate_acceptance import run_stage


def render(source, instruction_scope='rv32i38'):
    original=synthesis.isa_demands(source)
    plan=scopes.select(original,instruction_scope)
    selected={row['instruction'] for row in plan['instructions']}
    arms=[];supported=[]
    for row in original['instructions']:
        reads=[x['field']for x in row['reference_uses']['inputs']if x['kind']=='register_value']
        pattern='Decode.'+row['instruction']+' '+ ' '.join(row['operands'])
        arms.append(' | '+pattern+' => ['+';'.join(reads)+']')
        if row['instruction'] in selected:
            supported.append(' | '+pattern+' => true')
    text='''From Coq Require Import ZArith List Lia Bool.
Require Import Ex.External.CPUISAExecutionEffects Ex.External.CV32E40PReq41Instruction
 Ex.External.CPUISAOperandCut Ex.External.CPUISAOwnedEffects
 Ex.External.CPUOriginalISAReference Ex.External.CPUReferenceCuts
 Ex.External.CPUOwnedOperandReference Ex.External.CPURegisterEffectRelation
 Ex.External.CPUISAInstructionExecution
 Ex.External.CPUDecodedSourceBounds
 Ex.External.CPUISACompositionalEffects
 Ex.External.CPUGeneratedJointTemplate
 Ex.RvCore.FormalSpec Ex.RvCore.Machine riscv.Spec.ExecuteI
 coqutil.Word.Interface coqutil.Map.Interface coqutil.Word.Bitwidth coqutil.Byte riscv.Utility.Monads.
Import ListNotations CPUISAExecutionEffects CV32E40PReq41Instruction.
Import CPUISAOperandCut CPUISAOwnedEffects CPUOriginalISAReference CPUReferenceCuts
 CPUOwnedOperandReference CPURegisterEffectRelation.
Import CPUISAInstructionExecution CPUISACompositionalEffects CPUGeneratedJointTemplate.
Import CPUDecodedSourceBounds.
Local Open Scope Z_scope.
Definition requested_registers(i:Decode.InstructionI):list Z:=match i with
'''+ '\n'.join(arms)+'''
 | _=>[] end.
Definition requested_instruction(i:Decode.InstructionI):bool:=match i with
'''+ '\n'.join(supported)+'''
 | _=>false end.
Theorem requested_registers_agree i:requested_registers i=source_registers i.
Proof. destruct i;reflexivity. Qed.
Section Execution.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.
Lemma requested_translation_frame (before after:FormalSpec.State) access
 (alignment address value:word):
 Machine.translate access alignment address before=(Some value,after) ->after=before.
Proof. intro H;inversion H;reflexivity. Qed.
Theorem requested_reads (before after:FormalSpec.State) i:
 ExecuteI.execute i before=(Some tt,after) ->
 Forall (fun address=>exists value,Machine.getRegister address before=(Some value,before))
 (requested_registers i).
Proof.
 destruct i;intro H;cbn[requested_registers];try solve[exact(Forall_nil _)];
 cbn[ExecuteI.execute]in H;
 repeat match goal with
 | H:Bind _ _ _=(Some _,_) |- _ =>
   apply bind_success in H;
   let x:=fresh "v" in let s:=fresh "s" in let HX:=fresh "HX" in
   destruct H as[x [s [HX H]]]
 end;
 repeat match goal with
 | H:Machine.translate ?access ?alignment ?address ?b=(Some ?v,?a) |- _ =>
   first[constr_eq b a;fail 1|idtac];
   let HE:=fresh "HE" in pose proof(requested_translation_frame b a access alignment address v H)as HE;subst a
 | H:Machine.getRegister ?r ?b=(Some ?v,?a) |- _ =>
   first[constr_eq b a;fail 1|idtac];
   let HE:=fresh "HE" in pose proof(original_read_preserves b a r v H)as HE;subst a
 | H:Machine.getPC ?b=(Some ?v,?a) |- _ =>
   first[constr_eq b a;fail 1|idtac];
   let HE:=fresh "HE" in pose proof(original_pc_read_preserves b a v H)as HE;subst a
 end;
 cbn[requested_registers];
 repeat(apply Forall_cons;[eexists;eassumption|]);apply Forall_nil.
Qed.
Theorem requested_data_reads (before after:FormalSpec.State) i:
 data_operation i=true ->ExecuteI.execute i before=(Some tt,after) ->
 Forall (fun address=>exists value,Machine.getRegister address before=(Some value,before))
 (requested_registers i).
Proof. intros _ H;exact(requested_reads before after i H). Qed.
Theorem requested_values_at_pending_cut {Token:Type} (token_pc token_word:Token->Z)
 initial pending index token batches before reference after i:
 CertifiedBatches token_pc token_word initial batches before ->
 map fst batches=firstn index pending ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Forall(fun address=>0<=address<32)(requested_registers i) ->
 ExecuteI.execute i reference=(Some tt,after) ->
 Forall(fun address=>exists value,
   Machine.getRegister address reference=(Some value,reference) /\\
   word.unsigned value=
     if address=?0 then 0 else owner_value 32(ISAView initial)batches address)
 (requested_registers i).
Proof.
 intros HC HP HT HB HE.
 pose proof(requested_reads reference after i HE)as HR.
 apply Forall_forall;intros address HI.
 rewrite Forall_forall in HB,HR.
 destruct(HR address HI)as[value HV].
 exists value;split;[exact HV|].
 eapply operand_at_exact_pending_cut;[exact HC|exact HP|exact HT|exact(HB address HI)|exact HV].
Qed.
Theorem requested_token_values {Token:Type} (token_pc token_word:Token->Z)
 initial pending index token batches before reference after i:
 CertifiedBatches token_pc token_word initial batches before ->
 map fst batches=firstn index pending ->
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 instruction_effect token_pc token_word token reference=Some after ->
 Forall(fun address=>exists value,
   Machine.getRegister address reference=(Some value,reference) /\\
   word.unsigned value=
     if address=?0 then 0 else owner_value 32(ISAView initial)batches address)
 (requested_registers i).
Proof.
 intros HC HP HT HD HS.
 destruct(token_execute token_pc token_word token reference after i HS HD)as[middle [HE HEND]].
 eapply requested_values_at_pending_cut;[exact HC|exact HP|exact HT| |exact HE].
 pose proof(requested_reads reference middle i HE)as HR.
 eapply Forall_impl;[|exact HR].
 intros address [value HV];exact(read_address_bounds reference reference address value HV).
Qed.
Theorem requested_effects_from_history {Token:Type}(token_pc token_word:Token->Z)
 initial tokens final:
 EffectChain(instruction_effect token_pc token_word)initial tokens final ->
 Forall(fun token=>exists i,requested_instruction i=true /\\
   Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i)tokens ->
 exists batches,map fst batches=tokens /\\ CertifiedBatches token_pc token_word initial batches final.
Proof.
 intros HC HD;apply(certify_original_chain token_pc token_word initial tokens final HC).
 eapply Forall_impl;[|exact HD];intros token [i [_ HI]];exists i;exact HI.
Qed.
Theorem requested_values_from_history {Token:Type}(token_pc token_word:Token->Z)
 initial pending index token reference after i:
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 instruction_effect token_pc token_word token reference=Some after ->
 exists batches,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 Forall(fun address=>exists value,
   Machine.getRegister address reference=(Some value,reference) /\\
   word.unsigned value=if address=?0 then 0 else owner_value 32(ISAView initial)batches address)
 (requested_registers i).
Proof.
 intros HT HP _ HD HS.
 destruct HT as[HN [HB HC]].
 destruct(requested_effects_from_history token_pc token_word initial
   (firstn index pending)reference HC HP)as[batches [HM HE]].
 exists batches;split;[exact HM|];split;[exact HE|].
 eapply requested_token_values;[exact HE|exact HM| |exact HD|exact HS].
 split;[exact HN|split;assumption].
Qed.
Lemma legal_register_read (before:FormalSpec.State) address:
 0<=address<32 ->exists value,Machine.getRegister address before=(Some value,before).
Proof.
 intro HB;unfold Machine.getRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec address 0)as[HZ|HN].
 - exists(word.of_Z 0);reflexivity.
 - assert(HG:((0<?address)&&(address<?32))%bool=true).
   { apply andb_true_iff;split;apply Z.ltb_lt;lia. }
   rewrite HG;cbn[Bind Return OState_Monad OStateOperations.get].
   destruct(map.get(getRegs before)address)as[value|];eexists;reflexivity.
Qed.
Theorem requested_values_before_execution {Token:Type}(token_pc token_word:Token->Z)
 initial pending index token reference i:
 BeforeToken(instruction_effect token_pc token_word)initial pending index token reference ->
 Forall(fun older=>exists j,requested_instruction j=true /\\
   Decode.decode Decode.RV32I(token_word older)=Decode.IInstruction j)(firstn index pending) ->
 requested_instruction i=true ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 exists batches,map fst batches=firstn index pending /\\
 CertifiedBatches token_pc token_word initial batches reference /\\
 Forall(fun address=>exists value,
   Machine.getRegister address reference=(Some value,reference) /\\
   word.unsigned value=if address=?0 then 0 else owner_value 32(ISAView initial)batches address)
 (requested_registers i).
Proof.
 intros HT HP HI HD.
 assert(HB:Forall(fun address=>0<=address<32)(requested_registers i)).
 { rewrite requested_registers_agree;exact(decoded_source_bounds (token_word token) i HD). }
 destruct HT as[HN [Hlen HC]].
 destruct(requested_effects_from_history token_pc token_word initial
   (firstn index pending)reference HC HP)as[batches[HM HE]].
 exists batches;split;[exact HM|];split;[exact HE|].
 apply Forall_forall;intros address HA.
 rewrite Forall_forall in HB.
 destruct(legal_register_read reference address(HB address HA))as[value HV].
 exists value;split;[exact HV|].
 eapply operand_at_exact_pending_cut;[exact HE|exact HM| |exact(HB address HA)|exact HV].
 split;[exact HN|split;assumption].
Qed.
End Execution.
Print Assumptions requested_registers_agree.
Print Assumptions requested_translation_frame.
Print Assumptions requested_reads.
Print Assumptions requested_data_reads.
Print Assumptions requested_values_at_pending_cut.
Print Assumptions requested_token_values.
Print Assumptions requested_effects_from_history.
Print Assumptions requested_values_from_history.
Print Assumptions legal_register_read.
Print Assumptions requested_values_before_execution.
'''
    return plan,text


def assumptions_expected(log):
    names=[name for name in re.findall(r'^([A-Za-z_][\w.]*)\s*:',log,re.M)if name!='Axioms']
    return ('Closed under the global context'in log and log.count('Axioms:')==9
            and names==['FunctionalExtensionality.functional_extensionality_dep']*9)


def run(output, instruction_scope='rv32i38'):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    plan,source=render((synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text(),instruction_scope)
    path=output/'ISAInputs.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    flags=list(synthesis.origin.pending.rtl.framework.FLAGS)+['-R',str(output.resolve()),'GeneratedISAInputs']
    started=time.monotonic();deadline=started+1200
    c,t=run_stage([str(synthesis.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,old_inv_read=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        complete_R_generated=False,parameter_semantics_proved=False,
        pending_cut_values_generated=True,hardware_source_selection_proved=False,
        token_fetch_bound_values_generated=True,hardware_token_binding_proved=False,
        certified_prefix_generated_from_original_chain=True,
        pre_execution_reads_generated=True,current_instruction_success_required_for_reads=False,
        decoded_register_bounds_proved=False,
        register_argument_library_scope=38, instruction_scope=instruction_scope,
        selected_instruction_count=len(plan['instructions']),
        excluded_instructions=plan['excluded_instructions'],
        successful_execution_scope='requested_instruction restricts the history entry points; general read lemmas are not DUT coverage')
    if c.returncode==0 and time.monotonic()<deadline:
        report['expected_assumptions']=assumptions_expected(c.stdout)
        k,t=run_stage([str(synthesis.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
            'GeneratedISAInputs.ISAInputs'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                      accepted=k.returncode==0 and report['expected_assumptions'])
        report['decoded_register_bounds_proved']=report['accepted']
    report['seconds']=time.monotonic()-started
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True)
    p.add_argument('--instruction-scope',choices=scopes.SCOPES,default='rv32i38')
    a=p.parse_args();result=run(a.output,a.instruction_scope);print(json.dumps(result,indent=2))
    raise SystemExit(0 if result['accepted']else 1)
