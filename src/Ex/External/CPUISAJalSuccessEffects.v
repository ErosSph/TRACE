(** Extract JAL register effects from successful ORIGINAL execution.
    In particular, successful execution already selects the non-exception
    branch. No target-alignment premise or hardware invariant is imported. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterEffectRelation
 Ex.External.CPUOriginalISAReference Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface
 coqutil.Byte riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISAInstructionExecution CPUISAExecutionEffects CPUISARegisterUpdate
 CPURegisterEffectRelation CPUOriginalISAReference.

Module CPUISAJalSuccessEffects.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Theorem set_pc_register_frame (before after:FormalSpec.State) target:
 Machine.setPC target before=(Some tt,after) ->getRegs after=getRegs before.
Proof. destruct before;intro H;inversion H;reflexivity. Qed.

Theorem original_jal_effect (before after:FormalSpec.State) rd imm:
 ExecuteI.execute(Decode.Jal rd imm)before=(Some tt,after) ->
 ISAProjectedRegisterEffects before after
  (register_operations rd(word.add(getPc before)(word.of_Z 4))).
Proof.
 intro H;cbn[ExecuteI.execute]in H.
 apply bind_success in H;destruct H as[pc[middle[HP H]]].
 pose proof(original_pc_read_preserves before middle pc HP);subst middle.
 assert(HPC:pc=getPc before)by(inversion HP;reflexivity);subst pc.
 cbv beta zeta in H.
 match type of H with context[if ?guard then _ else _]=>destruct guard eqn:HG end.
 - discriminate H.
 - apply bind_success in H;destruct H as[[] [written[HW HT]]].
   pose proof(original_set_register before written rd
    (word.add(getPc before)(word.of_Z 4))HW)as HR.
   intros address HA;unfold ISAView.
   rewrite(set_pc_register_frame written after _ HT);exact(HR address HA).
Qed.

Context {Token:Type}.
Variables token_pc token_word:Token->Z.
Theorem original_token_jal_effect token before after rd imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 ISAProjectedRegisterEffects before after
  (register_operations rd(word.add(getPc before)(word.of_Z 4))).
Proof.
 intros HS HD.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 pose proof(original_jal_effect before middle rd imm HE)as HR.
 intros address HA;unfold ISAView.
 rewrite(end_cycle_register_frame middle after HEnd);exact(HR address HA).
Qed.
End ISA.
End CPUISAJalSuccessEffects.
Print Assumptions CPUISAJalSuccessEffects.set_pc_register_frame.
Print Assumptions CPUISAJalSuccessEffects.original_jal_effect.
Print Assumptions CPUISAJalSuccessEffects.original_token_jal_effect.
