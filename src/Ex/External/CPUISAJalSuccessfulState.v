(** Original successful JAL's PC/ROM/RAM fields, without an additional
    alignment hypothesis. Success eliminates the original exception branch. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUISAInstructionExecution Ex.External.CPUISAExecutionEffects
 Ex.External.CPUOriginalISAReference Ex.External.CPUOriginalADDFrontier
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISAInstructionExecution CPUISAExecutionEffects CPUOriginalISAReference CPUOriginalADDFrontier.
Module CPUISAJalSuccessfulState.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.
Theorem set_pc_fields (before after:FormalSpec.State) target:
 Machine.setPC target before=(Some tt,after) ->
 getPc after=getPc before /\getNextPc after=target /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof. destruct before;intro H;inversion H;repeat split;reflexivity. Qed.

Theorem successful_jal_fields (before after:FormalSpec.State) rd imm:
 ExecuteI.execute(Decode.Jal rd imm)before=(Some tt,after) ->
 getPc after=getPc before /\getNextPc after=word.add(getPc before)(word.of_Z imm) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof.
 intro H;cbn[ExecuteI.execute]in H.
 apply bind_success in H;destruct H as[pc[middle[HP H]]].
 pose proof(original_pc_read_preserves before middle pc HP);subst middle.
 assert(HPC:pc=getPc before)by(inversion HP;reflexivity);subst pc.
 cbv beta zeta in H.
 match type of H with context[if ?guard then _ else _]=>destruct guard eqn:HG end.
 - discriminate H.
 - apply bind_success in H;destruct H as[[] [written[HW HT]]].
   destruct(original_write_frame before written rd(word.add(getPc before)(word.of_Z 4))HW)
    as[HPCFrame[HN[HI HM]]].
   destruct(set_pc_fields written after(word.add(getPc before)(word.of_Z imm))HT)
    as[HP'[HN'[HI' HM']]].
   exact(conj(eq_trans HP' HPCFrame)(conj HN'(conj(eq_trans HI' HI)(eq_trans HM' HM)))).
Qed.

Theorem successful_token_jal_fields {Token:Type}(token_pc token_word:Token->Z)
 token before after rd imm:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 getPc after=word.add(getPc before)(word.of_Z imm) /\
 getNextPc after=word.add(getPc after)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof.
 intros HS HD.
 destruct(token_execute token_pc token_word token before after _ HS HD)as[middle[HE HEnd]].
 destruct(successful_jal_fields before middle rd imm HE)as[HP[HN[HI HM]]].
 destruct(original_end_cycle_frontier middle after HEnd)as[HP'[HN'[HI' HM']]].
 exact(conj(eq_trans HP' HN)(conj
  (eq_trans HN'(f_equal(fun pc=>word.add pc(word.of_Z 4))(eq_sym HP')))
  (conj(eq_trans HI' HI)(eq_trans HM' HM)))).
Qed.
End ISA.
End CPUISAJalSuccessfulState.
Print Assumptions CPUISAJalSuccessfulState.set_pc_fields.
Print Assumptions CPUISAJalSuccessfulState.successful_jal_fields.
Print Assumptions CPUISAJalSuccessfulState.successful_token_jal_fields.
