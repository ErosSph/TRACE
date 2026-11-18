(** Frontier fields of the ORIGINAL ADD execution; no replacement ISA step. *)
From Coq Require Import ZArith Bool.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CPUISAExecutionEffects Ex.External.CPUISAInstructionExecution
 Ex.External.CPUOriginalISAReference coqutil.Word.Interface coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Monads riscv.Spec.ExecuteI.
Import CPUISAExecutionEffects CPUISAInstructionExecution CPUOriginalISAReference.
Local Open Scope Z_scope.
Module CPUOriginalADDFrontier.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Definition MemoryPCFrame(before after:FormalSpec.State):=
 getPc after=getPc before /\getNextPc after=getNextPc before /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.

Lemma original_write_frame(before after:FormalSpec.State)rd value:
 Machine.setRegister rd value before=(Some tt,after) ->MemoryPCFrame before after.
Proof. unfold Machine.setRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec rd 0);[intro H;inversion H;subst;repeat split;reflexivity|].
 destruct((0<?rd)&&(rd<?32))%bool;[|discriminate].
 destruct before;intro H;inversion H;subst;repeat split;reflexivity. Qed.

Lemma original_end_cycle_frontier(before after:FormalSpec.State):
 Machine.endCycleNormal before=(Some tt,after) ->
 getPc after=getNextPc before /\
 getNextPc after=word.add(getNextPc before)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof. destruct before;intro H;inversion H;repeat split;reflexivity. Qed.

Lemma original_add_execution_frame(before after:FormalSpec.State)rd rs1 rs2:
 ExecuteI.execute(Decode.Add rd rs1 rs2)before=(Some tt,after) ->MemoryPCFrame before after.
Proof.
 change(Bind(Machine.getRegister rs1)(fun x=>Bind(Machine.getRegister rs2)
 (fun y=>Machine.setRegister rd(Utility.add x y)))before=(Some tt,after) ->MemoryPCFrame before after).
 intro H;apply bind_success in H;destruct H as[x[s1[HX H]]].
 pose proof(original_read_preserves before s1 rs1 x HX);subst s1.
 apply bind_success in H;destruct H as[y[s2[HY H]]].
 pose proof(original_read_preserves before s2 rs2 y HY);subst s2.
 exact(original_write_frame before after rd(Utility.add x y)H). Qed.

Theorem original_token_ADD_frontier{Token:Type}(pc code:Token->Z)token
 (before after:FormalSpec.State)rd rs1 rs2:
 instruction_effect pc code token before=Some after ->
 Decode.decode Decode.RV32I(code token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 getPc after=getNextPc before /\
 getNextPc after=word.add(getPc after)(word.of_Z 4) /\
 getInstMem after=getInstMem before /\getDataMem after=getDataMem before.
Proof. intros HS HD.
 destruct(token_execute pc code token before after(Decode.Add rd rs1 rs2)HS HD)as[middle[HX HE]].
 destruct(original_add_execution_frame before middle rd rs1 rs2 HX)as[HPC[HN[HI HM]]].
 destruct(original_end_cycle_frontier middle after HE)as[HP[HNext[HInst HData]]].
 exact(conj(eq_trans HP HN)(conj
 (eq_trans HNext(f_equal(fun x=>word.add x(word.of_Z 4))(eq_sym HP)))
 (conj(eq_trans HInst HI)(eq_trans HData HM)))). Qed.
End ISA.
End CPUOriginalADDFrontier.
Print Assumptions CPUOriginalADDFrontier.original_write_frame.
Print Assumptions CPUOriginalADDFrontier.original_end_cycle_frontier.
Print Assumptions CPUOriginalADDFrontier.original_add_execution_frame.
Print Assumptions CPUOriginalADDFrontier.original_token_ADD_frontier.
