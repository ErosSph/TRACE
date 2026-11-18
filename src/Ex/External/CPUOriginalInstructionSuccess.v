(** Totality of original ISA primitives at legal register numbers.
    This library does not assume a CPU invariant or an ISA post-state. *)
From Coq Require Import ZArith Bool Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CV32E40PReq41Instruction coqutil.Word.Interface coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte riscv.Utility.Monads riscv.Spec.ExecuteI.
Local Open Scope Z_scope.
Module CPUOriginalInstructionSuccess.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Lemma original_read_total (before:FormalSpec.State) address:
 0<=address<32 ->exists value,Machine.getRegister address before=(Some value,before).
Proof.
 intro HB;unfold Machine.getRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec address 0)as[HZ|HN];[eexists;reflexivity|].
 assert(HT:((0<?address)&&(address<?32))%bool=true).
 { apply andb_true_iff;split;apply Z.ltb_lt;lia. }
 rewrite HT;cbn[Bind Return OState_Monad OStateOperations.get].
 destruct(map.get(getRegs before)address);eexists;reflexivity.
Qed.

Lemma original_write_total (before:FormalSpec.State) address value:
 0<=address<32 ->exists after,Machine.setRegister address value before=(Some tt,after).
Proof.
 intro HB;unfold Machine.setRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec address 0)as[HZ|HN];[eexists;reflexivity|].
 assert(HT:((0<?address)&&(address<?32))%bool=true).
 { apply andb_true_iff;split;apply Z.ltb_lt;lia. }
 rewrite HT;eexists;reflexivity.
Qed.

Theorem original_binary_total (before:FormalSpec.State) rd rs1 rs2(f:word->word->word):
 0<=rd<32 ->0<=rs1<32 ->0<=rs2<32 ->
 exists middle,Bind(Machine.getRegister rs1)(fun x=>
 Bind(Machine.getRegister rs2)(fun y=>Machine.setRegister rd(f x y)))before=(Some tt,middle).
Proof.
 intros HD H1 H2.
 destruct(original_read_total before rs1 H1)as[x HX].
 destruct(original_read_total before rs2 H2)as[y HY].
 destruct(original_write_total before rd(f x y)HD)as[middle HM].
 exists middle;cbn[Bind OState_Monad];rewrite HX,HY;exact HM.
Qed.

Lemma original_end_cycle_total (before:FormalSpec.State):
 exists after,Machine.endCycleNormal before=(Some tt,after).
Proof. destruct before;eexists;reflexivity. Qed.

Theorem original_add_run1_total {mem_ok:map.ok Mem}(before:FormalSpec.State)rd rs1 rs2:
 CV32E40PReq41Instruction.CurrentInstruction before(Decode.Add rd rs1 rs2) ->
 0<=rd<32 ->0<=rs1<32 ->0<=rs2<32 ->
 exists after,FormalSpec.run1 before=(Some tt,after).
Proof.
 intros HC HD H1 H2.
 rewrite(CV32E40PReq41Instruction.run1_current_instruction before(Decode.Add rd rs1 rs2)HC).
 change(exists after,Bind(ExecuteI.execute(Decode.Add rd rs1 rs2))(fun _=>Machine.endCycleNormal)before=(Some tt,after)).
 destruct(original_binary_total before rd rs1 rs2 Utility.add HD H1 H2)as[middle HM].
 destruct(original_end_cycle_total middle)as[after HA].
 exists after;change((let '(result,updated):=Bind(Machine.getRegister rs1)(fun x=>
 Bind(Machine.getRegister rs2)(fun y=>Machine.setRegister rd(Utility.add x y)))before in
 match result with Some _=>Machine.endCycleNormal updated|None=>(None,updated)end)=(Some tt,after)).
 rewrite HM;exact HA.
Qed.
End ISA.
End CPUOriginalInstructionSuccess.
Print Assumptions CPUOriginalInstructionSuccess.original_read_total.
Print Assumptions CPUOriginalInstructionSuccess.original_write_total.
Print Assumptions CPUOriginalInstructionSuccess.original_binary_total.
Print Assumptions CPUOriginalInstructionSuccess.original_end_cycle_total.
Print Assumptions CPUOriginalInstructionSuccess.original_add_run1_total.
