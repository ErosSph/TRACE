(** Original ADDI success and execution frame. No RTL or CPU invariant. *)
From Coq Require Import ZArith Bool Lia.
Require Import Ex.RvCore.FormalSpec Ex.RvCore.Machine
 Ex.External.CV32E40PReq41Instruction Ex.External.CPUOriginalInstructionSuccess
 Ex.External.CPUOriginalADDFrontier Ex.External.CPUISAExecutionEffects
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUOriginalInstructionSuccess CPUOriginalADDFrontier CPUISAExecutionEffects.
Local Open Scope Z_scope.
Module CPUOriginalADDIFetchRules.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.

Theorem original_addi_run1_total (before:FormalSpec.State)rd rs imm:
 CV32E40PReq41Instruction.CurrentInstruction before(Decode.Addi rd rs imm) ->
 0<=rd<32 ->0<=rs<32 ->
 exists after,FormalSpec.run1 before=(Some tt,after).
Proof.
 intros HC HD HS.
 rewrite(CV32E40PReq41Instruction.run1_current_instruction before(Decode.Addi rd rs imm)HC).
 change(exists after,Bind(ExecuteI.execute(Decode.Addi rd rs imm))(fun _=>Machine.endCycleNormal)before=(Some tt,after)).
 destruct(original_read_total before rs HS)as[x HX].
 destruct(original_write_total before rd(Utility.add x(Utility.ZToReg imm))HD)as[middle HM].
 destruct(original_end_cycle_total middle)as[after HA].
 exists after;change((let '(result,updated):=Bind(Machine.getRegister rs)
 (fun value=>Machine.setRegister rd(Utility.add value(Utility.ZToReg imm)))before in
 match result with Some _=>Machine.endCycleNormal updated|None=>(None,updated)end)=(Some tt,after)).
 cbn[Bind OState_Monad];rewrite HX,HM;exact HA.
Qed.

Theorem original_addi_execution_frame(before after:FormalSpec.State)rd rs imm:
 ExecuteI.execute(Decode.Addi rd rs imm)before=(Some tt,after) ->MemoryPCFrame before after.
Proof.
 change(Bind(Machine.getRegister rs)(fun x=>Machine.setRegister rd(Utility.add x(Utility.ZToReg imm)))before
 =(Some tt,after) ->MemoryPCFrame before after).
 intro H;apply bind_success in H;destruct H as[x[middle[HX H]]].
 pose proof(original_read_preserves before middle rs x HX);subst middle.
 exact(original_write_frame before after rd(Utility.add x(Utility.ZToReg imm))H).
Qed.
End ISA.
End CPUOriginalADDIFetchRules.
Print Assumptions CPUOriginalADDIFetchRules.original_addi_run1_total.
Print Assumptions CPUOriginalADDIFetchRules.original_addi_execution_frame.
