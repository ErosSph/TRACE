(** Unary original-ISA effects, including ADDI; no hardware or CPU INV. *)
From Coq Require Import ZArith.
Require Import Ex.External.CPUISAExecutionEffects Ex.External.CPUISARegisterUpdate
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec Ex.RvCore.Machine
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Monads riscv.Utility.Utility riscv.Spec.ExecuteI.
Import CPUISAExecutionEffects CPUISARegisterUpdate CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUISAAddiEffects.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Theorem unary_register_effect (before after:FormalSpec.State) rd rs
 (f:word->word):
 Bind(Machine.getRegister rs)(fun x=>Machine.setRegister rd(f x))before=(Some tt,after) ->
 exists x,Machine.getRegister rs before=(Some x,before) /\
 ISAProjectedRegisterEffects before after(register_operations rd(f x)).
Proof.
 intro H;apply bind_success in H;destruct H as[x [middle [HX H]]].
 pose proof(original_read_preserves before middle rs x HX);subst middle.
 exists x;split;[exact HX|now apply original_set_register].
Qed.

Theorem original_addi_effect (before after:FormalSpec.State) rd rs imm:
 ExecuteI.execute(Decode.Addi rd rs imm)before=(Some tt,after) ->
 exists x,Machine.getRegister rs before=(Some x,before) /\
 ISAProjectedRegisterEffects before after
  (register_operations rd(Utility.add x(Utility.ZToReg imm))).
Proof. apply unary_register_effect. Qed.
End ISA.
End CPUISAAddiEffects.
Print Assumptions CPUISAAddiEffects.unary_register_effect.
Print Assumptions CPUISAAddiEffects.original_addi_effect.
