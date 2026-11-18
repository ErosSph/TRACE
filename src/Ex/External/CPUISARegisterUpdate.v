(** ISA-side register effect extraction rules. No DUT, CPU invariant, or
    expected RTL result is imported. The map equality must be obtained from
    the original ISA execution; these rules do not assert run1 success. *)
From Coq Require Import ZArith List Lia.
Require Import Ex.External.CPURegisterEffectRelation Ex.External.PicoISARF
 Lang.ExtendedSV Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility
 Ex.RvCore.FormalSpec Ex.RvCore.Machine riscv.Utility.Monads.
Import ListNotations ExtendedSV ExtendedSVRegisterBank
 ExtendedSVBankAlignment CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPUISARegisterUpdate.
Section Rules.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.

Definition register_operations (rd:Z) (value:word):list BankOperation :=
 if rd=?0 then [] else [WriteLane rd (word.unsigned value)].

Lemma unsigned_normalized (value:word):
 norm 32 (word.unsigned value)=word.unsigned value.
Proof. rewrite norm_mod;apply Z.mod_small;apply word.unsigned_range. Qed.

Lemma unchanged_registers (before after:FormalSpec.State):
 getRegs after=getRegs before -> ISAProjectedRegisterEffects before after [].
Proof.
 intros HE i HI;unfold ISAView,PicoISARF.isa_value,project_x0,operation_effects32;cbn[operation_effects].
 rewrite HE;destruct(i=?0);reflexivity.
Qed.

Lemma updated_registers (before after:FormalSpec.State) rd (value:word):
 getRegs after=(if Z.eq_dec rd 0 then getRegs before
               else map.put (getRegs before) rd value) ->
 ISAProjectedRegisterEffects before after (register_operations rd value).
Proof.
 intros HE;unfold register_operations;destruct(rd=?0)eqn:HZ.
 - apply Z.eqb_eq in HZ;subst rd;apply unchanged_registers;exact HE.
 - apply Z.eqb_neq in HZ;destruct(Z.eq_dec rd 0);[contradiction|].
   intros i HI;unfold ISAView,PicoISARF.isa_value,project_x0,operation_effects32;
   cbn[operation_effects operation_effect abstract_write].
   rewrite HE;destruct(Z.eq_dec rd 0);[contradiction|].
   destruct(i=?0)eqn:HI0;[reflexivity|].
   unfold abstract_write;rewrite HI0.
   change ((match map.get (map.put (getRegs before) rd value) i with
     |Some v=>word.unsigned v|None=>0 end)=
     if i=?rd then norm 32(word.unsigned value)
     else match map.get(getRegs before)i with Some v=>word.unsigned v|None=>0 end).
   destruct(i=?rd)eqn:HD.
   + apply Z.eqb_eq in HD;subst i;rewrite map.get_put_same,unsigned_normalized;reflexivity.
   + apply Z.eqb_neq in HD;rewrite map.get_put_diff by congruence;reflexivity.
Qed.

(** This is compositional: ISA programs with more than one write use the
    same append rule as hardware-side chronological operations. *)
Lemma append_updates (before middle after:FormalSpec.State) rd value operations:
 getRegs middle=(if Z.eq_dec rd 0 then getRegs before
                 else map.put(getRegs before)rd value) ->
 ISAProjectedRegisterEffects middle after operations ->
 ISAProjectedRegisterEffects before after(register_operations rd value++operations).
Proof. intros HE HR;eapply isa_projected_effects_append;[apply updated_registers;exact HE|exact HR]. Qed.

Theorem original_set_register (before after:FormalSpec.State) rd value:
 Machine.setRegister rd value before=(Some tt,after) ->
 ISAProjectedRegisterEffects before after(register_operations rd value).
Proof.
 unfold Machine.setRegister;cbn[IsRiscvProgram].
 destruct(Z.eq_dec rd 0)as[HZ|HN].
 - subst rd;intro HE;inversion HE;subst after.
   apply updated_registers;reflexivity.
 - destruct((0<?rd)&&(rd<?32))%bool eqn:HB.
   + destruct before as[regs pc npc imem dmem];cbn[update Bind Return OState_Monad
       OStateOperations.get OStateOperations.put withRegs].
     intro HE;inversion HE;subst after;apply updated_registers;
     cbn[getRegs];destruct(Z.eq_dec rd 0);congruence.
   + intro HE;discriminate HE.
Qed.
End Rules.

(** Rule-based extraction from an actual primitive execution fact. This
    produces the operation list as well as its proof; it never searches a
    CPU invariant database. Other ISA primitives intentionally remain goals. *)
Ltac extract_register_operations :=
 match goal with
 | H : Machine.setRegister ?rd ?v ?before = (Some tt, ?after)
   |- exists operations, ISAProjectedRegisterEffects ?before ?after operations =>
     exists (register_operations rd v);exact (original_set_register before after rd v H)
 | H : getRegs ?after = getRegs ?before
   |- exists operations, ISAProjectedRegisterEffects ?before ?after operations =>
     exists [];exact (unchanged_registers before after H)
 end.

Section Regression.
Context {word:Interface.word 32}{BW:Bitwidth 32}{MW:MachineWidth word}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.
Example automatic_original_write (before after:FormalSpec.State) rd value:
 Machine.setRegister rd value before=(Some tt,after) ->
 exists operations, ISAProjectedRegisterEffects before after operations.
Proof. intro H;extract_register_operations. Qed.
Example automatic_original_frame (before after:FormalSpec.State):
 getRegs after=getRegs before ->
 exists operations, ISAProjectedRegisterEffects before after operations.
Proof. intro H;extract_register_operations. Qed.
End Regression.
End CPUISARegisterUpdate.
Print Assumptions CPUISARegisterUpdate.updated_registers.
Print Assumptions CPUISARegisterUpdate.append_updates.
Print Assumptions CPUISARegisterUpdate.original_set_register.
Print Assumptions CPUISARegisterUpdate.automatic_original_write.
