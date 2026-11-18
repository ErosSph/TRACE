(** ISA x0 suppression and a concrete physical lane write have the same
    architectural effect. The physical result value still needs a proof. *)
From Coq Require Import ZArith List.
Require Import Ex.External.CPUISARegisterUpdate Ex.External.CPURegisterEffectRelation
 Ex.RvCore.FormalSpec Lang.ExtendedSV Lang.ExtendedSVRegisterBank
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte.
Import ListNotations ExtendedSV ExtendedSVRegisterBank CPUISARegisterUpdate CPURegisterEffectRelation.
Local Open Scope Z_scope.
Module CPURegisterWritebackValue.
Section ISA.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}.

Theorem register_operations_as_lane (before after:FormalSpec.State) rd (value:word) actual:
 ISAProjectedRegisterEffects before after(register_operations rd value) ->
 norm 32 actual=word.unsigned value ->
 ISAProjectedRegisterEffects before after[WriteLane rd actual].
Proof.
 intros HE HV i HI;rewrite(HE i HI).
 unfold register_operations,project_x0,operation_effects32.
 destruct(rd=?0)eqn:HD;cbn[operation_effects operation_effect abstract_write];
 destruct(i=?0)eqn:HZ;[reflexivity| |reflexivity|].
 - apply Z.eqb_eq in HD;subst rd.
   change(ISAView before i=(if i=?0 then norm 32 actual else ISAView before i)).
   now rewrite HZ.
 - change((if i=?rd then norm 32(word.unsigned value)else ISAView before i)=
     (if i=?rd then norm 32 actual else ISAView before i)).
   rewrite HV,unsigned_normalized;reflexivity.
Qed.

Example zero_write_is_not_an_architectural_update (before after:FormalSpec.State) actual:
 ISAProjectedRegisterEffects before after[] ->
 ISAProjectedRegisterEffects before after[WriteLane 0 actual].
Proof.
 intros HE i HI;rewrite(HE i HI);unfold project_x0,operation_effects32;
 cbn[operation_effects operation_effect];unfold abstract_write;destruct(i=?0);reflexivity.
Qed.
End ISA.
End CPURegisterWritebackValue.
Print Assumptions CPURegisterWritebackValue.register_operations_as_lane.
Print Assumptions CPURegisterWritebackValue.zero_write_is_not_an_architectural_update.
