(** Packed physical RF -> ALL 32 ISA registers. Pure, architecture-independent
    update facts; no CPU/ISA correctness premise and no trace expected override. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Ex.External.CPUArrayContracts
 coqutil.Map.Interface coqutil.Word.Interface.
Import ExtendedSV ExtendedSVBitSlice CPUArrayContracts.
Local Open Scope Z_scope.
Module PicoISARF.
Section Architecture.
Context {word:Interface.word 32} {Registers:map.map Z word}.
Context {word_ok:word.ok word} {registers_ok:map.ok Registers}.
Definition isa_value (regs:Registers) index := if index =? 0 then 0 else
 match map.get regs index with Some v=>word.unsigned v | None=>0 end.
Definition rtl_value bank index := if index =? 0 then 0 else bank_read 32 bank index.
Definition RFRelated bank regs := forall index,0<=index<32 ->
 rtl_value bank index=isa_value regs index.
Lemma zero_bank_related : RFRelated 0 map.empty.
Proof.
 intros index Hindex. unfold rtl_value,isa_value. destruct(index =? 0);[reflexivity|].
 rewrite map.get_empty. unfold bank_read,read_slice. rewrite Z.shiftr_0_l,Z.land_0_l.
 reflexivity.
Qed.
Theorem write_restores_all_lanes bank regs rd data value :
 RFRelated bank regs -> 0<rd<32 -> word.unsigned value=norm 32 data ->
 RFRelated (bank_write 32 bank rd data) (map.put regs rd value).
Proof.
 intros Hrelated Hrd Hvalue index Hindex. unfold rtl_value,isa_value.
 destruct(index =? 0) eqn:Hz;[reflexivity|].
 destruct(Z.eq_dec rd index) as [Heq|Hneq].
 - subst index. rewrite map.get_put_same,write_read_same by lia.
   unfold read_slice. rewrite Z.shiftr_0_r. symmetry. exact Hvalue.
 - rewrite map.get_put_diff by congruence. rewrite write_read_other by lia.
   specialize(Hrelated index Hindex). unfold rtl_value,isa_value in Hrelated.
   rewrite Hz in Hrelated. exact Hrelated.
Qed.
End Architecture.
Print Assumptions write_restores_all_lanes.
End PicoISARF.
