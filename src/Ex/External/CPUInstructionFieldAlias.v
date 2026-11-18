(** Bit-layout transport across checked normalized 32-bit word aliases. *)
From Coq Require Import ZArith Lia.
Require Import Ex.External.CPUInstructionFields Ex.External.CPUPhysicalRegisterFile.
Import CPUInstructionFields CPUPhysicalRegisterFile.
Module CPUInstructionFieldAlias.
Lemma field_reference_normalized value field :
 field_reference (ExtendedSV.ExtendedSV.norm 32 value) field=field_reference value field.
Proof.
 unfold field_reference. rewrite !Nat2Z.inj_add.
 rewrite <-!read_slice_reference by lia.
 apply read_slice_normalized_inside;destruct field;cbn;lia.
Qed.
Theorem field_reference_alias x y field :
 ExtendedSV.ExtendedSV.norm 32 x=ExtendedSV.ExtendedSV.norm 32 y ->
 field_reference x field=field_reference y field.
Proof.
 intro H. rewrite <-(field_reference_normalized x field),
 <-(field_reference_normalized y field). now rewrite H.
Qed.
End CPUInstructionFieldAlias.
Print Assumptions CPUInstructionFieldAlias.field_reference_normalized.
Print Assumptions CPUInstructionFieldAlias.field_reference_alias.
