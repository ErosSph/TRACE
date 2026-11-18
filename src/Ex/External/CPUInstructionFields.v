(** ISA field layout transport for actual RTL expressions. A bit-layout
    certificate does NOT identify its source word as the current ISA token. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVBankAlignment
 Lang.ExtendedSVWordInvariant Ex.External.CPUPhysicalRegisterFile coqutil.Z.BitOps.
Import ExtendedSV ExtendedSVBitSlice ExtendedSVBankAlignment ExtendedSVWordInvariant
 CPUPhysicalRegisterFile.
Local Open Scope Z_scope.
Module CPUInstructionFields.
Inductive Field := Rd | Rs1 | Rs2 | Opcode | Funct3 | Funct7.
Definition field_width field : nat := match field with
 | Rd|Rs1|Rs2=>5 | Opcode|Funct7=>7 | Funct3=>3 end.
Definition field_offset field : nat := match field with
 | Rd=>7 | Rs1=>15 | Rs2=>20 | Opcode=>0 | Funct3=>12 | Funct7=>25 end.
Definition field_expr source field := ESel (field_width field) (EVar 32 source)
 (EConst 5 (Z.of_nat(field_offset field))).
Definition field_reference word field := BitOps.bitSlice word
 (Z.of_nat(field_offset field)) (Z.of_nat(field_offset field+field_width field)).

Lemma read_slice_reference value offset width : 0<=offset ->0<=width ->
 read_slice value offset width=BitOps.bitSlice value offset (offset+width).
Proof.
 intros HO HW. unfold read_slice.
 replace (2^width-1) with (Z.ones width) by (rewrite Z.ones_equiv;reflexivity).
 rewrite Z.land_ones by exact HW.
 rewrite BitOps.bitSlice_alt by lia. unfold BitOps.bitSlice'.
 replace (offset+width-offset) with width by lia.
 rewrite <-Z.shiftr_div_pow2 by exact HO. reflexivity.
Qed.

Lemma native_slice_reference s source width offset :
 (0<width)%nat ->(offset+width<=32)%nat ->
 eval_expr s (ESel width (EVar 32 source) (EConst 5 (Z.of_nat offset)))=
 BitOps.bitSlice (read_signal s source) (Z.of_nat offset) (Z.of_nat(offset+width)).
Proof.
 intros HW HO. cbn [eval_expr].
 assert (HC:norm 5 (Z.of_nat offset)=Z.of_nat offset).
 { rewrite norm_mod. apply Z.mod_small. cbn. lia. }
 rewrite HC.
 change (read_slice(norm 32(read_signal s source))(Z.of_nat offset)(Z.of_nat width)=
  BitOps.bitSlice(read_signal s source)(Z.of_nat offset)(Z.of_nat(offset+width))).
 rewrite read_slice_normalized_inside by lia.
 rewrite Nat2Z.inj_add. apply read_slice_reference;lia.
Qed.

Theorem field_value s source field :
 eval_expr s (field_expr source field)=field_reference (read_signal s source) field.
Proof. unfold field_expr,field_reference. apply native_slice_reference;
 destruct field;cbn;lia. Qed.

Lemma eval_is_normalized s expression :
 norm (expr_width expression) (eval_expr s expression)=eval_expr s expression.
Proof. destruct expression;cbn [expr_width eval_expr];apply norm_idempotent. Qed.

Theorem native_field_reference s source field :
 norm (field_width field) (eval_expr s (field_expr source field))=
 field_reference (read_signal s source) field.
Proof.
 rewrite <-field_value. change(norm(expr_width(field_expr source field))
  (eval_expr s(field_expr source field))=eval_expr s(field_expr source field)).
 apply eval_is_normalized.
Qed.

Theorem widened_field_reference s source field :
 norm 32 (eval_expr s (EExtend 32 false (field_expr source field)))=
 field_reference (read_signal s source) field.
Proof.
 cbn [eval_expr]. rewrite norm_idempotent.
 fold (eval_expr s (field_expr source field)). rewrite field_value.
 assert (HB:0<=field_reference(read_signal s source)field<2^Z.of_nat(field_width field)).
 { rewrite <-field_value. exact (eval_bounds s (field_expr source field)). }
 rewrite norm_mod. apply Z.mod_small. destruct field;cbn [field_width] in HB.
 all: cbn;lia.
Qed.
End CPUInstructionFields.
Print Assumptions CPUInstructionFields.read_slice_reference.
Print Assumptions CPUInstructionFields.native_slice_reference.
Print Assumptions CPUInstructionFields.field_value.
Print Assumptions CPUInstructionFields.native_field_reference.
Print Assumptions CPUInstructionFields.widened_field_reference.
