(** For CPUs whose source mux reads physical bank lane0 without masking it.
 Architectural x0 masking alone is insufficient; expose the extra invariant. *)
From Coq Require Import ZArith Lia Bool.
Require Import Ex.External.CPUArrayContracts Ex.External.PicoISARF
 Lang.ExtendedSV Lang.ExtendedSVBitSlice coqutil.Map.Interface coqutil.Word.Interface.
Import CPUArrayContracts PicoISARF ExtendedSV ExtendedSVBitSlice.
Local Open Scope Z_scope.
Module CPUPhysicalRegisterFile.
(** Pure bit-slice fact extracted from the old Pico connection: no Pico AST
 or runtime dependency is needed by consumers of this module. *)
Lemma read_slice_normalized_inside packed offset width total :
 0<=offset ->0<=width ->offset+width<=Z.of_nat total ->
 read_slice(norm total packed)offset width=read_slice packed offset width.
Proof.
 intros HO HW HT. apply Z.bits_inj. intro bit.
 destruct(Z_lt_ge_dec bit 0)as[HN|HN].
 - rewrite !Z.testbit_neg_r by lia. reflexivity.
 - unfold read_slice,norm,mask. rewrite !Z.land_spec.
   destruct(Z_lt_ge_dec bit width)as[HL|HH].
   + rewrite mask_bit_low by lia. rewrite !Bool.andb_true_r,!Z.shiftr_spec by lia.
     rewrite Z.land_spec,mask_bit_low by lia. rewrite Bool.andb_true_r. reflexivity.
   + rewrite mask_bit_high by lia. rewrite !Bool.andb_false_r. reflexivity.
Qed.
Lemma bank_normalization_preserves_legal_lane bank index :0<=index<32 ->
 bank_read 32(norm 1024 bank)index=bank_read 32 bank index.
Proof. intro HI. unfold bank_read. apply read_slice_normalized_inside;lia. Qed.
Section Architecture.
Context {word:Interface.word 32}{Registers:map.map Z word}.
Context {word_ok:word.ok word}{registers_ok:map.ok Registers}.
Definition PhysicalRFRelated bank regs := forall index,0<=index<32 ->
 bank_read 32 bank index=isa_value regs index.
Theorem physical_relation_iff bank regs :
 PhysicalRFRelated bank regs <-> RFRelated bank regs /\ bank_read 32 bank 0=0.
Proof.
 split.
 - intro H. split.
   + intros index HI. unfold rtl_value,isa_value.
     destruct(index=?0)eqn:HE;[reflexivity|].
     specialize(H index HI). unfold isa_value in H. rewrite HE in H. exact H.
   + specialize(H 0 ltac:(lia)). exact H.
 - intros [HA Hzero] index HI.
   destruct(Z.eq_dec index 0)as[->|HN].
   + exact Hzero.
   + specialize(HA index HI). unfold rtl_value in HA.
     assert(HE:(index=?0)=false)by(now apply Z.eqb_neq).
     rewrite HE in HA.
     exact HA.
Qed.
Theorem zero_physical_rf : PhysicalRFRelated 0 map.empty.
Proof.
 apply physical_relation_iff. split;[apply zero_bank_related|].
 unfold bank_read,ExtendedSVBitSlice.read_slice.
 rewrite Z.shiftr_0_l,Z.land_0_l. reflexivity.
Qed.
Theorem nonzero_write_preserves_physical bank regs rd data value :
 PhysicalRFRelated bank regs ->0<rd<32 ->word.unsigned value=norm 32 data ->
 PhysicalRFRelated(bank_write 32 bank rd data)(map.put regs rd value).
Proof.
 intros HR HD HV. apply physical_relation_iff in HR as[HA Hzero].
 apply physical_relation_iff. split.
 - apply write_restores_all_lanes;assumption.
 - rewrite write_read_other by lia. exact Hzero.
Qed.
End Architecture.
Theorem actual_write_port_preserves_zero bank rd data :
 bank_read 32 bank 0=0 ->0<=rd ->
 bank_read 32(bank_write 32 bank rd(if rd=?0 then 0 else data))0=0.
Proof.
 intros Hzero HD. destruct(Z.eq_dec rd 0)as[->|HN].
 - change(bank_read 32(bank_write 32 bank 0 0)0=0).
   rewrite write_read_same by lia.
   unfold ExtendedSVBitSlice.read_slice. reflexivity.
 - assert(HE:(rd=?0)=false)by(now apply Z.eqb_neq).
   rewrite HE,write_read_other by lia. exact Hzero.
Qed.
End CPUPhysicalRegisterFile.
Print Assumptions CPUPhysicalRegisterFile.physical_relation_iff.
Print Assumptions CPUPhysicalRegisterFile.nonzero_write_preserves_physical.
Print Assumptions CPUPhysicalRegisterFile.actual_write_port_preserves_zero.
