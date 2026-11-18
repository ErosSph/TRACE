(** Packed register-bank projection and ordered write/frame rules.
    These facts hold for arbitrary packed contents and update lists. They say
    nothing about whether the value written is the correct ISA operand/result. *)
From Coq Require Import ZArith List Lia Bool btauto.Btauto.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVBitSlice ExtendedSVRootProjection.
Local Open Scope Z_scope.

Module ExtendedSVRegisterBank.
Definition lane_read (width:nat) (packed index:Z) :=
 read_slice packed (Z.of_nat width*index) (Z.of_nat width).

Lemma read_slice_normalized width value :
 read_slice value 0 (Z.of_nat width)=norm width value.
Proof. unfold read_slice,norm,mask. now rewrite Z.shiftr_0_r. Qed.

(** A root-wide assignment is a slice write at zero. Only lanes wholly
    contained in its width may use this projection; partial overlap is not
    covered by this rule. *)
Theorem read_slice_write_cover_zero old offset width total value :
 0<=offset -> 0<=width -> offset+width<=total ->
 read_slice(write_slice old 0 total value)offset width=read_slice value offset width.
Proof.
 intros HO HW HC. apply Z.bits_inj;intro bit.
 destruct(Z_lt_ge_dec bit 0)as[HN|HP].
 - repeat rewrite Z.testbit_neg_r by lia. reflexivity.
 - unfold read_slice. rewrite !Z.land_spec.
   destruct(Z_lt_ge_dec bit width)as[HL|HH].
   + rewrite mask_bit_low by lia. rewrite !Bool.andb_true_r.
     rewrite !Z.shiftr_spec by lia.
     unfold write_slice. rewrite !Z.shiftl_0_r.
     rewrite Z.lor_spec,!Z.land_spec,Z.lnot_spec by lia.
     rewrite mask_bit_low by lia. btauto.
   + rewrite mask_bit_high by lia. now rewrite !Bool.andb_false_r.
Qed.

Definition LaneCompatible root width index (u:Update) : Prop :=
 update_signal u<>root \/
 (update_offset u=Z.of_nat width*index /\ update_width u=width) \/
 (update_offset u=0 /\ Z.of_nat width*index+Z.of_nat width<=Z.of_nat(update_width u)) \/
 (0<=update_offset u /\
  (Z.of_nat width*index+Z.of_nat width<=update_offset u \/
   update_offset u+Z.of_nat(update_width u)<=Z.of_nat width*index)).

Definition lane_update root width index (current:Z) (u:Update) :=
 if Nat.eqb(update_signal u)root then
   if Z.eqb(update_offset u)(Z.of_nat width*index) && Nat.eqb(update_width u)width
   then norm width(update_value u)
   else if Z.eqb(update_offset u)0 &&
     Z.leb(Z.of_nat width*index+Z.of_nat width)(Z.of_nat(update_width u))
   then lane_read width(update_value u)index else current
 else current.

Fixpoint lane_replay root width index current (updates:list Update) :=
 match updates with
 | []=>current
 | u::rest=>lane_replay root width index(lane_update root width index current u)rest
 end.

Theorem lane_update_correct root width index packed u :
 0<=index -> LaneCompatible root width index u ->
 lane_read width(apply_update_root_value root packed u)index=
 lane_update root width index(lane_read width packed index)u.
Proof.
 intros HI HC. unfold apply_update_root_value,lane_update.
 destruct(Nat.eqb(update_signal u)root)eqn:HR;[|reflexivity].
 apply Nat.eqb_eq in HR.
 destruct(Z.eqb(update_offset u)(Z.of_nat width*index) && Nat.eqb(update_width u)width)eqn:HE.
 - apply andb_true_iff in HE as[HO HW].
   apply Z.eqb_eq in HO;apply Nat.eqb_eq in HW.
   unfold lane_read. rewrite HO,HW,read_slice_write_same by nia.
   apply read_slice_normalized.
 - destruct(Z.eqb(update_offset u)0 &&
     Z.leb(Z.of_nat width*index+Z.of_nat width)(Z.of_nat(update_width u)))eqn:HCov.
   + apply andb_true_iff in HCov as[HO HW]. apply Z.eqb_eq in HO;apply Z.leb_le in HW.
     unfold lane_read. rewrite HO. apply read_slice_write_cover_zero;nia.
   + destruct HC as[HN|[[HO HW]|[[HO HW]|[HO HD]]]];[contradiction| | |].
     * rewrite HO,HW,Z.eqb_refl,Nat.eqb_refl in HE;discriminate.
     * rewrite HO,Z.eqb_refl in HCov. apply Z.leb_le in HW.
       rewrite HW in HCov;discriminate.
     * unfold lane_read. apply read_slice_write_disjoint;try assumption;nia.
Qed.

Theorem lane_replay_correct root width index updates :
 0<=index -> Forall(LaneCompatible root width index)updates ->
 forall packed,
 lane_read width(apply_updates_root_value root packed updates)index=
 lane_replay root width index(lane_read width packed index)updates.
Proof.
 intros HI HC. induction HC as[|u rest HU HR IH];intro packed;cbn;[reflexivity|].
 rewrite IH,lane_update_correct by assumption. reflexivity.
Qed.

Theorem state_lane_replay_correct root width index updates s :
 0<=index -> Forall(LaneCompatible root width index)updates ->
 lane_read width(read_signal(apply_updates s updates)root)index=
 lane_replay root width index(lane_read width(read_signal s root)index)updates.
Proof.
 intros HI HC. rewrite read_signal_apply_updates.
 now apply lane_replay_correct.
Qed.

Definition bank_write root width index value : Update :=
 {|update_signal:=root;update_offset:=Z.of_nat width*index;
   update_width:=width;update_value:=value|}.

Lemma bank_write_compatible root width observed written value :
 0<=observed -> 0<=written ->
 LaneCompatible root width observed(bank_write root width written value).
Proof.
 intros HO HW. unfold LaneCompatible,bank_write;cbn.
 destruct(Z.eq_dec observed written)as[->|HN].
 - right;left;auto.
 - right;right;right. split;[nia|].
   destruct(Z_lt_ge_dec observed written);[left|right];nia.
Qed.

Theorem bank_write_lane root width observed written value packed :
 0<=observed -> 0<=written ->
 lane_read width(apply_update_root_value root packed(bank_write root width written value))observed=
 if Z.eqb observed written then norm width value else lane_read width packed observed.
Proof.
 intros HO HW.
 destruct(Z.eqb observed written)eqn:HE.
 - apply Z.eqb_eq in HE;subst written.
   unfold apply_update_root_value,bank_write;cbn.
   rewrite Nat.eqb_refl. unfold lane_read.
   rewrite read_slice_write_same by nia. apply read_slice_normalized.
 - apply Z.eqb_neq in HE.
   unfold apply_update_root_value,bank_write;cbn.
   rewrite Nat.eqb_refl. unfold lane_read.
   apply read_slice_write_disjoint;nia.
Qed.

Theorem state_bank_write_lane root width observed written value s :
 0<=observed -> 0<=written ->
 lane_read width(read_signal(apply_update s(bank_write root width written value))root)observed=
 if Z.eqb observed written then norm width value else lane_read width(read_signal s root)observed.
Proof. intros;rewrite read_signal_apply_update;now apply bank_write_lane. Qed.

Definition BankRelated width count packed (abstract:Z->Z) :=
 forall index,0<=index<count -> lane_read width packed index=abstract index.
Definition abstract_write width (abstract:Z->Z) written value :=
 fun observed=>if Z.eqb observed written then norm width value else abstract observed.

Theorem bank_related_write root width count packed abstract written value :
 BankRelated width count packed abstract -> 0<=written ->
 BankRelated width count
   (apply_update_root_value root packed(bank_write root width written value))
   (abstract_write width abstract written value).
Proof.
 intros HR HW index HI. rewrite bank_write_lane by lia.
 unfold abstract_write. destruct(Z.eqb index written);[reflexivity|now apply HR].
Qed.

Fixpoint abstract_writes width (abstract:Z->Z) (writes:list(Z*Z)) :=
 match writes with
 | []=>abstract
 | (index,value)::rest=>abstract_writes width(abstract_write width abstract index value)rest
 end.
Definition bank_updates root width (writes:list(Z*Z)) :=
 map(fun iv=>bank_write root width(fst iv)(snd iv))writes.

(** Later writes are replayed after earlier writes, including repeated writes
    to the same lane; neither sorting nor a last-writer assumption is used. *)
Theorem bank_related_writes root width count writes :
 Forall(fun iv=>0<=fst iv)writes ->
 forall packed abstract, BankRelated width count packed abstract ->
 BankRelated width count
   (apply_updates_root_value root packed(bank_updates root width writes))
   (abstract_writes width abstract writes).
Proof.
 intro HC;induction HC as[|[index value]rest HI HR IH];intros packed abstract Hbank;cbn;[exact Hbank|].
 apply IH. now apply bank_related_write.
Qed.

Theorem state_bank_related_writes root width count writes s abstract :
 Forall(fun iv=>0<=fst iv)writes ->
 BankRelated width count(read_signal s root)abstract ->
 BankRelated width count(read_signal(apply_updates s(bank_updates root width writes))root)
   (abstract_writes width abstract writes).
Proof.
 intros HC HR. rewrite read_signal_apply_updates. now apply bank_related_writes.
Qed.

Definition bank_reset root total value : Update :=
 {|update_signal:=root;update_offset:=0;update_width:=total;update_value:=value|}.

Theorem bank_reset_compatible root width index total value :
 Z.of_nat width*index+Z.of_nat width<=Z.of_nat total ->
 LaneCompatible root width index(bank_reset root total value).
Proof. intro H;right;right;left;split;[reflexivity|exact H]. Qed.

Theorem bank_related_reset root width count packed total value :
 count*Z.of_nat width<=Z.of_nat total ->
 BankRelated width count
   (apply_update_root_value root packed(bank_reset root total value))
   (fun index=>lane_read width value index).
Proof.
 intros HC index HI. unfold apply_update_root_value,bank_reset;cbn.
 rewrite Nat.eqb_refl. unfold lane_read. apply read_slice_write_cover_zero;nia.
Qed.

Theorem state_bank_related_reset root width count s total value :
 count*Z.of_nat width<=Z.of_nat total ->
 BankRelated width count(read_signal(apply_update s(bank_reset root total value))root)
   (fun index=>lane_read width value index).
Proof. intro HC;rewrite read_signal_apply_update;now apply bank_related_reset. Qed.

(** A checked bank plan can mix full-bank resets and individual lane writes.
    Operations retain their original order; reset values remain arbitrary. *)
Inductive BankOperation :=
| WriteLane (index value:Z)
| ResetBank (total:nat) (value:Z).

Definition operation_update root width (operation:BankOperation) : Update :=
 match operation with
 | WriteLane index value=>bank_write root width index value
 | ResetBank total value=>bank_reset root total value
 end.
Definition operation_effect width (abstract:Z->Z) (operation:BankOperation) : Z->Z :=
 match operation with
 | WriteLane index value=>abstract_write width abstract index value
 | ResetBank total value=>fun index=>lane_read width value index
 end.
Definition OperationValid width count (operation:BankOperation) : Prop :=
 match operation with
 | WriteLane index value=>0<=index
 | ResetBank total value=>count*Z.of_nat width<=Z.of_nat total
 end.

Theorem bank_related_operation root width count packed abstract operation :
 BankRelated width count packed abstract -> OperationValid width count operation ->
 BankRelated width count(apply_update_root_value root packed(operation_update root width operation))
   (operation_effect width abstract operation).
Proof.
 intros HR HC;destruct operation;cbn in *.
 - now apply bank_related_write.
 - now apply bank_related_reset.
Qed.

Fixpoint operation_effects width (abstract:Z->Z) (operations:list BankOperation) :=
 match operations with
 | []=>abstract
 | operation::rest=>operation_effects width(operation_effect width abstract operation)rest
 end.
Definition operation_updates root width (operations:list BankOperation) :=
 map(operation_update root width)operations.

Theorem bank_related_operations root width count operations :
 Forall(OperationValid width count)operations ->
 forall packed abstract, BankRelated width count packed abstract ->
 BankRelated width count
   (apply_updates_root_value root packed(operation_updates root width operations))
   (operation_effects width abstract operations).
Proof.
 intro HC;induction HC as[|operation rest HO HR IH];intros packed abstract Hbank;cbn;[exact Hbank|].
 apply IH. now apply bank_related_operation.
Qed.

Theorem state_bank_related_operations root width count operations s abstract :
 Forall(OperationValid width count)operations ->
 BankRelated width count(read_signal s root)abstract ->
 BankRelated width count(read_signal(apply_updates s(operation_updates root width operations))root)
   (operation_effects width abstract operations).
Proof.
 intros HC HR. rewrite read_signal_apply_updates. now apply bank_related_operations.
Qed.
End ExtendedSVRegisterBank.
Print Assumptions ExtendedSVRegisterBank.lane_replay_correct.
Print Assumptions ExtendedSVRegisterBank.state_lane_replay_correct.
Print Assumptions ExtendedSVRegisterBank.bank_write_lane.
Print Assumptions ExtendedSVRegisterBank.bank_related_writes.
Print Assumptions ExtendedSVRegisterBank.state_bank_related_writes.
Print Assumptions ExtendedSVRegisterBank.read_slice_write_cover_zero.
Print Assumptions ExtendedSVRegisterBank.bank_related_reset.
Print Assumptions ExtendedSVRegisterBank.state_bank_related_operations.
