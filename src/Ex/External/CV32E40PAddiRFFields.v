(** Packed RF array -> individual architectural register fields. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice.
Require Import Lang.ExtendedSVBitSlice.
Require Import Ex.External.CV32E40PAddiRFLocal Ex.External.CV32E40PAddiRFPhase.
Require Import Ex.Generated.CV32E40PExtendedAST.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice.
Import ExtendedSVBitSlice CV32E40PAddiRFLocal CV32E40PAddiRFPhase CV32E40PExtendedAST.
Local Open Scope Z_scope.

Module CV32E40PAddiRFFields.
  Definition rf_field (value : Z) (r : nat) := read_slice value (32 * Z.of_nat r) 32.

  Lemma norm_idempotent : forall width value,
      norm width (norm width value) = norm width value.
  Proof. intros. unfold norm. rewrite <- Z.land_assoc. rewrite Z.land_diag. reflexivity. Qed.

  Lemma lane_offset_exact : forall r, (r < 32)%nat ->
      norm 10 (32 * Z.of_nat r) = 32 * Z.of_nat r.
  Proof.
    intros r Hr. unfold norm, mask.
    replace (2 ^ Z.of_nat 10 - 1) with (Z.ones 10) by reflexivity.
    rewrite Z.land_ones by lia. apply Z.mod_small.
    change (0 <= 32 * Z.of_nat r < 1024). lia.
  Qed.

  Lemma read_zero_offset_is_norm : forall value,
      read_slice value 0 32 = norm 32 value.
  Proof. intros. unfold read_slice, norm, mask. now rewrite Z.shiftr_0_r. Qed.

  Lemma one_lane_write_same : forall old r value, (r < 32)%nat ->
      rf_field (apply_update_root_value 902%nat old (lane_update r value)) r =
        norm 32 value.
  Proof.
    intros old r value Hr.
    unfold apply_update_root_value, lane_update, rf_field.
    cbn [update_signal update_offset update_width update_value Nat.eqb].
    rewrite lane_offset_exact by exact Hr.
    rewrite read_slice_write_same by lia.
    rewrite read_zero_offset_is_norm, norm_idempotent. reflexivity.
  Qed.

  Lemma one_lane_write_other : forall old r q value,
      (r < 32)%nat -> r <> q ->
      rf_field (apply_update_root_value 902%nat old (lane_update r value)) q =
        rf_field old q.
  Proof.
    intros old r q value Hr Hneq.
    unfold apply_update_root_value, lane_update, rf_field.
    cbn [update_signal update_offset update_width update_value Nat.eqb].
    rewrite lane_offset_exact by exact Hr.
    apply read_slice_write_disjoint; lia.
  Qed.

  Definition lane_effect (s : State) (r : nat) (old : Z) : Z :=
    if Z.eqb (norm 1 (read_signal s 885%nat)) 0 then 0
    else if Z.eqb (lane_enabled s 907%nat r) 0
         then if Z.eqb (lane_enabled s 906%nat r) 0 then rf_field old r
              else norm 32 (read_signal s 894%nat)
         else norm 32 (read_signal s 897%nat).

  Lemma lane_effect_congr : forall s r a b,
      rf_field a r = rf_field b r -> lane_effect s r a = lane_effect s r b.
  Proof.
    intros. unfold lane_effect.
    destruct (Z.eqb (norm 1 (read_signal s 885%nat)) 0);
    destruct (Z.eqb (lane_enabled s 907%nat r) 0);
    destruct (Z.eqb (lane_enabled s 906%nat r) 0); congruence.
  Qed.

  Lemma local_updates_field : forall s r old, (r < 32)%nat ->
      rf_field (apply_updates_root_value 902%nat old (local_lane_updates s r)) r =
        lane_effect s r old.
  Proof.
    intros. unfold local_lane_updates, lane_effect.
    destruct (Z.eqb (norm 1 (read_signal s 885%nat)) 0);
    destruct (Z.eqb (lane_enabled s 907%nat r) 0);
    destruct (Z.eqb (lane_enabled s 906%nat r) 0);
    cbn [apply_updates_root_value]; rewrite ?one_lane_write_same by assumption;
    rewrite ?norm_idempotent; reflexivity.
  Qed.

  Lemma local_updates_other_field : forall s r q old,
      (r < 32)%nat -> r <> q ->
      rf_field (apply_updates_root_value 902%nat old (local_lane_updates s r)) q =
        rf_field old q.
  Proof.
    intros. unfold local_lane_updates.
    destruct (Z.eqb (norm 1 (read_signal s 885%nat)) 0);
    destruct (Z.eqb (lane_enabled s 907%nat r) 0);
    destruct (Z.eqb (lane_enabled s 906%nat r) 0);
    cbn [apply_updates_root_value]; try reflexivity;
    apply one_lane_write_other; assumption.
  Qed.

  #[local] Opaque local_lane_updates lane_effect read_signal norm rf_field.

  Lemma scan_rf_field : forall s rs old q,
      Forall (fun r => (r < 32)%nat) rs -> NoDup rs ->
      rf_field (apply_updates_root_value 902%nat old
        (flat_map (local_lane_updates s) rs)) q =
      if in_dec Nat.eq_dec q rs then lane_effect s q old else rf_field old q.
  Proof.
    intros s rs. induction rs as [|r rs IH]; intros old q Hall Hnodup.
    - cbn. reflexivity.
    - inversion Hall; subst. inversion Hnodup; subst.
      cbn [flat_map]. rewrite apply_root_app.
      rewrite IH by assumption.
      destruct (Nat.eq_dec r q) as [->|Hneq].
      + destruct (in_dec Nat.eq_dec q rs) as [Hin|Hout]; [contradiction|].
        destruct (in_dec Nat.eq_dec q (q :: rs)) as [Hin|Hout'];
          [apply local_updates_field; assumption|exfalso; apply Hout'; now left].
      + destruct (in_dec Nat.eq_dec q rs) as [Hin|Hout];
          destruct (in_dec Nat.eq_dec q (r :: rs)) as [Hin'|Hout'].
        * apply lane_effect_congr. apply local_updates_other_field; assumption.
        * exfalso. apply Hout'. now right.
        * destruct Hin' as [Heq|Hin']; congruence.
        * apply local_updates_other_field; assumption.
  Qed.

  Theorem rf_chain_all_fields : forall s old r, (r < 32)%nat ->
      rf_field (apply_updates_root_value 902%nat old (rf_local_chain s)) r =
        if Nat.eq_dec r 0 then 0 else lane_effect s r old.
  Proof.
    intros s old r Hr. unfold rf_local_chain. cbn [apply_updates_root_value].
    rewrite scan_rf_field.
    - destruct (Nat.eq_dec r 0) as [->|Hnonzero].
      + destruct (in_dec Nat.eq_dec 0%nat (seq 1 31)) as [Hin|Hout].
        * apply in_seq in Hin. lia.
        * rewrite one_lane_write_same by lia. reflexivity.
      + destruct (in_dec Nat.eq_dec r (seq 1 31)) as [Hin|Hout].
        * apply lane_effect_congr. apply one_lane_write_other; lia.
        * exfalso. apply Hout. apply in_seq. lia.
    - apply Forall_forall. intros x Hx. apply in_seq in Hx. lia.
    - apply seq_NoDup.
  Qed.

  Theorem fullcore_phase_rf_field : forall ev pre r,
      changed_signal ev <> 902%nat -> (r < 32)%nat ->
      rf_field (read_signal (PhaseSemantics cv32e40p_program ev pre) 902%nat) r =
      let driven := phase_driven_state cv32e40p_program ev pre in
      if rf_trigger pre driven
      then if Nat.eq_dec r 0 then 0 else lane_effect driven r (read_signal pre 902%nat)
      else rf_field (read_signal pre 902%nat) r.
  Proof.
    intros ev pre r Hchanged Hr.
    rewrite fullcore_phase_rf_is_local by exact Hchanged.
    cbv beta zeta. destruct (rf_trigger pre (phase_driven_state cv32e40p_program ev pre));
      [apply rf_chain_all_fields; exact Hr|reflexivity].
  Qed.

  #[local] Transparent lane_effect.
  (** An actual FullCore reset edge clears every lane, regardless of the old
      RF and regardless of both write ports. This is not a fixture theorem. *)
  Theorem fullcore_reset_clears_every_register : forall ev pre r,
      changed_signal ev <> 902%nat -> (r < 32)%nat ->
      rf_trigger pre (phase_driven_state cv32e40p_program ev pre) = true ->
      norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 885%nat) = 0 ->
      rf_field (read_signal (PhaseSemantics cv32e40p_program ev pre) 902%nat) r = 0.
  Proof.
    intros ev pre r Hev Hr Hedge Hreset.
    rewrite fullcore_phase_rf_field by assumption. cbv beta zeta.
    rewrite Hedge. destruct (Nat.eq_dec r 0); [reflexivity|].
    unfold lane_effect. rewrite Hreset. reflexivity.
  Qed.

  (** Full RF frame rule at a real physical edge. All premises concern only
      the *pre-edge driven ports*. Deriving these ports from a reachable ID/EX
      instruction is a separate, still necessary pipeline proof obligation. *)
  Theorem fullcore_single_port_b_write : forall ev pre rd value,
      changed_signal ev <> 902%nat ->
      rf_trigger pre (phase_driven_state cv32e40p_program ev pre) = true ->
      norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 885%nat) <> 0 ->
      (forall r, (0 < r < 32)%nat ->
        lane_enabled (phase_driven_state cv32e40p_program ev pre) 906%nat r = 0) ->
      (forall r, (0 < r < 32)%nat ->
        (lane_enabled (phase_driven_state cv32e40p_program ev pre) 907%nat r <> 0
         <-> r = rd)) ->
      norm 32 (read_signal (phase_driven_state cv32e40p_program ev pre) 897%nat) = value ->
      forall r, (r < 32)%nat ->
      rf_field (read_signal (PhaseSemantics cv32e40p_program ev pre) 902%nat) r =
        if Nat.eq_dec r 0 then 0
        else if Nat.eq_dec r rd then value else rf_field (read_signal pre 902%nat) r.
  Proof.
    intros ev pre rd value Hev Hedge Hreset Ha Hb Hvalue r Hr.
    rewrite fullcore_phase_rf_field by assumption. cbv beta zeta.
    rewrite Hedge. destruct (Nat.eq_dec r 0) as [->|Hnonzero]; [reflexivity|].
    unfold lane_effect. apply Z.eqb_neq in Hreset. rewrite Hreset.
    specialize (Ha r ltac:(lia)). specialize (Hb r ltac:(lia)).
    destruct (Nat.eq_dec r rd) as [Heq|Hneq].
    - apply Hb in Heq. apply Z.eqb_neq in Heq. now rewrite Heq.
    - assert (Hzero : lane_enabled
          (phase_driven_state cv32e40p_program ev pre) 907%nat r = 0).
      { destruct (Z.eq_dec (lane_enabled
          (phase_driven_state cv32e40p_program ev pre) 907%nat r) 0);
          [assumption|exfalso; apply Hneq; now apply Hb]. }
      now rewrite Hzero, Ha.
  Qed.
End CV32E40PAddiRFFields.
