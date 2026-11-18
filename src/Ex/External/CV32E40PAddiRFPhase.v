(** Full real CV32E40P phase -> exact local RF update chain, for arbitrary
    input states. The full CPU transition is rewritten, never evaluated. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Require Import Lang.ExtendedSVProcessSlice.
Require Import Ex.Generated.CV32E40PExtendedAST.
Require Import Ex.External.CV32E40PAddiRFLocal.
Require Import Lang.ExtendedSVBankPlan Lang.ExtendedSVRegisterBank
 Ex.External.CPUArrayContracts Ex.Generated.CV32E40PGeneratedBank.
From Coq Require Import Lia.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice.
Import CV32E40PExtendedAST CV32E40PAddiRFLocal.
Import ExtendedSVBankPlan ExtendedSVRegisterBank CV32E40PGeneratedBank CV32E40PAddiRFLocal.

Module CV32E40PAddiRFPhase.
  #[local] Opaque process_updates read_signal norm.
  Definition rf_processes : list Process :=
    process_44 :: map rf_lane_process (seq 1 31).

  Theorem fullcore_rf_writer_slice :
      filter (writes_rootb 902) (processes cv32e40p_program) = rf_processes.
  Proof. vm_compute. reflexivity. Qed.

  Theorem fullcore_rf_comb_unwritten :
      comb_root_unwrittenb cv32e40p_program 902 = true.
  Proof. vm_compute. reflexivity. Qed.

  Definition rf_trigger (old driven : State) : bool :=
    process_matches_states old driven process_44.

  Lemma rf_process_list_triggers_together : forall old driven rs,
      filter (process_matches_states old driven) (process_44 :: map rf_lane_process rs) =
        if rf_trigger old driven then process_44 :: map rf_lane_process rs else [].
  Proof.
    intros old driven rs0.
    assert (H : forall rs, filter (process_matches_states old driven)
      (map rf_lane_process rs) =
      if rf_trigger old driven then map rf_lane_process rs else []).
    { induction rs as [|r rs IH]; cbn [filter map];
        [destruct (rf_trigger old driven); reflexivity|].
      change ((if rf_trigger old driven then
        rf_lane_process r :: filter (process_matches_states old driven)
          (map rf_lane_process rs)
        else filter (process_matches_states old driven) (map rf_lane_process rs)) =
          (if rf_trigger old driven then map rf_lane_process (r :: rs) else [])).
      rewrite IH. destruct (rf_trigger old driven); reflexivity. }
    change ((if rf_trigger old driven then
      process_44 :: filter (process_matches_states old driven)
        (map rf_lane_process rs0)
      else filter (process_matches_states old driven)
        (map rf_lane_process rs0)) =
          (if rf_trigger old driven then process_44 :: map rf_lane_process rs0
           else [])).
    rewrite H. destruct (rf_trigger old driven); reflexivity.
  Qed.

  Lemma rf_processes_trigger_together : forall old driven,
      filter (process_matches_states old driven) rf_processes =
        if rf_trigger old driven then rf_processes else [].
  Proof.
    intros. exact (rf_process_list_triggers_together old driven (seq 1 31)).
  Qed.

  Definition rf_local_chain (driven : State) : list Update :=
    lane_update 0 0 :: flat_map (local_lane_updates driven) (seq 1 31).

  Lemma rf_process_chain_is_local : forall driven,
      flat_map (process_updates cv32e40p_program driven) rf_processes =
        rf_local_chain driven.
  Proof.
    intros driven. unfold rf_processes, rf_local_chain.
    generalize (seq 1 31) as rs. intros rs.
    change (process_updates cv32e40p_program driven process_44 ++
      flat_map (process_updates cv32e40p_program driven)
        (map rf_lane_process rs) =
      lane_update 0 0 :: flat_map (local_lane_updates driven) rs).
    rewrite actual_x0_always_writes_zero. cbn [app].
    f_equal.
    induction rs as [|r rs IH]; cbn [flat_map map]; auto.
    rewrite template_updates_are_local, IH. reflexivity.
  Qed.

  (** These plans only name the common syntactic shape of the generated
      lane plans. Their evaluation below is pure ordered-operation algebra;
      no hand-written process execution theorem is used by the new bridge. *)
  Definition rf_lane_bank_plan (r : nat) : BankPlan :=
    BPSeq [BPSeq [BPIf (EVar 1 885%nat)
      (BPSeq [BPIf (ESel 1 (EVar 32 907%nat) (EConst 5 (Z.of_nat r)))
        (BPWord (EConst 10 (32 * Z.of_nat r)) (EVar 32 897%nat))
        (BPIf (ESel 1 (EVar 32 906%nat) (EConst 5 (Z.of_nat r)))
          (BPWord (EConst 10 (32 * Z.of_nat r)) (EVar 32 894%nat))
          BPEmpty)])
      (BPSeq [BPWord (EConst 10 (32 * Z.of_nat r)) (EConst 32 0)])]].

  Lemma generated_bank_plan_shapes :
    map bank_plan bank_902_entries =
      bank_902_process_44_plan :: map rf_lane_bank_plan (seq 1 31).
  Proof. reflexivity. Qed.

  Lemma generated_bank_common_trigger old driven :
    Forall (fun entry =>
      process_matches_states old driven (bank_process entry) = rf_trigger old driven)
      bank_902_entries.
  Proof. repeat constructor; reflexivity. Qed.

  Lemma bank_operations_common_trigger total entries old driven trigger :
    Forall (fun entry =>
      process_matches_states old driven (bank_process entry) = trigger) entries ->
    bank_phase_operations total old driven entries =
      if trigger then flat_map (eval_bank_plan total driven) (map bank_plan entries)
      else [].
  Proof.
    intro H. unfold bank_phase_operations.
    induction H as [|entry entries HE HT IH].
    - destruct trigger; reflexivity.
    - cbn [bank_phase_operations flat_map map bank_process bank_plan] in *.
      rewrite HE. destruct trigger; cbn [app] in *; now rewrite IH.
  Qed.

  Lemma generated_lane_updates_are_local driven r : (r < 32)%nat ->
    operation_updates 902%nat 32
      (eval_bank_plan 1024 driven (rf_lane_bank_plan r)) =
    local_lane_updates driven r.
  Proof.
    Local Transparent norm.
    intro Hr.
    assert (HO : norm 10 (32 * Z.of_nat r)%Z = (32 * Z.of_nat r)%Z).
    { apply CPUArrayContracts.norm_in_range.
      change (0 <= 32 * Z.of_nat r < 1024)%Z. lia. }
    assert (HD : (32 * Z.of_nat r / 32 = Z.of_nat r)%Z).
    { rewrite Z.mul_comm. apply Z.div_mul. discriminate. }
    assert (HZ : norm 32 0 = 0%Z) by (unfold norm, mask; reflexivity).
    Local Opaque norm.
    unfold rf_lane_bank_plan, local_lane_updates.
    cbn [eval_bank_plan flat_map app eval_expr operation_updates map
      operation_update ExtendedSVRegisterBank.bank_write lane_update lane_enabled].
    destruct (Z.eqb (norm 1 (read_signal driven 885%nat)) 0) eqn:HR;
      destruct (Z.eqb (lane_enabled driven 907%nat r) 0) eqn:HB;
      destruct (Z.eqb (lane_enabled driven 906%nat r) 0) eqn:HA;
      repeat progress (cbn [flat_map app operation_updates map operation_update
        ExtendedSVRegisterBank.bank_write eval_bank_plan eval_expr lane_update];
        fold (lane_enabled driven 907%nat r) (lane_enabled driven 906%nat r);
        rewrite ?HR, ?HB, ?HA);
      rewrite ?HO, ?HD, ?HZ;
      unfold lane_update, ExtendedSVRegisterBank.bank_write;
      rewrite ?HO, ?HZ; reflexivity.
  Qed.

  Lemma generated_x0_updates driven :
    operation_updates 902%nat 32
      (eval_bank_plan 1024 driven bank_902_process_44_plan) =
    [lane_update 0 0].
  Proof.
    Local Transparent norm.
    cbn [bank_902_process_44_plan eval_bank_plan eval_expr flat_map app
      operation_updates map operation_update ExtendedSVRegisterBank.bank_write lane_update].
    destruct (Z.eqb (norm 1 (read_signal driven 885%nat)) 0);
      reflexivity.
  Qed.
  Local Opaque norm.

  Lemma generated_bank_updates_are_local old driven :
    operation_updates 902%nat 32
      (bank_phase_operations 1024 old driven bank_902_entries) =
    if rf_trigger old driven then rf_local_chain driven else [].
  Proof.
    rewrite (bank_operations_common_trigger 1024 bank_902_entries old driven
      (rf_trigger old driven) (generated_bank_common_trigger old driven)).
    destruct (rf_trigger old driven); [|reflexivity].
    rewrite generated_bank_plan_shapes.
    cbn [flat_map]. unfold operation_updates at 1.
    rewrite map_app. fold (operation_updates 902%nat 32
      (eval_bank_plan 1024 driven bank_902_process_44_plan)).
    rewrite generated_x0_updates.
    unfold rf_local_chain. cbn [app]. f_equal.
    assert (HL : forall rs, Forall (fun r => (r < 32)%nat) rs ->
      map (operation_update 902%nat 32)
        (flat_map (eval_bank_plan 1024 driven) (map rf_lane_bank_plan rs)) =
      flat_map (local_lane_updates driven) rs).
    { intros rs HR. induction HR as [|r rs Hr HR IH];
        cbn [flat_map map]; [reflexivity|].
      rewrite map_app. change (operation_updates 902%nat 32
        (eval_bank_plan 1024 driven (rf_lane_bank_plan r)) ++
        map (operation_update 902%nat 32)
          (flat_map (eval_bank_plan 1024 driven) (map rf_lane_bank_plan rs)) =
        local_lane_updates driven r ++ flat_map (local_lane_updates driven) rs).
      rewrite generated_lane_updates_are_local by assumption.
      now rewrite IH. }
    apply HL. apply Forall_forall. intros r Hin. apply in_seq in Hin. lia.
  Qed.

  Local Opaque phase_driven_state PhaseSemantics.
  Lemma apply_updates_root_value_if root current (trigger : bool) updates :
    apply_updates_root_value root current (if trigger then updates else []) =
    if trigger then apply_updates_root_value root current updates else current.
  Proof. destruct trigger; reflexivity. Qed.

  Theorem fullcore_phase_rf_is_local : forall ev pre,
      changed_signal ev <> 902 ->
      read_signal (PhaseSemantics cv32e40p_program ev pre) 902 =
      let driven := phase_driven_state cv32e40p_program ev pre in
      if rf_trigger pre driven
      then apply_updates_root_value 902 (read_signal pre 902) (rf_local_chain driven)
      else read_signal pre 902.
  Proof.
    intros ev pre Hchanged.
    refine (eq_trans (bank_phase_updates cv32e40p_program 902%nat 1024 bank_902_entries
      bank_902_certificate ev pre Hchanged) _).
    exact (eq_trans
      (f_equal (apply_updates_root_value 902 (read_signal pre 902))
        (generated_bank_updates_are_local pre (phase_driven_state cv32e40p_program ev pre)))
      (apply_updates_root_value_if 902 (read_signal pre 902)
        (rf_trigger pre (phase_driven_state cv32e40p_program ev pre))
        (rf_local_chain (phase_driven_state cv32e40p_program ev pre)))).
  Qed.

  Corollary no_rf_edge_preserves_fullcore_rf : forall ev pre,
      changed_signal ev <> 902 ->
      rf_trigger pre (phase_driven_state cv32e40p_program ev pre) = false ->
      read_signal (PhaseSemantics cv32e40p_program ev pre) 902 = read_signal pre 902.
  Proof.
    intros ev pre Hchanged Htrigger.
    rewrite fullcore_phase_rf_is_local by exact Hchanged.
    cbv beta zeta. now rewrite Htrigger.
  Qed.
End CV32E40PAddiRFPhase.
Print Assumptions CV32E40PAddiRFPhase.generated_bank_updates_are_local.
Print Assumptions CV32E40PAddiRFPhase.fullcore_phase_rf_is_local.
Print CV32E40PAddiRFPhase.fullcore_phase_rf_is_local.
