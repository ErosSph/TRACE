(** Initial architectural projection certificate for the concrete Req40
    two-ADDI trace.  The shared checker evaluates the real pipeline prefix
    once, while the soundness theorem exposes ordinary field equations. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV.
Require Import Ex.External.CV32E40PReq39Trace.
Require Import Ex.External.CV32E40PReq40StateRel.
Require Import Ex.External.CV32E40PReq40NextCommit.
Require Import Ex.External.CV32E40PReq40ConcreteTrace.
Require Import Ex.External.CV32E40PReq40Windows.

Import CV32E40PReq39Trace CV32E40PReq40NextCommit.
Import ExtendedSV.
Import CV32E40PReq40ConcreteTrace.
Import CV32E40PReq40Windows.
Import CV32E40PReq40StateRel.
Local Open Scope Z_scope.

Module CV32E40PReq40InitialProjection.

  Definition initial_projection_checkb (w : CommitWindow) : bool :=
    andb (Z.eqb (window_pre_pc w) 0)
    (andb (Z.eqb (window_pre_next_pc w) 4)
    (andb (rf_projection_checkb (window_pre_rf w) (fun _ => 0))
          (Z.eqb (addi_pre_memory w) 0))).

  (** Call-by-value form of exactly the same test. *)
  Definition initial_projection_checkb_shared (w : CommitWindow) : bool :=
    let image := window_image w in
    let c0 := window_cursor w in
    let c1 := full_cycle_image image c0 in
    let pre_pc := read_signal (trace_rtl c0) architectural_pc_signal in
    let actual_rf := fun r : Z =>
      if (0 <=? r) && (r <? 32)
      then rf_register (trace_rtl c1) (Z.to_nat r) else 0 in
    andb (Z.eqb pre_pc 0)
    (andb (Z.eqb ((pre_pc + 4) mod 2 ^ 32) 4)
    (andb (rf_projection_checkb actual_rf (fun _ => 0))
          (Z.eqb (trace_memory_word c1) 0))).

  #[local] Opaque full_cycle_image.
  Lemma initial_projection_shared_equiv : forall w,
      initial_projection_checkb_shared w = initial_projection_checkb w.
  Proof. reflexivity. Qed.
  #[local] Transparent full_cycle_image.

  Lemma initial_projection_checkb_sound : forall w,
      initial_projection_checkb w = true ->
      window_pre_pc w = 0 /\
      window_pre_next_pc w = 4 /\
      (forall r, legal_reg r -> window_pre_rf w r = 0) /\
      addi_pre_memory w = 0.
  Proof.
    intros w H.
    unfold initial_projection_checkb in H.
    apply andb_true_iff in H as [Hpc H].
    apply andb_true_iff in H as [Hnext H].
    apply andb_true_iff in H as [Hrf Hmem].
    apply Z.eqb_eq in Hpc; apply Z.eqb_eq in Hnext;
    apply Z.eqb_eq in Hmem.
    repeat split; try assumption.
    intros r Hr.
    exact (rf_projection_checkb_sound
      (window_pre_rf w) (fun _ : Z => 0) Hrf r Hr).
  Qed.

  Theorem first_window_initial_projection_shared :
      initial_projection_checkb_shared first_window = true.
  Proof. vm_compute. reflexivity. Qed.

  Corollary first_window_initial_projection :
      window_pre_pc first_window = 0 /\
      window_pre_next_pc first_window = 4 /\
      (forall r, legal_reg r -> window_pre_rf first_window r = 0) /\
      addi_pre_memory first_window = 0.
  Proof.
    apply initial_projection_checkb_sound.
    rewrite <- initial_projection_shared_equiv.
    exact first_window_initial_projection_shared.
  Qed.

End CV32E40PReq40InitialProjection.
