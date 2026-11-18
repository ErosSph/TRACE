(** Cross-round prefetch busy propagation through the original comb ordering. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVCombCut
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperands
 Ex.External.CV32E40PAddiAdderInputs Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiDecoderPhase Ex.External.CV32E40PAddiIDEXAccept
 Ex.External.CV32E40PFetchFIFOCount Ex.External.CV32E40PRequestWiring.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVCombCut
 CV32E40PExtendedAST CV32E40PAddiOperands CV32E40PAddiAdderInputs
 CV32E40PAddiOperandCone CV32E40PAddiDecoderPhase CV32E40PAddiIDEXAccept
 CV32E40PFetchFIFOCount CV32E40PRequestWiring.
Local Open Scope Z_scope.
Module CV32E40PBusyCone.
 #[local] Opaque norm read_signal run_process before_process comb_round.
 Lemma old_wire n proc src dst s :
   nth_error (processes cv32e40p_program) n = Some proc -> is_comb proc = true ->
   process_body proc = SAssign false (EVar 1 src) (LVar 1 dst) ->
   avoids_root dst (filter is_comb (skipn (S n) (processes cv32e40p_program))) = true ->
   avoids_root src (filter is_comb (firstn n (processes cv32e40p_program))) = true ->
   norm 1 (read_signal (round s) dst) = norm 1 (read_signal s src).
 Proof.
   intros Hn Hc Hb Hd Hs. unfold round.
   rewrite (comb_cut_root cv32e40p_program n proc s dst Hn Hc Hd),
     (assign_value _ proc 1 dst (EVar 1 src) Hb).
   cbn [eval_expr]. rewrite norm_twice, before_process_keeps_root by exact Hs. reflexivity.
 Qed.
 Lemma round_prefetch_busy s : norm 2 (read_signal s 440%nat) <> 0 ->
   norm 1 (read_signal (round s) 363%nat) = 1.
 Proof.
   intros H.
   rewrite (wire 1590 process_1590 398%nat 363%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)),
     (wire 1561 process_1561 423%nat 398%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   unfold round. rewrite (comb_cut_root cv32e40p_program 1546 process_1546 s 423%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1546 1 423%nat (rhs process_1546) eq_refl).
   unfold rhs. cbn [process_1546 process_body eval_expr]. rewrite norm_twice.
   rewrite (before_process_keeps_root cv32e40p_program 1546 s 440%nat ltac:(vm_compute; reflexivity)).
   change (norm 2 0) with 0. assert (Hz : (0 =? norm 2 (read_signal s 440%nat)) = false).
   { apply Z.eqb_neq. congruence. } rewrite Hz. change (norm 1 (boolz (negb false))) with 1.
   destruct (bit_cases (read_signal (before_process cv32e40p_program 1546 s) 426%nat)) as [Hb|Hb];
     rewrite Hb; reflexivity.
 Qed.
 Lemma round_if_busy s : norm 1 (read_signal (round s) 132%nat) = norm 1 (read_signal s 363%nat).
 Proof.
   rewrite (wire 1621 process_1621 359%nat 132%nat s eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
   apply (old_wire 1541 process_1541); try reflexivity; vm_compute; reflexivity.
 Qed.
 Lemma round_sleep_if_busy s : norm 1 (read_signal (round s) 294%nat) = norm 1 (read_signal s 132%nat).
 Proof. apply (old_wire 1535 process_1535); try reflexivity; vm_compute; reflexivity. Qed.
 Lemma round_busy_input s : norm 1 (read_signal s 294%nat) = 1 ->
   norm 1 (read_signal (round s) 306%nat) = 1.
 Proof.
   intros H. unfold round. rewrite (comb_cut_root cv32e40p_program 1534 process_1534 s 306%nat
     eq_refl eq_refl ltac:(vm_compute; reflexivity)),
     (assign_value _ process_1534 1 306%nat (rhs process_1534) eq_refl).
   unfold rhs. cbn [process_1534 process_body eval_expr]. rewrite norm_twice.
   rewrite (before_process_keeps_root cv32e40p_program 1534 s 294%nat ltac:(vm_compute; reflexivity)), H.
   destruct (bit_cases (read_signal (before_process cv32e40p_program 1534 s) 295%nat)) as [Ha|Ha];
   destruct (bit_cases (read_signal (before_process cv32e40p_program 1534 s) 296%nat)) as [Hb|Hb];
   destruct (bit_cases (read_signal (before_process cv32e40p_program 1534 s) 297%nat)) as [Hc|Hc];
     rewrite Ha, Hb, Hc; reflexivity.
 Qed.
 Theorem counter_busy_four_rounds s : norm 2 (read_signal s 440%nat) <> 0 ->
   norm 1 (read_signal (round (round (round (round s)))) 306%nat) = 1.
 Proof. intros H. apply round_busy_input. rewrite round_sleep_if_busy, round_if_busy. now apply round_prefetch_busy. Qed.
 Theorem counter_busy_lfp s : norm 2 (read_signal s 440%nat) <> 0 ->
   norm 1 (read_signal (lfp_candidate cv32e40p_program s) 306%nat) = 1.
 Proof.
   intros H. unfold lfp_candidate. change (lfp_fuel cv32e40p_program) with 8%nat.
   rewrite (comb_iter_last _ 7), (comb_iter_last _ 6), (comb_iter_last _ 5), (comb_iter_last _ 4).
   apply counter_busy_four_rounds.
   rewrite comb_iter_preserves_unwritten_root by (vm_compute; reflexivity). exact H.
 Qed.
 Theorem counter_busy_phase ev pre : changed_signal ev <> 440%nat ->
   norm 2 (read_signal pre 440%nat) <> 0 ->
   norm 1 (read_signal (phase_driven_state cv32e40p_program ev pre) 306%nat) = 1.
 Proof.
   intros He H. unfold phase_driven_state. apply counter_busy_lfp.
   rewrite read_signal_write_other by exact He. exact H.
 Qed.
 Print Assumptions counter_busy_lfp.
End CV32E40PBusyCone.
