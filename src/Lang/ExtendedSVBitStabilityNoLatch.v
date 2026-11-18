(** Bit-level stability certificate for combinational settling, latch-free variant (generic).
    Same method as ExtendedSVBitStability (known-bit masks, per-round transformer), for programs whose combinational
    processes are all blocking-only (no clock-gate latch).  Reuses the masks, [slx_sound]-based [runs_agree] and
    [base_agree] of that library.
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitStability.
Import ListNotations ExtendedSV ExtendedSVBitStability.
Local Open Scope Z_scope.

Module ExtendedSVBitStabilityNoLatch.

Definition Kround0 (p : Program) (K : list Z) : list Z := trs K (procs p).

Fixpoint Kiter0 (p : Program) (N : nat) : list Z :=
  match N with O => K0 p | S n => Kround0 p (Kiter0 p n) end.

Definition PGood0 (p : Program) (pr : Process) : Prop :=
  nbafree (process_body pr) = true /\ (depth (process_body pr) <= statement_fuel p)%nat.

Lemma round_sound0 : forall p K A B,
  (forall pr, In pr (procs p) -> PGood0 p pr) -> Agree K A B -> B = comb_round p A ->
  Agree (Kround0 p K) B (comb_round p B).
Proof.
  intros p K A B H HA HB. unfold Kround0.
  change (comb_round p A) with (runs p (procs p) A) in HB.
  change (comb_round p B) with (runs p (procs p) B).
  rewrite HB at 1. apply runs_agree; [exact H | exact HA].
Qed.

Theorem comb_stable0 : forall p N,
  (4 <= statement_fuel p)%nat ->
  (forall pr, In pr (procs p) -> PGood0 p pr) ->
  (forall pr q, In pr (procs p) -> In q (fpp pr) -> (fst q < signal_count p)%nat) ->
  all_known (Kiter0 p N) (signal_count p) = true ->
  forall seed, length seed = signal_count p ->
  comb_round p (comb_iter p N seed) = comb_iter p N seed.
Proof.
  intros p N Hf Hg HR Hk seed Hl.
  assert (Hfr : forall pr, In pr (procs p) -> PFrameOk pr) by (intros pr Hin; left; exact (proj1 (Hg pr Hin))).
  assert (Hlen : forall n, length (comb_iter p n seed) = signal_count p).
  { induction n as [|n IH]; [exact Hl | ]. rewrite comb_iter_S_r.
    unfold comb_round. change (fold_left (run_process p) (filter is_comb (processes p)) (comb_iter p n seed))
      with (runs p (procs p) (comb_iter p n seed)).
    apply runs_len; auto. }
  assert (Hag : forall n, Agree (Kiter0 p n) (comb_iter p n seed) (comb_round p (comb_iter p n seed))).
  { induction n as [|n IH]; [apply base_agree; auto | ].
    simpl Kiter0. rewrite comb_iter_S_r.
    eapply round_sound0; [exact Hg | exact IH | reflexivity]. }
  symmetry. apply list_ext.
  - assert (Hl2 : length (comb_round p (comb_iter p N seed)) = signal_count p).
    { rewrite <- (comb_iter_S_r p N seed). apply Hlen. }
    rewrite Hl2, Hlen. reflexivity.
  - intros r Hr. rewrite Hlen in Hr. apply Z.bits_inj'. intros i Hi.
    apply (Hag N r i Hi).
    unfold all_known in Hk. rewrite forallb_forall in Hk.
    assert (Hr' : In r (seq 0 (signal_count p))) by (apply in_seq; lia).
    pose proof (Hk r Hr') as Hk0. apply Z.eqb_eq in Hk0 as Hk1.
    rewrite Hk1. rewrite Z.bits_m1 by auto. reflexivity.
Qed.

(** boolean front end, checked by computation *)
Definition pgood0_b (p : Program) (pr : Process) : bool :=
  andb (nbafree (process_body pr)) (Nat.leb (depth (process_body pr)) (statement_fuel p)).

Definition cert0_b (p : Program) : bool :=
  andb (Nat.leb 4 (statement_fuel p)) (andb (forallb (pgood0_b p) (procs p)) (roots_b p)).

Theorem comb_stable0_b : forall p N,
  cert0_b p = true ->
  all_known (Kiter0 p N) (signal_count p) = true ->
  forall seed, length seed = signal_count p ->
  comb_round p (comb_iter p N seed) = comb_iter p N seed.
Proof.
  intros p N Hc Hk. unfold cert0_b in Hc. apply andb_true_iff in Hc as [H4 Hc]. apply andb_true_iff in Hc as [Hg Hr].
  apply (comb_stable0 p N); [apply Nat.leb_le; exact H4 | | | exact Hk].
  - intros pr Hin. rewrite forallb_forall in Hg. specialize (Hg pr Hin). unfold pgood0_b in Hg.
    apply andb_true_iff in Hg as [H1 H2]. split; [exact H1 | apply Nat.leb_le; exact H2].
  - intros pr q Hin Hq. unfold roots_b in Hr. rewrite forallb_forall in Hr. specialize (Hr pr Hin).
    rewrite forallb_forall in Hr. specialize (Hr q Hq). apply Nat.ltb_lt in Hr. exact Hr.
Qed.

End ExtendedSVBitStabilityNoLatch.
Print Assumptions ExtendedSVBitStabilityNoLatch.comb_stable0_b.
