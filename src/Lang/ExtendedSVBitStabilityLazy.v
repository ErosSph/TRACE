(** Lazy variant of the known-bit transfer [slx] (template route, additive; 2026-11-04).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    Why: [ExtendedSVBitStability.exhaustive] is [andb (width <= 12) (forallb ... (seq 0 (2^width)))].  The kernel VM evaluates both
    arguments of [andb], so a [case] on a 32-bit scrutinee without a default arm (NERV's unrolled [for] loops) builds [seq 0 (2^32)]
    and never finishes (80 GB after 16 CPU minutes).  Here the width test guards the enumeration with an [if].
    [slx_l] is [slx] with that [if]; [slx_l_eq] proves they are equal as functions, so every existing theorem
    ([comb_stable0_b], [Kiter0]) transfers: [comb_stable0_l] has the same statement with [Kiter0_l].
    Nothing is assumed; no accepted definition or statement is changed. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitStability Lang.ExtendedSVBitStabilityNoLatch.
Import ListNotations ExtendedSV ExtendedSVBitStability ExtendedSVBitStabilityNoLatch.
Local Open Scope Z_scope.
Module ExtendedSVBitStabilityLazy.

Definition exhaustive_l (scr : Expr) (arms : list (option Expr * Stmt)) : bool :=
  if Nat.leb (expr_width scr) 12
  then forallb (fun v => existsb (arm_hits v) arms) (map Z.of_nat (seq 0 (Nat.pow 2 (expr_width scr))))
  else false.

Lemma exhaustive_l_eq scr arms : exhaustive_l scr arms = exhaustive scr arms.
Proof. unfold exhaustive_l, exhaustive. destruct (Nat.leb (expr_width scr) 12); reflexivity. Qed.

Definition case_total_l (scr : Expr) (arms : list (option Expr * Stmt)) : bool :=
  orb (has_none arms) (exhaustive_l scr arms).

Lemma case_total_l_eq scr arms : case_total_l scr arms = case_total scr arms.
Proof. unfold case_total_l, case_total. rewrite exhaustive_l_eq. reflexivity. Qed.

Fixpoint slx_l (K : list Z) (st : Stmt) : list Z :=
  match st with
  | SSkip => K
  | SAssign _ rhs lv =>
      if ok_assign K rhs lv
      then match lv_static lv with
           | Some _ => kset K (lvalue_root lv) (fun m => Z.lor m (lv_mask lv))
           | None => K
           end
      else kset K (lvalue_root lv) (fun m => Z.land m (Z.lnot (lv_mask lv)))
  | SSeq l => fold_left (fun K' st' => slx_l K' st') l K
  | SIf g y n =>
      if eknown K g then meet (slx_l K y) (slx_l K n) else killl K (fpl st)
  | SCase scr arms =>
      if case_ok K scr arms
      then fold_left meet (map (fun a => slx_l K (snd a)) arms) (if case_total_l scr arms then [] else K)
      else killl K (fpl st)
  end.

Lemma depth_in_seq : forall l st, In st l -> (depth st <= fold_right Nat.max 0%nat (map depth l))%nat.
Proof.
  induction l as [|a l IH]; intros st H; [contradiction|]. cbn [map fold_right]. destruct H as [<-|H].
  - apply Nat.le_max_l.
  - specialize (IH st H). eapply Nat.le_trans; [exact IH | apply Nat.le_max_r].
Qed.

Lemma depth_in_arms : forall (arms : list (option Expr * Stmt)) a, In a arms ->
  (depth (snd a) <= fold_right Nat.max 0%nat (map (fun a => depth (snd a)) arms))%nat.
Proof.
  induction arms as [|b arms IH]; intros a H; [contradiction|]. cbn [map fold_right]. destruct H as [<-|H].
  - apply Nat.le_max_l.
  - specialize (IH a H). eapply Nat.le_trans; [exact IH | apply Nat.le_max_r].
Qed.

Lemma slx_l_eq_n : forall n st, (depth st <= n)%nat -> forall K, slx_l K st = slx K st.
Proof.
  induction n as [|n IH]; intros st Hd K.
  - destruct st; cbn [depth] in Hd; lia.
  - destruct st as [|nb rhs lv|l|g y nn|scr arms]; cbn [slx_l slx].
    + reflexivity.
    + reflexivity.
    + cbn [depth] in Hd.
      assert (Hall : forall st', In st' l -> (depth st' <= n)%nat).
      { intros st' Hin. pose proof (depth_in_seq l st' Hin). lia. }
      assert (Hf : forall (l0 : list Stmt), (forall st', In st' l0 -> (depth st' <= n)%nat) -> forall K0,
                fold_left (fun K' st' => slx_l K' st') l0 K0 = fold_left (fun K' st' => slx K' st') l0 K0).
      { induction l0 as [|a l0 IH0]; intros Hl K0; cbn [fold_left]; [reflexivity|].
        rewrite (IH a (Hl a (or_introl eq_refl))). apply IH0. intros st' Hin. apply Hl. right. exact Hin. }
      exact (Hf l Hall K).
    + cbn [depth] in Hd. rewrite (IH y) by lia. rewrite (IH nn) by lia. reflexivity.
    + cbn [depth] in Hd. rewrite case_total_l_eq.
      assert (Hmap : map (fun a => slx_l K (snd a)) arms = map (fun a => slx K (snd a)) arms).
      { apply map_ext_in. intros a Hin. apply IH. pose proof (depth_in_arms arms a Hin). lia. }
      rewrite Hmap. reflexivity.
Qed.

Lemma slx_l_eq K st : slx_l K st = slx K st.
Proof. exact (slx_l_eq_n (depth st) st (Nat.le_refl _) K). Qed.

Definition trs_l (K : list Z) (ps : list Process) : list Z :=
  fold_left (fun K' pr => slx_l K' (process_body pr)) ps K.

Lemma trs_l_eq K ps : trs_l K ps = trs K ps.
Proof.
  revert K. induction ps as [|pr ps IH]; intros K; cbn [trs_l trs fold_left]; [reflexivity|].
  rewrite slx_l_eq. exact (IH _).
Qed.

Fixpoint Kiter0_l (p : Program) (N : nat) : list Z :=
  match N with O => K0 p | S n => trs_l (Kiter0_l p n) (procs p) end.

Lemma Kiter0_l_eq p N : Kiter0_l p N = Kiter0 p N.
Proof.
  induction N as [|n IH]; cbn [Kiter0_l Kiter0]; [reflexivity|].
  unfold Kround0. rewrite trs_l_eq, IH. reflexivity.
Qed.

Theorem comb_stable0_l : forall p N,
  cert0_b p = true ->
  all_known (Kiter0_l p N) (signal_count p) = true ->
  forall seed, length seed = signal_count p ->
  comb_round p (comb_iter p N seed) = comb_iter p N seed.
Proof.
  intros p N Hc Hk. rewrite Kiter0_l_eq in Hk. exact (comb_stable0_b p N Hc Hk).
Qed.

End ExtendedSVBitStabilityLazy.
Print Assumptions ExtendedSVBitStabilityLazy.comb_stable0_l.
