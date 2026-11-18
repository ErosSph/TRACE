(** Design-independent: state length is preserved by comb_round / comb_iter / PhaseSemantics / phase_driven_state
    when every process only writes roots below the state length (checkable bound [wb_check]).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBitStability.
Import ListNotations ExtendedSV ExtendedSVBitStability.
Local Open Scope Z_scope.
Module ExtendedSVPhaseLength.

Definition Bnd (n : nat) (st : Stmt) : Prop := forall x, In x (stmt_writers st) -> (x < n)%nat.
Definition WB (p : Program) (n : nat) : Prop := forall P, In P (processes p) -> Bnd n (process_body P).

Definition wb_check (p : Program) (n : nat) : bool :=
  forallb (fun P => forallb (fun x => Nat.ltb x n) (stmt_writers (process_body P))) (processes p).

Lemma wb_check_sound : forall p n, wb_check p n = true -> WB p n.
Proof.
 intros p n H P HP x Hx. unfold wb_check in H. rewrite forallb_forall in H.
 pose proof (H P HP) as H1. rewrite forallb_forall in H1. apply Nat.ltb_lt. apply H1. exact Hx.
Qed.

Definition Inv (n : nat) (es : ExecState) : Prop :=
 length (blocking_state es) = n /\ (forall u, In u (pending_nba es) -> (update_signal u < n)%nat) /\
 (forall u, In u (emitted_updates es) -> (update_signal u < n)%nat).

Lemma exec_inv : forall n fuel st es, Bnd n st -> Inv n es -> Inv n (exec_stmt fuel st es).
Proof.
 intros n fuel. induction fuel as [|fuel IH]; intros st es HB HI; [exact HI|].
 destruct HI as [Hl [Hp He]].
 destruct st as [|nba rhs lhs|l|g y m|scr arms]; cbn [exec_stmt].
 - exact (conj Hl (conj Hp He)).
 - assert (Hs : (update_signal (resolve_update (blocking_state es) lhs (eval_expr (blocking_state es) rhs)) < n)%nat).
   { rewrite resolve_update_signal. apply HB. cbn. left. reflexivity. }
   destruct nba; cbn [blocking_state pending_nba emitted_updates].
   + split; [exact Hl|]. split.
     * intros u Hu. apply in_app_or in Hu as [Hu|[Hu|[]]]; [apply Hp; exact Hu | subst; exact Hs].
     * intros u Hu. apply in_app_or in Hu as [Hu|[Hu|[]]]; [apply He; exact Hu | subst; exact Hs].
   + unfold apply_update at 1. cbn [blocking_state pending_nba emitted_updates]. split; [|split].
     * cbn [blocking_state]. rewrite length_write_signal; [exact Hl|]. rewrite Hl. exact Hs.
     * exact Hp.
     * intros u Hu. apply in_app_or in Hu as [Hu|[Hu|[]]]; [apply He; exact Hu | subst; exact Hs].
 - cbn [stmt_writers] in HB.
   assert (Hg : forall l0 es0, (forall x, In x (flat_map stmt_writers l0) -> (x < n)%nat) -> Inv n es0 ->
      Inv n (fold_left (fun es' st' => exec_stmt fuel st' es') l0 es0)).
   { induction l0 as [|a l0 IHl]; intros es0 H0 H1; cbn [fold_left]; [exact H1|].
     apply IHl.
     - intros x Hx. apply H0. cbn [flat_map]. apply in_or_app. right. exact Hx.
     - apply IH; [|exact H1]. intros x Hx. apply H0. cbn [flat_map]. apply in_or_app. left. exact Hx. }
   apply Hg; [exact HB|]. exact (conj Hl (conj Hp He)).
 - cbn [stmt_writers] in HB. destruct (Z.eqb (eval_expr (blocking_state es) g) 0).
   + apply IH; [|exact (conj Hl (conj Hp He))]. intros x Hx. apply HB. apply in_or_app. right. exact Hx.
   + apply IH; [|exact (conj Hl (conj Hp He))]. intros x Hx. apply HB. apply in_or_app. left. exact Hx.
 - destruct (select_in (blocking_state es) (eval_expr (blocking_state es) scr) arms SSkip) as [H|H].
   + rewrite H. destruct fuel; exact (conj Hl (conj Hp He)).
   + apply IH; [|exact (conj Hl (conj Hp He))]. intros x Hx. apply HB. cbn [stmt_writers].
     apply in_map_iff in H as [[ko b] [Hb Hin]]. cbn in Hb. subst b.
     apply in_flat_map. exists (ko, select_case_stmt (blocking_state es) (eval_expr (blocking_state es) scr) arms SSkip). split; [exact Hin|exact Hx].
Qed.

Lemma apply_nba_len : forall n us s, length s = n -> (forall u, In u us -> (update_signal u < n)%nat) -> length (apply_nba s us) = n.
Proof.
 intros n us. induction us as [|u us IH]; intros s Hl H; cbn [apply_nba]; [exact Hl|].
 apply IH; [|intros v Hv; apply H; right; exact Hv].
 unfold apply_update. rewrite length_write_signal; [exact Hl|]. rewrite Hl. apply H. left. reflexivity.
Qed.

Lemma apply_updates_len : forall n us s, length s = n -> (forall u, In u us -> (update_signal u < n)%nat) -> length (apply_updates s us) = n.
Proof.
 intros n us. induction us as [|u us IH]; intros s Hl H; cbn [apply_updates]; [exact Hl|].
 apply IH; [|intros v Hv; apply H; right; exact Hv].
 unfold apply_update. rewrite length_write_signal; [exact Hl|]. rewrite Hl. apply H. left. reflexivity.
Qed.

Lemma init_inv : forall n s, length s = n -> Inv n {| blocking_state := s; pending_nba := []; emitted_updates := [] |}.
Proof. intros n s H. cbn. split; [exact H|]. split; intros u Hu; contradiction. Qed.

Lemma run_process_len : forall p n P s, Bnd n (process_body P) -> length s = n -> length (run_process p s P) = n.
Proof.
 intros p n P s HB Hl. unfold run_process.
 destruct (exec_inv n (statement_fuel p) _ _ HB (init_inv n s Hl)) as [H1 [H2 H3]].
 apply apply_nba_len; assumption.
Qed.

Lemma process_updates_sig : forall p n P s, Bnd n (process_body P) -> length s = n ->
  forall u, In u (process_updates p s P) -> (update_signal u < n)%nat.
Proof.
 intros p n P s HB Hl u Hu. unfold process_updates in Hu.
 destruct (exec_inv n (statement_fuel p) _ _ HB (init_inv n s Hl)) as [H1 [H2 H3]]. apply H3. exact Hu.
Qed.

Lemma comb_round_len : forall p n s, WB p n -> length s = n -> length (comb_round p s) = n.
Proof.
 intros p n s HW Hl. unfold comb_round.
 assert (Hg : forall l s0, (forall P, In P l -> In P (processes p)) -> length s0 = n -> length (fold_left (run_process p) l s0) = n).
 { induction l as [|P l IH]; intros s0 Hin H0; cbn [fold_left]; [exact H0|].
   apply IH; [intros Q HQ; apply Hin; right; exact HQ|].
   apply run_process_len; [apply HW; apply Hin; left; reflexivity | exact H0]. }
 apply Hg; [|exact Hl]. intros P HP. apply filter_In in HP as [HP _]. exact HP.
Qed.

Lemma comb_iter_len : forall p n k s, WB p n -> length s = n -> length (comb_iter p k s) = n.
Proof.
 intros p n k. induction k as [|k IH]; intros s HW Hl; cbn [comb_iter]; [exact Hl|].
 apply IH; [exact HW|]. apply comb_round_len; assumption.
Qed.

Lemma write_signal_len : forall s x v, (x < length s)%nat -> length (write_signal s x v) = length s.
Proof. exact length_write_signal. Qed.

Lemma driven_len : forall p ev pre n, WB p n -> length pre = n -> (changed_signal ev < n)%nat ->
  length (phase_driven_state p ev pre) = n.
Proof.
 intros p ev pre n HW Hl Hc. unfold phase_driven_state, lfp_candidate.
 apply comb_iter_len; [exact HW|]. rewrite length_write_signal; [exact Hl|]. lia.
Qed.

Theorem phase_len : forall p ev pre n, WB p n -> length pre = n -> (changed_signal ev < n)%nat ->
  length (PhaseSemantics p ev pre) = n.
Proof.
 intros p ev pre n HW Hl Hc. unfold PhaseSemantics, phase_execute_order, lfp_candidate.
 apply comb_iter_len; [exact HW|].
 unfold execute_process_order. apply apply_updates_len; [apply driven_len; assumption|].
 intros u Hu. apply in_flat_map in Hu as [P [HP Hu]].
 unfold selected_on_transition in HP. apply filter_In in HP as [HP _].
 apply (process_updates_sig p n P (phase_driven_state p ev pre)); [apply HW; exact HP| |exact Hu].
 apply driven_len; assumption.
Qed.

(** The seed of the second settle of a phase, and the exact equation PhaseSemantics = settle of that seed (generic). *)
Definition phase_seed (p : Program) (ev : Event) (pre : State) : State :=
 execute_process_order p (phase_driven_state p ev pre) (selected_on_transition p pre (phase_driven_state p ev pre)).

Lemma phase_eq : forall p ev pre, PhaseSemantics p ev pre = lfp_candidate p (phase_seed p ev pre).
Proof. intros. reflexivity. Qed.

Lemma phase_seed_len : forall p ev pre n, WB p n -> length pre = n -> (changed_signal ev < n)%nat ->
  length (phase_seed p ev pre) = n.
Proof.
 intros p ev pre n HW Hl Hc. unfold phase_seed, execute_process_order.
 apply apply_updates_len; [apply driven_len; assumption|].
 intros u Hu. apply in_flat_map in Hu as [P [HP Hu]].
 unfold selected_on_transition in HP. apply filter_In in HP as [HP _].
 apply (process_updates_sig p n P (phase_driven_state p ev pre)); [apply HW; exact HP| |exact Hu].
 apply driven_len; assumption.
Qed.

End ExtendedSVPhaseLength.
Print Assumptions ExtendedSVPhaseLength.phase_len.
