(** Raw one-bit signal preservation; needed when edge predicates inspect raw
    signal values rather than normalized expression values. No CPU constants. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection.
Local Open Scope Z_scope.
Module ExtendedSVBitInvariant.
 Definition Bit (v : Z) := v = 0 \/ v = 1.
 Definition BitRoot root s := Bit (read_signal s root).
 Definition BitUpdate root u := update_signal u <> root \/
   (update_offset u = 0 /\ update_width u = 1%nat).
 Fixpoint bit_writesb root st : bool :=
   match st with
   | SSkip => true
   | SAssign _ _ lv => if Nat.eqb (lvalue_root lv) root then
       match lv with LVar w _ => Nat.eqb w 1 | _ => false end else true
   | SSeq xs => forallb (bit_writesb root) xs
   | SIf _ a b => bit_writesb root a && bit_writesb root b
   | SCase _ arms => forallb (fun a => bit_writesb root (snd a)) arms
   end.
 Lemma norm_bit v : Bit (norm 1 v).
 Proof.
   unfold norm, mask, Bit. change (Z.land v (Z.ones 1) = 0 \/ Z.land v (Z.ones 1) = 1).
   rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound v 2 ltac:(lia)).
   change (2^1) with 2. lia.
 Qed.
 Lemma bit_normalized v : Bit v -> norm 1 v = v.
 Proof. intros [H | H]; rewrite H; reflexivity. Qed.
 Lemma bit_slice old v : Bit old -> Bit (write_slice old 0 1 v).
 Proof.
   intros [H | H]; rewrite H; change (Bit (norm 1 v)); apply norm_bit.
 Qed.
 Lemma resolved_bit root s lv value :
   (if Nat.eqb (lvalue_root lv) root then
       match lv with LVar w _ => Nat.eqb w 1 | _ => false end else true) = true ->
   BitUpdate root (resolve_update s lv value).
 Proof.
   destruct (Nat.eqb (lvalue_root lv) root) eqn:E; intros H.
   - apply Nat.eqb_eq in E. destruct lv as [w id|]; [|discriminate].
     apply Nat.eqb_eq in H. subst w. right. split; reflexivity.
   - left. rewrite resolve_update_root. now apply Nat.eqb_neq.
 Qed.
 Lemma update_bit root s u : BitRoot root s -> BitUpdate root u -> BitRoot root (apply_update s u).
 Proof.
   intros H [Hother|[Ho Hw]].
   - unfold BitRoot. rewrite read_signal_apply_update_other by exact Hother. exact H.
   - destruct (Nat.eq_dec (update_signal u) root) as [E|E].
     + unfold BitRoot, apply_update. rewrite E, read_signal_write_same.
       rewrite Ho, Hw. apply bit_slice. exact H.
     + unfold BitRoot. rewrite read_signal_apply_update_other by exact E. exact H.
 Qed.
 Lemma apply_updates_bit root us s : Forall (BitUpdate root) us -> BitRoot root s ->
   BitRoot root (apply_updates s us).
 Proof. intros Hu. induction Hu in s |- *; cbn; auto. intros Hs. apply IHHu. now apply update_bit. Qed.
 Lemma apply_nba_bit root us s : Forall (BitUpdate root) us -> BitRoot root s ->
   BitRoot root (apply_nba s us).
 Proof.
   intros Hu. induction Hu in s |- *; cbn [apply_nba fold_left]; auto.
   intros Hs. apply IHHu. now apply update_bit.
 Qed.
 Definition ExecBit root es := BitRoot root (blocking_state es) /\
   Forall (BitUpdate root) (pending_nba es) /\ Forall (BitUpdate root) (emitted_updates es).
 Lemma selected_bit root s v arms default :
   forallb (fun a => bit_writesb root (snd a)) arms = true ->
   bit_writesb root default = true -> bit_writesb root (select_case_stmt s v arms default) = true.
 Proof.
   induction arms as [|[key body] rest IH] in default |- *; cbn; auto.
   intros H Hd. apply andb_true_iff in H as [Hb Hr].
   destruct key as [key|]; [destruct (v =? eval_expr s key)|]; auto.
 Qed.
 Theorem exec_bit fuel st root es : bit_writesb root st = true -> ExecBit root es ->
   ExecBit root (exec_stmt fuel st es).
 Proof.
   induction fuel as [|fuel IH] in st, es |- *; [auto|].
   destruct st as [|nba e lv|xs|g yes no|e arms]; cbn [bit_writesb]; intros H Hb.
   - exact Hb.
   - pose proof (resolved_bit root (blocking_state es) lv (eval_expr (blocking_state es) e) H) as Hu.
     destruct Hb as [Hs [Hp He]]. destruct nba; unfold ExecBit; cbn [exec_stmt blocking_state pending_nba emitted_updates].
     + split; [exact Hs|]. split; apply Forall_app; split; auto; constructor; auto.
     + split; [now apply update_bit|]. split; [exact Hp|]. apply Forall_app. split; auto.
   - cbn [exec_stmt]. induction xs as [|x xs IHr] in es, H, Hb |- *; cbn [fold_left]; [exact Hb|].
     apply andb_true_iff in H as [Hx Hxs]. apply IHr; [exact Hxs|]. now apply IH.
   - apply andb_true_iff in H as [Hy Hn]. cbn [exec_stmt].
     destruct (eval_expr (blocking_state es) g =? 0); apply IH; assumption.
   - cbn [exec_stmt]. apply IH; [apply selected_bit; [exact H|reflexivity]|exact Hb].
 Qed.
 Definition program_bitb p root := forallb (fun proc => bit_writesb root (process_body proc)) (processes p).
 Lemma process_bit p root proc s : bit_writesb root (process_body proc) = true -> BitRoot root s ->
   BitRoot root (run_process p s proc) /\ Forall (BitUpdate root) (process_updates p s proc).
 Proof.
   intros H Hs. pose proof (exec_bit (statement_fuel p) (process_body proc) root
     {| blocking_state := s; pending_nba := []; emitted_updates := [] |} H
     ltac:(repeat split; auto; constructor)) as [Hb [Hp He]].
   split; [unfold run_process; now apply apply_nba_bit|exact He].
 Qed.
 Lemma process_checked p root proc : program_bitb p root = true -> In proc (processes p) ->
   bit_writesb root (process_body proc) = true.
 Proof. intros H Hi. unfold program_bitb in H. now apply forallb_forall with (x:=proc) in H. Qed.
 Lemma fold_bit p root xs s : program_bitb p root = true ->
   (forall proc, In proc xs -> In proc (processes p)) -> BitRoot root s ->
   BitRoot root (fold_left (run_process p) xs s).
 Proof.
   intros H. induction xs as [|proc xs IH] in s |- *; cbn; auto.
   intros Hin Hs. apply IH; [intros q Hq; apply Hin; now right|].
   exact (proj1 (process_bit p root proc s
     (process_checked p root proc H (Hin proc (or_introl eq_refl))) Hs)).
 Qed.
 Lemma round_bit p root s : program_bitb p root = true -> BitRoot root s -> BitRoot root (comb_round p s).
 Proof.
   intros H Hs. unfold comb_round. apply fold_bit; auto.
   intros proc Hin. apply filter_In in Hin. tauto.
 Qed.
 Lemma iter_bit p root n s : program_bitb p root = true -> BitRoot root s -> BitRoot root (comb_iter p n s).
 Proof. intros H. induction n in s |- *; cbn; auto. intros Hs. apply IHn. now apply round_bit. Qed.
 Lemma lfp_bit p root s : program_bitb p root = true -> BitRoot root s -> BitRoot root (lfp_candidate p s).
 Proof. apply iter_bit. Qed.
 Lemma initialize_bit p root s : program_bitb p root = true -> BitRoot root s -> BitRoot root (initialize p s).
 Proof.
   intros Hp Hs. unfold initialize. apply fold_bit; auto.
   intros proc Hin. apply filter_In in Hin. tauto.
 Qed.
 Lemma zero_state_bit n root : BitRoot root (repeat 0 n).
 Proof.
   unfold BitRoot, Bit. left. induction n in root |- *; destruct root; cbn; auto.
 Qed.
 Lemma phase_bit p root ev s : program_bitb p root = true -> changed_signal ev <> root ->
   BitRoot root s -> BitRoot root (PhaseSemantics p ev s).
 Proof.
   intros Hp He Hs.
   assert (Hd : BitRoot root (phase_driven_state p ev s)).
   { unfold phase_driven_state. apply lfp_bit; [exact Hp|].
     unfold BitRoot. rewrite read_signal_write_other by exact He. exact Hs. }
   unfold PhaseSemantics, phase_execute_order, execute_process_order. apply lfp_bit; [exact Hp|].
   apply apply_updates_bit; [|exact Hd]. apply Forall_forall. intros u Hu.
   apply in_flat_map in Hu as [proc [Hproc Hu]].
   unfold selected_on_transition in Hproc. apply filter_In in Hproc as [Hin _].
   pose proof (proj2 (process_bit p root proc (phase_driven_state p ev s)
     (process_checked p root proc Hp Hin) Hd)) as H.
   now apply Forall_forall with (x:=u) in H.
 Qed.
 Print Assumptions phase_bit.
End ExtendedSVBitInvariant.
