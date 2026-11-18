(** Non-interference through the actual phase semantics (design independent).

    Two states that agree outside a set [T] of "tainted" roots (same length, same value on every root not in [T])
    are run through [initialize], [comb_round]/[comb_iter]/[lfp_candidate] and [PhaseSemantics].  A computable checker
    runs the concrete semantics on ONE of the two states and tracks the taint set: an expression is independent of [T]
    if it reads no tainted root, where a condition only needs the branch its (independent) guard selects on the
    concrete state; an assignment whose value or index is not independent taints its root; an [if]/[case] whose guard
    is not independent, or a sequential process whose clock/event signal is tainted, makes the checker fail ([None]).
    Soundness: if the checker returns [Some T'] then the two results agree outside [T'].

    Typical use: one state has a symbolic input (e.g. a ROM image), the other the same input set to 0; the checker is
    evaluated by [vm_compute] on the concrete state only, and every root outside [T'] of the symbolic run has the value
    of the concrete run.  No symbolic value is ever computed.
    proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection.
Local Open Scope Z_scope.

Module ExtendedSVNonInterference.

Definition memb (x:signal) (T:list signal) : bool := existsb (Nat.eqb x) T.
Lemma memb_cons_self x T : memb x (x :: T) = true.
Proof. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Definition Sub (T T':list signal) : Prop := forall x, memb x T = true -> memb x T' = true.
Lemma sub_refl T : Sub T T. Proof. intros x H. exact H. Qed.
Lemma sub_trans a b c : Sub a b -> Sub b c -> Sub a c. Proof. intros H1 H2 x H. exact (H2 x (H1 x H)). Qed.
Lemma sub_cons x T : Sub T (x :: T). Proof. intros y H. unfold memb in *. cbn. rewrite H. apply orb_true_r. Qed.
Lemma sub_out T T' x : Sub T T' -> memb x T' = false -> memb x T = false.
Proof. intros H E. destruct (memb x T) eqn:M; [rewrite (H x M) in E; discriminate|reflexivity]. Qed.

(** ---- agreement of states, updates, execution states ---- *)
Definition Agree (T:list signal) (s t:State) : Prop :=
 length s = length t /\ forall x, memb x T = false -> read_signal s x = read_signal t x.
Lemma agree_sub T T' s t : Sub T T' -> Agree T s t -> Agree T' s t.
Proof. intros H [L R]. split; [exact L|]. intros x E. exact (R x (sub_out T T' x H E)). Qed.

Lemma write_length s x v : length (write_signal s x v) = Nat.max (length s) (S x).
Proof. revert s. induction x as [|x IH]; intros [|h s]; cbn [write_signal length]; try rewrite IH; cbn [length]; lia. Qed.

Lemma read_write s x y v : read_signal (write_signal s x v) y = if Nat.eqb x y then v else read_signal s y.
Proof. destruct (Nat.eqb x y) eqn:E.
 - apply Nat.eqb_eq in E. subst. apply read_signal_write_same.
 - apply Nat.eqb_neq in E. apply read_signal_write_other. exact E. Qed.

(** same root on both sides; the values may differ only if the root is tainted *)
Lemma agree_write T s t x v w : Agree T s t -> (memb x T = true \/ v = w) -> Agree T (write_signal s x v) (write_signal t x w).
Proof. intros [L R] H. split; [rewrite !write_length, L; reflexivity|]. intros y E. rewrite !read_write.
 destruct (Nat.eqb x y) eqn:Exy; [|exact (R y E)].
 apply Nat.eqb_eq in Exy. subst y. destruct H as [H|H]; [rewrite H in E; discriminate|exact H]. Qed.

Definition UAgree (T:list signal) (u v:Update) : Prop :=
 update_signal u = update_signal v /\ (memb (update_signal u) T = true \/ u = v).
Lemma uagree_sub T T' u v : Sub T T' -> UAgree T u v -> UAgree T' u v.
Proof. intros H [E [M|M]]; split; auto. Qed.
Lemma forall2_sub T T' l1 l2 : Sub T T' -> Forall2 (UAgree T) l1 l2 -> Forall2 (UAgree T') l1 l2.
Proof. intros H F. induction F; constructor; auto. exact (uagree_sub T T' _ _ H H0). Qed.

Lemma apply_update_agree T s t u v : Agree T s t -> UAgree T u v -> Agree T (apply_update s u) (apply_update t v).
Proof. intros HA [Es [M | ->]]; unfold apply_update.
 - rewrite <- Es. apply agree_write; [exact HA|left; exact M].
 - apply agree_write; [exact HA|]. destruct (memb (update_signal v) T) eqn:M; [left; reflexivity|right].
   destruct HA as [_ R]. rewrite (R _ M). reflexivity. Qed.
Lemma apply_updates_agree T s t l1 l2 : Agree T s t -> Forall2 (UAgree T) l1 l2 -> Agree T (apply_updates s l1) (apply_updates t l2).
Proof. intros HA F. revert s t HA. induction F; intros s t HA; cbn; [exact HA|]. apply IHF. exact (apply_update_agree T s t x y HA H). Qed.
Lemma apply_nba_agree T s t l1 l2 : Agree T s t -> Forall2 (UAgree T) l1 l2 -> Agree T (apply_nba s l1) (apply_nba t l2).
Proof. intros HA F. revert s t HA. induction F; intros s t HA; cbn; [exact HA|]. apply IHF. exact (apply_update_agree T s t x y HA H). Qed.

Definition EAgree (T:list signal) (a b:ExecState) : Prop :=
 Agree T (blocking_state a) (blocking_state b) /\ Forall2 (UAgree T) (pending_nba a) (pending_nba b) /\
 Forall2 (UAgree T) (emitted_updates a) (emitted_updates b).
Lemma eagree_sub T T' a b : Sub T T' -> EAgree T a b -> EAgree T' a b.
Proof. intros H (A & B & C). split; [exact (agree_sub T T' _ _ H A)|]. split; [exact (forall2_sub T T' _ _ H B)|exact (forall2_sub T T' _ _ H C)]. Qed.

(** ---- expressions ---- *)
Fixpoint indep (T:list signal) (s:State) (e:Expr) : bool :=
 match e with
 | EConst _ _ => true
 | EVar _ x => negb (memb x T)
 | ESel _ a b | EConcat _ a b | EBinary _ _ a b => indep T s a && indep T s b
 | EReplicate _ _ a | EExtend _ _ a | EUnary _ _ a => indep T s a
 | ECond _ g a b => indep T s g && (if Z.eqb (eval_expr s g) 0 then indep T s b else indep T s a)
 end.

Theorem indep_eval T s t e : Agree T s t -> indep T s e = true -> eval_expr t e = eval_expr s e.
Proof. intros HA. pose proof HA as [_ R]. induction e; cbn [indep eval_expr]; intro H; try rewrite !andb_true_iff in H.
 - reflexivity.
 - apply negb_true_iff in H. rewrite (R _ H). reflexivity.
 - destruct H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
 - destruct H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
 - rewrite (IHe H). reflexivity.
 - rewrite (IHe H). reflexivity.
 - rewrite (IHe H). reflexivity.
 - destruct H as [H1 H2]. rewrite (IHe1 H1), (IHe2 H2). reflexivity.
 - destruct H as [H1 H2]. rewrite (IHe1 H1). destruct (Z.eqb (eval_expr s e1) 0).
   + rewrite (IHe3 H2). reflexivity.
   + rewrite (IHe2 H2). reflexivity.
Qed.

Fixpoint lv_indep (T:list signal) (s:State) (lv:LValue) : bool :=
 match lv with LVar _ _ => true | LSel _ b l => lv_indep T s b && indep T s l end.

Lemma resolve_eq T s t lv : Agree T s t -> lv_indep T s lv = true -> resolve_lvalue t lv = resolve_lvalue s lv.
Proof. intro HA. induction lv as [w x|w b IH l]; cbn [lv_indep resolve_lvalue]; intro H; [reflexivity|].
 apply andb_true_iff in H as [H1 H2]. rewrite (IH H1), (indep_eval T s t l HA H2). reflexivity. Qed.

Lemma resolve_signal s lv : fst (fst (resolve_lvalue s lv)) = lvalue_root lv.
Proof. induction lv as [w x|w b IH l]; cbn [resolve_lvalue lvalue_root]; [reflexivity|].
 destruct (resolve_lvalue s b) as [[i o] w0]. exact IH. Qed.

Lemma update_signal_root s lv v : update_signal (resolve_update s lv v) = lvalue_root lv.
Proof. unfold resolve_update. pose proof (resolve_signal s lv) as H. destruct (resolve_lvalue s lv) as [[i o] w0]. exact H. Qed.

Definition keys_indep (T:list signal) (s:State) (arms:list (option Expr * Stmt)) : bool :=
 forallb (fun a => match fst a with None => true | Some k => indep T s k end) arms.

Lemma select_eq T s t v arms d : Agree T s t -> keys_indep T s arms = true ->
 select_case_stmt t v arms d = select_case_stmt s v arms d.
Proof. intros HA. revert d. induction arms as [|[[k|] b] rest IH]; intros d H; cbn [select_case_stmt]; [reflexivity| |].
 - cbn in H. apply andb_true_iff in H as [H1 H2]. rewrite (indep_eval T s t k HA H1).
   destruct (Z.eqb v (eval_expr s k)); [reflexivity|exact (IH d H2)].
 - cbn in H. exact (IH b H).
Qed.

(** ---- statements: the checker runs the concrete execution and returns the grown taint set ---- *)
Fixpoint aseq (g : Stmt -> ExecState -> list signal -> option (list signal)) (ex : Stmt -> ExecState -> ExecState)
 (sts : list Stmt) (es : ExecState) (T : list signal) : option (list signal) :=
 match sts with
 | [] => Some T
 | st :: r => match g st es T with Some T' => aseq g ex r (ex st es) T' | None => None end
 end.

Fixpoint aexec (fuel:nat) (st:Stmt) (es:ExecState) (T:list signal) : option (list signal) :=
 match fuel with
 | O => Some T
 | S f =>
   match st with
   | SSkip => Some T
   | SAssign _ rhs lhs =>
       if lv_indep T (blocking_state es) lhs && indep T (blocking_state es) rhs then Some T else Some (lvalue_root lhs :: T)
   | SSeq sts => aseq (aexec f) (exec_stmt f) sts es T
   | SIf g y n =>
       if indep T (blocking_state es) g
       then aexec f (if Z.eqb (eval_expr (blocking_state es) g) 0 then n else y) es T else None
   | SCase e arms =>
       if indep T (blocking_state es) e && keys_indep T (blocking_state es) arms
       then aexec f (select_case_stmt (blocking_state es) (eval_expr (blocking_state es) e) arms SSkip) es T else None
   end
 end.

Lemma aseq_sub g ex : (forall st es T T', g st es T = Some T' -> Sub T T') ->
 forall sts es T T', aseq g ex sts es T = Some T' -> Sub T T'.
Proof. intros Hg sts. induction sts as [|st r IH]; intros es T T' H; cbn in H.
 - injection H as <-. apply sub_refl.
 - destruct (g st es T) as [T1|] eqn:E; [|discriminate]. exact (sub_trans _ _ _ (Hg _ _ _ _ E) (IH _ _ _ H)). Qed.

Lemma aexec_sub fuel : forall st es T T', aexec fuel st es T = Some T' -> Sub T T'.
Proof. induction fuel as [|f IH]; intros st es T T' H; cbn in H; [injection H as <-; apply sub_refl|].
 destruct st.
 - injection H as <-. apply sub_refl.
 - destruct (lv_indep T (blocking_state es) lhs && indep T (blocking_state es) rhs); injection H as <-; [apply sub_refl|apply sub_cons].
 - exact (aseq_sub (aexec f) (exec_stmt f) IH statements es T T' H).
 - destruct (indep T (blocking_state es) guard); [exact (IH _ _ _ _ H)|discriminate].
 - destruct (indep T (blocking_state es) scrutinee && keys_indep T (blocking_state es) arms); [exact (IH _ _ _ _ H)|discriminate].
Qed.

Lemma aseq_sound g ex :
 (forall st a b T T', g st a T = Some T' -> EAgree T a b -> EAgree T' (ex st a) (ex st b)) ->
 forall sts a b T T', aseq g ex sts a T = Some T' -> EAgree T a b ->
 EAgree T' (fold_left (fun es' st' => ex st' es') sts a) (fold_left (fun es' st' => ex st' es') sts b).
Proof. intros Hg sts. induction sts as [|st r IH]; intros a b T T' H HA; cbn in H |- *.
 - injection H as <-. exact HA.
 - destruct (g st a T) as [T1|] eqn:E; [|discriminate]. exact (IH _ _ _ _ H (Hg _ _ _ _ _ E HA)). Qed.

Theorem aexec_sound fuel : forall st a b T T', aexec fuel st a T = Some T' -> EAgree T a b ->
 EAgree T' (exec_stmt fuel st a) (exec_stmt fuel st b).
Proof. induction fuel as [|f IH]; intros st a b T T' H HA; cbn in H |- *; [injection H as <-; exact HA|].
 destruct st.
 - injection H as <-. exact HA.
 - pose proof HA as (A & Pn & Em). set (ua := resolve_update (blocking_state a) lhs (eval_expr (blocking_state a) rhs)).
   set (ub := resolve_update (blocking_state b) lhs (eval_expr (blocking_state b) rhs)).
   assert (HU : UAgree T' ua ub).
   { destruct (lv_indep T (blocking_state a) lhs && indep T (blocking_state a) rhs) eqn:Ei; injection H as <-.
     - apply andb_true_iff in Ei as [E1 E2]. split; [unfold ua, ub; rewrite !update_signal_root; reflexivity|right].
       unfold ua, ub, resolve_update. rewrite (resolve_eq T _ _ lhs A E1), (indep_eval T _ _ rhs A E2). reflexivity.
     - split; [unfold ua, ub; rewrite !update_signal_root; reflexivity|left]. unfold ua. rewrite update_signal_root. apply memb_cons_self. }
   assert (HS : Sub T T') by (destruct (lv_indep T (blocking_state a) lhs && indep T (blocking_state a) rhs); injection H as <-; [apply sub_refl|apply sub_cons]).
   destruct (eagree_sub T T' a b HS HA) as (A' & Pn' & Em'). fold ua ub.
   destruct nonblocking; cbn [blocking_state pending_nba emitted_updates]; split; [exact A'| |exact (apply_update_agree T' _ _ ua ub A' HU)|].
   + split; apply Forall2_app; auto.
   + split; [exact Pn'|]. apply Forall2_app; auto.
 - exact (aseq_sound (aexec f) (exec_stmt f) (IH) statements a b T T' H HA).
 - destruct (indep T (blocking_state a) guard) eqn:Eg; [|discriminate].
   rewrite (indep_eval T _ _ guard (proj1 HA) Eg). exact (IH _ _ _ _ _ H HA).
 - destruct (indep T (blocking_state a) scrutinee && keys_indep T (blocking_state a) arms) eqn:Eg; [|discriminate].
   apply andb_true_iff in Eg as [E1 E2]. rewrite (indep_eval T _ _ scrutinee (proj1 HA) E1), (select_eq T _ _ _ arms SSkip (proj1 HA) E2).
   exact (IH _ _ _ _ _ H HA).
Qed.

(** ---- processes, rounds, LFP candidate, initialisation ---- *)
Definition es0 (s:State) : ExecState := {| blocking_state := s; pending_nba := []; emitted_updates := [] |}.
Definition arun (p:Program) (T:list signal) (s:State) (proc:Process) : option (list signal) :=
 aexec (statement_fuel p) (process_body proc) (es0 s) T.

Lemma arun_sub p T T' s proc : arun p T s proc = Some T' -> Sub T T'.
Proof. exact (aexec_sub _ _ _ _ _). Qed.

Theorem arun_sound p T T' s t proc : arun p T s proc = Some T' -> Agree T s t ->
 Agree T' (run_process p s proc) (run_process p t proc) /\ Forall2 (UAgree T') (process_updates p s proc) (process_updates p t proc).
Proof. intros H HA. assert (E0 : EAgree T (es0 s) (es0 t)) by (split; [exact HA|split; constructor]).
 pose proof (aexec_sound _ _ _ _ _ _ H E0) as (A & Pn & Em). unfold run_process, process_updates. fold (es0 s) (es0 t).
 split; [exact (apply_nba_agree T' _ _ _ _ A Pn)|exact Em]. Qed.

(** a combinational process whose checker run fails (a guard reads a tainted root) is still harmless if it is
    blocking-only and writes inside the state: then all its writers are tainted ("havoc") *)
Fixpoint bonly (st:Stmt) : bool :=
 match st with
 | SSkip => true | SAssign nba _ _ => negb nba
 | SSeq xs => forallb bonly xs
 | SIf _ y n => bonly y && bonly n
 | SCase _ arms => forallb (fun a => bonly (snd a)) arms
 end.

Lemma bonly_select s v arms d : forallb (fun a => bonly (snd a)) arms = true -> bonly d = true -> bonly (select_case_stmt s v arms d) = true.
Proof. revert d. induction arms as [|[[k|] b] rest IH]; intros d H Hd; cbn [select_case_stmt]; [exact Hd| |].
 - cbn in H. apply andb_true_iff in H as [H1 H2]. destruct (Z.eqb v (eval_expr s k)); [exact H1|exact (IH d H2 Hd)].
 - cbn in H. apply andb_true_iff in H as [H1 H2]. exact (IH b H2 H1). Qed.

Lemma havoc_exec fuel : forall st es, bonly st = true -> (forall r, In r (stmt_writers st) -> (r < length (blocking_state es))%nat) ->
 pending_nba (exec_stmt fuel st es) = pending_nba es /\ length (blocking_state (exec_stmt fuel st es)) = length (blocking_state es).
Proof. induction fuel as [|f IH]; intros st es Hb Hw; cbn; [split; reflexivity|].
 destruct st as [|nba rhs lhs|sts|g y n|e arms].
 - split; reflexivity.
 - cbn in Hb. destruct nba; [discriminate|]. cbn. split; [reflexivity|]. unfold apply_update. rewrite write_length.
   rewrite update_signal_root. pose proof (Hw (lvalue_root lhs) (or_introl eq_refl)). lia.
 - cbn in Hb, Hw. revert es Hw. induction sts as [|st r IHs]; intros es Hw; cbn; [split; reflexivity|].
   cbn in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
   assert (Hw1 : forall x, In x (stmt_writers st) -> (x < length (blocking_state es))%nat) by (intros x Hx; apply Hw; apply in_or_app; left; exact Hx).
   destruct (IH st es Hb1 Hw1) as [P1 L1].
   destruct (IHs Hb2 (exec_stmt f st es)) as [P2 L2].
   + intros x Hx. rewrite L1. apply Hw. apply in_or_app. right. exact Hx.
   + rewrite P2, P1, L2, L1. split; reflexivity.
 - cbn in Hb, Hw. apply andb_true_iff in Hb as [Hy Hn]. destruct (Z.eqb (eval_expr (blocking_state es) g) 0).
   + apply IH; [exact Hn|]. intros x Hx. apply Hw. apply in_or_app. right. exact Hx.
   + apply IH; [exact Hy|]. intros x Hx. apply Hw. apply in_or_app. left. exact Hx.
 - cbn in Hb, Hw. apply IH; [exact (bonly_select _ _ arms SSkip Hb eq_refl)|]. intros x Hx.
   apply Hw. pose proof (select_case_writers _ _ _ _ _ Hx) as Hi. cbn in Hi. exact Hi.
Qed.

Definition arun_c (p:Program) (T:list signal) (s:State) (proc:Process) : option (list signal) :=
 match arun p T s proc with
 | Some T' => Some T'
 | None => if bonly (process_body proc) && forallb (fun r => Nat.ltb r (length s)) (process_writers proc)
           then Some (process_writers proc ++ T) else None
 end.

Lemma memb_app_false x a b : memb x (a ++ b) = false -> ~ In x a /\ memb x b = false.
Proof. unfold memb. rewrite existsb_app. intro H. apply orb_false_iff in H as [H1 H2]. split; [|exact H2].
 intro Hin. assert (E : existsb (Nat.eqb x) a = true) by (apply existsb_exists; exists x; split; [exact Hin|apply Nat.eqb_refl]). exact (eq_true_false_abs _ E H1). Qed.
Lemma sub_app a b : Sub b (a ++ b).
Proof. intros x H. unfold memb in *. rewrite existsb_app. apply orb_true_iff. right. exact H. Qed.

Theorem arun_c_sound p T T' s t proc : arun_c p T s proc = Some T' -> Agree T s t -> Agree T' (run_process p s proc) (run_process p t proc).
Proof. unfold arun_c. intros H HA. destruct (arun p T s proc) as [T1|] eqn:E.
 - injection H as <-. exact (proj1 (arun_sound p T T1 s t proc E HA)).
 - destruct (bonly (process_body proc) && forallb (fun r => Nat.ltb r (length s)) (process_writers proc)) eqn:Hc; [|discriminate].
   injection H as <-. apply andb_true_iff in Hc as [Hb Hw]. rewrite forallb_forall in Hw.
   assert (Hws : forall r, In r (stmt_writers (process_body proc)) -> (r < length (blocking_state (es0 s)))%nat)
    by (intros r Hr; apply Nat.ltb_lt; exact (Hw r Hr)).
   assert (Hwt : forall r, In r (stmt_writers (process_body proc)) -> (r < length (blocking_state (es0 t)))%nat)
    by (intros r Hr; cbn; rewrite <- (proj1 HA); apply Nat.ltb_lt; exact (Hw r Hr)).
   destruct (havoc_exec (statement_fuel p) _ (es0 s) Hb Hws) as [Ps Ls].
   destruct (havoc_exec (statement_fuel p) _ (es0 t) Hb Hwt) as [Pt Lt].
   assert (Es : run_process p s proc = blocking_state (exec_stmt (statement_fuel p) (process_body proc) (es0 s)))
    by (unfold run_process; fold (es0 s); rewrite Ps; reflexivity).
   assert (Et : run_process p t proc = blocking_state (exec_stmt (statement_fuel p) (process_body proc) (es0 t)))
    by (unfold run_process; fold (es0 t); rewrite Pt; reflexivity).
   rewrite Es, Et. split; [rewrite Ls, Lt; exact (proj1 HA)|].
   intros x Hx. apply memb_app_false in Hx as [Hx1 Hx2].
   destruct (exec_stmt_preserves_unwritten_root (statement_fuel p) (process_body proc) x (es0 s) Hx1) as [Rs _].
   destruct (exec_stmt_preserves_unwritten_root (statement_fuel p) (process_body proc) x (es0 t) Hx1) as [Rt _].
   rewrite Rs, Rt. exact (proj2 HA x Hx2).
Qed.

Lemma arun_c_sub p T T' s proc : arun_c p T s proc = Some T' -> Sub T T'.
Proof. unfold arun_c. intro H. destruct (arun p T s proc) as [T1|] eqn:E.
 - injection H as <-. exact (arun_sub p T T1 s proc E).
 - destruct (bonly (process_body proc) && forallb (fun r => Nat.ltb r (length s)) (process_writers proc)); [|discriminate].
   injection H as <-. apply sub_app. Qed.

Fixpoint afold (p:Program) (procs:list Process) (s:State) (T:list signal) : option (list signal) :=
 match procs with
 | [] => Some T
 | pr :: r => match arun_c p T s pr with Some T' => afold p r (run_process p s pr) T' | None => None end
 end.

Theorem afold_sound p procs : forall s t T T', afold p procs s T = Some T' -> Agree T s t ->
 Agree T' (fold_left (run_process p) procs s) (fold_left (run_process p) procs t).
Proof. induction procs as [|pr r IH]; intros s t T T' H HA; cbn in H |- *; [injection H as <-; exact HA|].
 destruct (arun_c p T s pr) as [T1|] eqn:E; [|discriminate]. exact (IH _ _ _ _ H (arun_c_sound p T T1 s t pr E HA)). Qed.

Lemma afold_sub p procs : forall s T T', afold p procs s T = Some T' -> Sub T T'.
Proof. induction procs as [|pr r IH]; intros s T T' H; cbn in H; [injection H as <-; apply sub_refl|].
 destruct (arun_c p T s pr) as [T1|] eqn:E; [|discriminate]. exact (sub_trans _ _ _ (arun_c_sub p T T1 s pr E) (IH _ _ _ H)). Qed.

Fixpoint aiter (p:Program) (n:nat) (s:State) (T:list signal) : option (list signal) :=
 match n with
 | O => Some T
 | S k => match afold p (filter is_comb (processes p)) s T with Some T' => aiter p k (comb_round p s) T' | None => None end
 end.

Theorem aiter_sound p n : forall s t T T', aiter p n s T = Some T' -> Agree T s t -> Agree T' (comb_iter p n s) (comb_iter p n t).
Proof. induction n as [|k IH]; intros s t T T' H HA; cbn in H |- *; [injection H as <-; exact HA|].
 destruct (afold p (filter is_comb (processes p)) s T) as [T1|] eqn:E; [|discriminate].
 exact (IH _ _ _ _ H (afold_sound p _ s t T T1 E HA)). Qed.

Lemma aiter_sub p n : forall s T T', aiter p n s T = Some T' -> Sub T T'.
Proof. induction n as [|k IH]; intros s T T' H; cbn in H; [injection H as <-; apply sub_refl|].
 destruct (afold p (filter is_comb (processes p)) s T) as [T1|] eqn:E; [|discriminate].
 exact (sub_trans _ _ _ (afold_sub p _ s T T1 E) (IH _ _ _ H)). Qed.

Definition ainit (p:Program) (seed:State) (T:list signal) : option (list signal) := afold p (filter is_initial (processes p)) seed T.
Theorem ainit_sound p seed seed' T T' : ainit p seed T = Some T' -> Agree T seed seed' -> Agree T' (initialize p seed) (initialize p seed').
Proof. intros H HA. unfold initialize. exact (afold_sound p _ seed seed' T T' H HA). Qed.

Theorem alfp_sound p s t T T' : aiter p (lfp_fuel p) s T = Some T' -> Agree T s t -> Agree T' (lfp_candidate p s) (lfp_candidate p t).
Proof. intros H HA. unfold lfp_candidate. exact (aiter_sound p _ s t T T' H HA). Qed.

(** ---- one physical phase ---- *)
Definition events_ok (T:list signal) (p:Program) : bool :=
 forallb (fun proc => forallb (fun spec => negb (memb (event_signal spec) T)) (process_events proc)) (processes p).

(** update lists of a phase: pairwise agreeing updates, plus updates of tainted roots inside the state on either side *)
Inductive LA (T:list signal) (n:nat) : list Update -> list Update -> Prop :=
 | LA_nil : LA T n [] []
 | LA_cons u v l1 l2 : UAgree T u v -> LA T n l1 l2 -> LA T n (u :: l1) (v :: l2)
 | LA_left u l1 l2 : memb (update_signal u) T = true -> (update_signal u < n)%nat -> LA T n l1 l2 -> LA T n (u :: l1) l2
 | LA_right v l1 l2 : memb (update_signal v) T = true -> (update_signal v < n)%nat -> LA T n l1 l2 -> LA T n l1 (v :: l2).

Lemma la_sub T T' n l1 l2 : Sub T T' -> LA T n l1 l2 -> LA T' n l1 l2.
Proof. intros H L. induction L.
 - constructor.
 - apply LA_cons; [exact (uagree_sub T T' _ _ H H0)|exact IHL].
 - apply LA_left; [exact (H _ H0)|exact H1|exact IHL].
 - apply LA_right; [exact (H _ H0)|exact H1|exact IHL]. Qed.
Lemma la_app T n a b c d : LA T n a b -> LA T n c d -> LA T n (a ++ c) (b ++ d).
Proof. intros L1 L2. induction L1; cbn.
 - exact L2.
 - apply LA_cons; assumption.
 - apply LA_left; assumption.
 - apply LA_right; assumption. Qed.
Lemma la_forall2 T n l1 l2 : Forall2 (UAgree T) l1 l2 -> LA T n l1 l2.
Proof. intro F. induction F; [constructor|apply LA_cons; assumption]. Qed.
Lemma la_tainted T n l1 l2 : (forall u, In u l1 -> memb (update_signal u) T = true /\ (update_signal u < n)%nat) ->
 (forall u, In u l2 -> memb (update_signal u) T = true /\ (update_signal u < n)%nat) -> LA T n l1 l2.
Proof. revert l2. induction l1 as [|u l1 IH]; intros l2 H1 H2.
 - induction l2 as [|v l2 IH2]; [constructor|]. destruct (H2 v (or_introl eq_refl)) as [M L].
   apply LA_right; [exact M|exact L|]. apply IH2. intros u Hu. exact (H2 u (or_intror Hu)).
 - destruct (H1 u (or_introl eq_refl)) as [M L]. apply LA_left; [exact M|exact L|]. apply IH; [|exact H2].
   intros w Hw. exact (H1 w (or_intror Hw)). Qed.

Lemma apply_update_length s u : (length s <= length (apply_update s u))%nat.
Proof. unfold apply_update. rewrite write_length. lia. Qed.
Lemma agree_tainted_left T s t u : Agree T s t -> memb (update_signal u) T = true -> (update_signal u < length s)%nat ->
 Agree T (apply_update s u) t.
Proof. intros [L R] M Hl. unfold apply_update. split.
 - rewrite write_length, <- L. lia.
 - intros x E. rewrite read_write. destruct (Nat.eqb (update_signal u) x) eqn:Ex; [|exact (R x E)].
   apply Nat.eqb_eq in Ex. subst x. rewrite M in E. discriminate. Qed.
Lemma agree_sym T s t : Agree T s t -> Agree T t s.
Proof. intros [L R]. split; [symmetry; exact L|intros x E; symmetry; exact (R x E)]. Qed.

Theorem la_apply T n l1 l2 : LA T n l1 l2 -> forall s t, Agree T s t -> (n <= length s)%nat ->
 Agree T (apply_updates s l1) (apply_updates t l2).
Proof. intro L. induction L; intros s t HA Hn; cbn [apply_updates].
 - exact HA.
 - apply IHL; [exact (apply_update_agree T s t u v HA H)|]. pose proof (apply_update_length s u). lia.
 - apply IHL; [exact (agree_tainted_left T s t u HA H ltac:(lia))|]. pose proof (apply_update_length s u). lia.
 - apply IHL; [|exact Hn]. apply agree_sym. apply agree_tainted_left; [exact (agree_sym _ _ _ HA)|exact H|].
   destruct HA as [Ls _]. rewrite <- Ls. lia. Qed.

Lemma exec_emitted_writers fuel : forall st es u, In u (emitted_updates (exec_stmt fuel st es)) ->
 In u (emitted_updates es) \/ In (update_signal u) (stmt_writers st).
Proof. induction fuel as [|f IH]; intros st es u H; cbn in H; [left; exact H|].
 destruct st as [|nba rhs lhs|sts|g y n|e arms].
 - left; exact H.
 - destruct nba; cbn in H; apply in_app_or in H as [H|H]; try (left; exact H);
   destruct H as [<-|[]]; right; rewrite update_signal_root; left; reflexivity.
 - revert es H. induction sts as [|st r IHs]; intros es H; cbn in H; [left; exact H|].
   destruct (IHs _ H) as [H1|H1].
   + destruct (IH st es u H1) as [H2|H2]; [left; exact H2|right; cbn; apply in_or_app; left; exact H2].
   + right. cbn. apply in_or_app. right. exact H1.
 - destruct (Z.eqb (eval_expr (blocking_state es) g) 0); destruct (IH _ es u H) as [H1|H1]; try (left; exact H1); right; cbn; apply in_or_app; [right|left]; exact H1.
 - destruct (IH _ es u H) as [H1|H1]; [left; exact H1|]. right. cbn. pose proof (select_case_writers _ _ _ _ _ H1) as Hi. cbn in Hi. exact Hi.
Qed.

Lemma process_updates_writers p d proc u : In u (process_updates p d proc) -> In (update_signal u) (process_writers proc).
Proof. intro H. unfold process_updates in H. destruct (exec_emitted_writers _ _ _ u H) as [[]|H1]. exact H1. Qed.

Lemma memb_app_in x a b : In x a -> memb x (a ++ b) = true.
Proof. intro H. unfold memb. rewrite existsb_app. apply orb_true_iff. left. apply existsb_exists. exists x. split; [exact H|apply Nat.eqb_refl]. Qed.

Definition tnorm (T:list signal) : list signal := nodup Nat.eq_dec T.
Lemma memb_tnorm x T : memb x (tnorm T) = memb x T.
Proof. unfold memb, tnorm. destruct (existsb (Nat.eqb x) T) eqn:E.
 - apply existsb_exists in E as [y [Hy Ey]]. apply existsb_exists. exists y. split; [apply nodup_In; exact Hy|exact Ey].
 - apply not_true_iff_false. intro H. apply existsb_exists in H as [y [Hy Ey]]. apply nodup_In in Hy.
   assert (existsb (Nat.eqb x) T = true) by (apply existsb_exists; exists y; split; assumption). congruence. Qed.
Lemma sub_tnorm T : Sub T (tnorm T). Proof. intros x H. rewrite memb_tnorm. exact H. Qed.
Lemma sub_tnorm_inv T : Sub (tnorm T) T. Proof. intros x H. rewrite memb_tnorm in H. exact H. Qed.

(** every selected sequential process is checked against the taint of the driven state [Td] (all of them read the same
    driven state); a process whose checker run fails is "havoc": all its writers are tainted *)
Fixpoint aupds (p:Program) (order:list Process) (d:State) (Td Tacc:list signal) : option (list signal) :=
 match order with
 | [] => Some Tacc
 | pr :: r => match arun p Td d pr with
              | Some T1 => aupds p r d Td (tnorm (T1 ++ Tacc))
              | None => if forallb (fun x => Nat.ltb x (length d)) (process_writers pr) then aupds p r d Td (process_writers pr ++ Tacc) else None
              end
 end.

Lemma sub_app_l a b : Sub a (a ++ b).
Proof. intros x H. unfold memb in *. rewrite existsb_app. apply orb_true_iff. left. exact H. Qed.

Lemma aupds_sub p order : forall d Td Tacc T', aupds p order d Td Tacc = Some T' -> Sub Tacc T'.
Proof. induction order as [|pr r IH]; intros d Td Tacc T' H; cbn [aupds] in H; [injection H as <-; apply sub_refl|].
 destruct (arun p Td d pr) as [T1|] eqn:E.
 - exact (sub_trans _ _ _ (sub_trans _ _ _ (sub_app T1 Tacc) (sub_tnorm _)) (IH _ _ _ _ H)).
 - unfold process_writers in H. destruct (forallb (fun x => Nat.ltb x (length d)) (stmt_writers (process_body pr))); [|discriminate].
   exact (sub_trans _ _ _ (sub_app _ Tacc) (IH _ _ _ _ H)). Qed.

Theorem aupds_sound p order : forall d d' Td Tacc T', aupds p order d Td Tacc = Some T' -> Agree Td d d' ->
 LA T' (length d) (flat_map (process_updates p d) order) (flat_map (process_updates p d') order).
Proof. induction order as [|pr r IH]; intros d d' Td Tacc T' H HA; cbn [aupds flat_map] in H |- *; [constructor|].
 destruct (arun p Td d pr) as [T1|] eqn:E.
 - destruct (arun_sound p Td T1 d d' pr E HA) as [_ F]. pose proof (aupds_sub p r d Td _ T' H) as HS. apply la_app.
   + exact (la_forall2 _ _ _ _ (forall2_sub T1 T' _ _ (sub_trans _ _ _ (sub_trans _ _ _ (sub_app_l T1 Tacc) (sub_tnorm _)) HS) F)).
   + exact (IH _ _ _ _ _ H HA).
 - unfold process_writers in H. destruct (forallb (fun x => Nat.ltb x (length d)) (stmt_writers (process_body pr))) eqn:Hw; [|discriminate].
   fold (process_writers pr) in Hw, H.
   rewrite forallb_forall in Hw. pose proof (aupds_sub p r d Td _ T' H) as HS. apply la_app.
   + assert (K : forall q u, In u (process_updates p q pr) -> memb (update_signal u) T' = true /\ (update_signal u < length d)%nat).
     { intros q u Hu. pose proof (process_updates_writers p q pr u Hu) as Hi. split.
       - exact (HS _ (memb_app_in _ _ Tacc Hi)).
       - apply Nat.ltb_lt. exact (Hw _ Hi). }
     exact (la_tainted _ _ _ _ (K d) (K d')).
   + exact (IH _ _ _ _ _ H HA).
Qed.

Lemma existsb_ext_in' {A} (f g : A -> bool) l : (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof. induction l as [|a l IH]; intro H; cbn; [reflexivity|]. rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. exact (H x (or_intror Hx)). Qed.
Lemma filter_ext_in' {A} (f g : A -> bool) l : (forall x, In x l -> f x = g x) -> filter f l = filter g l.
Proof. induction l as [|a l IH]; intro H; cbn; [reflexivity|]. rewrite (H a (or_introl eq_refl)), IH; [reflexivity|]. intros x Hx. exact (H x (or_intror Hx)). Qed.

Lemma selected_eq p T pre pre' d d' : events_ok T p = true -> Agree T pre pre' -> Agree T d d' ->
 selected_on_transition p pre' d' = selected_on_transition p pre d.
Proof. intros Hok [_ R1] [_ R2]. unfold selected_on_transition. apply filter_ext_in'. intros proc Hin.
 unfold events_ok in Hok. rewrite forallb_forall in Hok. pose proof (Hok proc Hin) as Hp. rewrite forallb_forall in Hp.
 unfold process_matches_states. destruct (process_kind proc); [reflexivity|reflexivity|].
 apply existsb_ext_in'. intros spec Hs. pose proof (Hp spec Hs) as Hm. apply negb_true_iff in Hm.
 unfold event_spec_matches_states. rewrite (R1 _ Hm), (R2 _ Hm). reflexivity. Qed.

Definition aphase (p:Program) (ev:Event) (pre:State) (T:list signal) : option (list signal) :=
 match aiter p (lfp_fuel p) (write_signal pre (changed_signal ev) (new_value ev)) T with
 | None => None
 | Some Td =>
   if events_ok Td p then
     match aupds p (selected_on_transition p pre (phase_driven_state p ev pre)) (phase_driven_state p ev pre) Td Td with
     | None => None
     | Some Tu => match aiter p (lfp_fuel p) (execute_process_order p (phase_driven_state p ev pre)
                    (selected_on_transition p pre (phase_driven_state p ev pre))) Tu with
                  | Some T' => Some (tnorm T') | None => None end
     end
   else None
 end.

(** the driven state alone *)
Theorem adriven_sound p ev ev' pre pre' T Td : changed_signal ev' = changed_signal ev -> new_value ev' = new_value ev ->
 aiter p (lfp_fuel p) (write_signal pre (changed_signal ev) (new_value ev)) T = Some Td -> Agree T pre pre' ->
 Agree Td (phase_driven_state p ev pre) (phase_driven_state p ev' pre').
Proof. intros Ec En H HA. unfold phase_driven_state. rewrite Ec, En.
 exact (alfp_sound p _ _ T Td H (agree_write T pre pre' _ _ _ HA (or_intror eq_refl))). Qed.

(** Main theorem: a phase keeps two states equal outside the computed taint set.  The events may differ in the
    (unused) old value. *)
Theorem aphase_sound p ev ev' pre pre' T T' : changed_signal ev' = changed_signal ev -> new_value ev' = new_value ev ->
 aphase p ev pre T = Some T' -> Agree T pre pre' -> Agree T' (PhaseSemantics p ev pre) (PhaseSemantics p ev' pre').
Proof. intros Ec En H HA. unfold aphase in H.
 destruct (aiter p (lfp_fuel p) (write_signal pre (changed_signal ev) (new_value ev)) T) as [Td|] eqn:E1; [|discriminate].
 destruct (events_ok Td p) eqn:Eok; [|discriminate].
 set (d := phase_driven_state p ev pre) in *. set (d' := phase_driven_state p ev' pre').
 destruct (aupds p (selected_on_transition p pre d) d Td Td) as [Tu|] eqn:E2; [|discriminate].
 assert (Hd : Agree Td d d') by exact (adriven_sound p ev ev' pre pre' T Td Ec En E1 HA).
 assert (HS1 : Sub T Td) by exact (aiter_sub p _ _ T Td E1).
 assert (Hsel : selected_on_transition p pre' d' = selected_on_transition p pre d)
  by exact (selected_eq p Td pre pre' d d' Eok (agree_sub T Td _ _ HS1 HA) Hd).
 unfold PhaseSemantics, phase_execute_order. fold d d'. rewrite Hsel.
 destruct (aiter p (lfp_fuel p) (execute_process_order p d (selected_on_transition p pre d)) Tu) as [T2|] eqn:E3; [|discriminate].
 injection H as <-. apply (agree_sub T2 _ _ _ (sub_tnorm T2)).
 apply (alfp_sound p _ _ Tu T2 E3). unfold execute_process_order.
 apply (la_apply Tu (length d)).
 - exact (aupds_sound p _ d d' Td Td Tu E2 Hd).
 - exact (agree_sub Td Tu _ _ (aupds_sub p _ d Td Td Tu E2) Hd).
 - lia.
Qed.

(** helper for the clients: membership is decided by computation *)
Lemma agree_read T s t x : Agree T s t -> memb x T = false -> read_signal t x = read_signal s x.
Proof. intros [_ R] H. symmetry. exact (R x H). Qed.
Lemma agree_length T s t : Agree T s t -> length t = length s.
Proof. intros [L _]. symmetry. exact L. Qed.
Lemma agree_refl T s : Agree T s s.
Proof. split; [reflexivity|intros; reflexivity]. Qed.

End ExtendedSVNonInterference.
