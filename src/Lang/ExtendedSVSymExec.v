(** Symbolic execution of a blocking process under expression-keyed facts.

    Generic, design independent (template route, 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    A decoder-style process writes dozens of outputs in one blocking sequence
    (defaults, then a case on the opcode, then nested cases/ifs).  Given facts
    [eval_expr s0 e = z] about sub-expressions of the original state [s0], the
    executor [xexec] runs the process with the SAME fuel structure as [exec_stmt]
    and returns an overlay [ov] (root -> width, normalised value) of everything
    written.  It fails (None) on non-blocking assignments, partial-width writes,
    and any guard/scrutinee/right-hand side it cannot decide.  Soundness:
    [xrun_process_sound]: every root in the overlay has that value after
    [run_process].  [xrun_comb_lfp] transfers this to the combinational fixed
    point (pivot theorems of ExtendedSVCombConnection).  Nothing is assumed:
    the facts are hypotheses of the final statement. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement.
Local Open Scope Z_scope.
Module ExtendedSVSymExec.

Definition Ov := list (signal * (nat * Z)).
Fixpoint ov_lookup (ov:Ov) (r:signal) : option (nat*Z) :=
 match ov with
 | [] => None
 | (r',v)::t => if Nat.eqb r r' then Some v else ov_lookup t r
 end.
Definition Facts := list (Expr * Z).

Definition expr_eq_dec : forall a b : Expr, {a=b}+{a<>b}.
Proof.
 decide equality; try apply Z.eq_dec; try apply Nat.eq_dec; try apply Bool.bool_dec; decide equality.
Defined.

Definition FactsHold (s0:State) (F:Facts) : Prop :=
 forall e z, In (e,z) F -> eval_expr s0 e = z.

Fixpoint fact_find (F:Facts) (e:Expr) : option Z :=
 match F with
 | [] => None
 | (e',z)::t => if expr_eq_dec e e' then Some z else fact_find t e
 end.

Lemma fact_find_sound F e z s0 : FactsHold s0 F -> fact_find F e = Some z -> eval_expr s0 e = z.
Proof.
 intros HF. induction F as [|[e' z'] t IH]; cbn [fact_find]; intro H; [discriminate|].
 destruct (expr_eq_dec e e') as [->|N].
 - inversion H; subst. apply HF. now left.
 - apply IH; [intros e2 z2 HI; apply HF; now right|exact H].
Qed.

Definition unwrittenb (ov:Ov) (e:Expr) : bool :=
 forallb (fun wr => match ov_lookup ov (snd wr) with None => true | _ => false end) (expr_inputs e).

Definition Agree (ov:Ov) (s0 s:State) : Prop :=
 (forall r w z, ov_lookup ov r = Some (w,z) -> norm w (read_signal s r) = z) /\
 (forall r, ov_lookup ov r = None -> read_signal s r = read_signal s0 r).

Lemma agree_nil s0 : Agree [] s0 s0.
Proof. split; [intros r w z H; discriminate|intros; reflexivity]. Qed.

Fixpoint xeval (F:Facts) (ov:Ov) (e:Expr) {struct e} : option Z :=
 match (if unwrittenb ov e then fact_find F e else None) with
 | Some z => Some z
 | None =>
  match e with
  | EConst w v => Some (norm w v)
  | EVar w x => match ov_lookup ov x with
     | Some (w',z) => if Nat.eqb w w' then Some z else None
     | None => None end
  | ESel w b l => match xeval F ov b, xeval F ov l with
     | Some vb, Some vl => Some (norm w (Z.shiftr vb vl)) | _,_ => None end
  | EConcat w h l => match xeval F ov h, xeval F ov l with
     | Some vh, Some vl => Some (norm w (Z.lor (Z.shiftl vh (Z.of_nat (expr_width l))) vl)) | _,_ => None end
  | EReplicate w c b => match xeval F ov b with
     | Some v => Some (norm w (replicate_bits c (expr_width b) v)) | None => None end
  | EExtend w sg b => match xeval F ov b with
     | Some v => Some (norm w (if sg then signed_value (expr_width b) v else v)) | None => None end
  | EUnary w op b => match xeval F ov b with
     | Some v => Some (norm w (match op with
                | UNot => Z.lnot v
                | UNegate => - v
                | URedOr => boolz (negb (Z.eqb v 0)) end)) | None => None end
  | EBinary w op l r => match xeval F ov l, xeval F ov r with
     | Some a, Some b => Some (norm w (match op with
           | BAnd => Z.land a b | BOr => Z.lor a b | BXor => Z.lxor a b
           | BAdd => a + b | BSub => a - b | BMul => a * b
           | BEq => boolz (Z.eqb a b) | BNeq => boolz (negb (Z.eqb a b))
           | BLtU => boolz (Z.ltb a b) | BGtU => boolz (Z.gtb a b)
           | BGtS => boolz (Z.gtb (signed_value (expr_width l) a) (signed_value (expr_width r) b))
           | BShiftL => Z.shiftl a b | BShiftR => Z.shiftr a b
           | BShiftRS => Z.shiftr (signed_value (expr_width l) a) b end))
     | _,_ => None end
  | ECond w g y n => match xeval F ov g with
     | Some v => match (if Z.eqb v 0 then xeval F ov n else xeval F ov y) with
        | Some u => Some (norm w u) | None => None end
     | None => None end
  end
 end.

(** A comb process that is one non-blocking assignment behaves like the blocking one. *)
Definition nbfix (st:Stmt) : Stmt :=
 match st with SAssign true e l => SAssign false e l | _ => st end.
Lemma run_process_nbfix p proc s :
 run_process p s proc = run_process p s
  {| process_kind := process_kind proc; process_events := process_events proc;
     process_body := nbfix (process_body proc); process_source_line := process_source_line proc |}.
Proof.
 unfold run_process. cbn [process_body]. destruct (process_body proc) as [|nba rhs lhs|l|g y n|scr arms]; try reflexivity.
 destruct nba; [|reflexivity].
 destruct (statement_fuel p) as [|f]; [reflexivity|].
 cbn [nbfix exec_stmt blocking_state pending_nba apply_nba].
 reflexivity.
Qed.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Lemma xeval_sound : forall e ov s z, Agree ov s0 s -> xeval F ov e = Some z -> eval_expr s e = z.
Proof.
 induction e; intros ov s z [HA1 HA2] H; cbn [xeval] in H;
  destruct (if unwrittenb ov _ then fact_find F _ else None) eqn:Hd.
 all: try (inversion H; subst; clear H;
   destruct (unwrittenb ov _) eqn:Hu; [|discriminate];
   rewrite <- (fact_find_sound _ _ _ s0 HF Hd);
   apply eval_expr_agree; intros w x Hin; unfold unwrittenb in Hu;
   rewrite forallb_forall in Hu; specialize (Hu (w,x) Hin); cbn [snd] in Hu;
   destruct (ov_lookup ov x) eqn:Hl; [discriminate|];
   now rewrite (HA2 x Hl)).
 all: cbn [eval_expr].
 - inversion H; reflexivity.
 - destruct (ov_lookup ov id) as [[w' z']|] eqn:Hl; [|discriminate].
   destruct (Nat.eqb width w') eqn:Hw; [|discriminate].
   apply Nat.eqb_eq in Hw; subst. inversion H; subst. exact (HA1 _ _ _ Hl).
 - destruct (xeval F ov e1) as [a|] eqn:E1; [|discriminate].
   destruct (xeval F ov e2) as [b|] eqn:E2; [|discriminate]. inversion H; subst.
   rewrite (IHe1 _ _ _ (conj HA1 HA2) E1), (IHe2 _ _ _ (conj HA1 HA2) E2). reflexivity.
 - destruct (xeval F ov e1) as [a|] eqn:E1; [|discriminate].
   destruct (xeval F ov e2) as [b|] eqn:E2; [|discriminate]. inversion H; subst.
   rewrite (IHe1 _ _ _ (conj HA1 HA2) E1), (IHe2 _ _ _ (conj HA1 HA2) E2). reflexivity.
 - destruct (xeval F ov e) as [a|] eqn:E1; [|discriminate]. inversion H; subst.
   rewrite (IHe _ _ _ (conj HA1 HA2) E1). reflexivity.
 - destruct (xeval F ov e) as [a|] eqn:E1; [|discriminate]. inversion H; subst.
   rewrite (IHe _ _ _ (conj HA1 HA2) E1). reflexivity.
 - destruct (xeval F ov e) as [a|] eqn:E1; [|discriminate]. inversion H; subst.
   rewrite (IHe _ _ _ (conj HA1 HA2) E1). reflexivity.
 - destruct (xeval F ov e1) as [a|] eqn:E1; [|discriminate].
   destruct (xeval F ov e2) as [b|] eqn:E2; [|discriminate]. inversion H; subst.
   rewrite (IHe1 _ _ _ (conj HA1 HA2) E1), (IHe2 _ _ _ (conj HA1 HA2) E2). reflexivity.
 - destruct (xeval F ov e1) as [a|] eqn:E1; [|discriminate].
   rewrite (IHe1 _ _ _ (conj HA1 HA2) E1).
   destruct (Z.eqb a 0) eqn:Hz.
   + destruct (xeval F ov e3) as [u|] eqn:E3; [|discriminate]. inversion H; subst.
     rewrite (IHe3 _ _ _ (conj HA1 HA2) E3). reflexivity.
   + destruct (xeval F ov e2) as [u|] eqn:E2; [|discriminate]. inversion H; subst.
     rewrite (IHe2 _ _ _ (conj HA1 HA2) E2). reflexivity.
Qed.

Fixpoint xselect (ov:Ov) (v:Z) (arms:list (option Expr * Stmt)) (d:Stmt) : option Stmt :=
 match arms with
 | [] => Some d
 | (None,b)::rest => xselect ov v rest b
 | (Some k,b)::rest => match xeval F ov k with
    | Some kv => if Z.eqb v kv then Some b else xselect ov v rest d
    | None => None end
 end.

Lemma xselect_sound : forall arms ov s v d c, Agree ov s0 s -> xselect ov v arms d = Some c ->
 select_case_stmt s v arms d = c.
Proof.
 induction arms as [|[[k|] b] rest IH]; intros ov s v d c HA H; cbn [xselect] in H.
 - inversion H; reflexivity.
 - destruct (xeval F ov k) as [kv|] eqn:Ek; [|discriminate].
   cbn [select_case_stmt]. rewrite (xeval_sound _ _ _ _ HA Ek).
   destruct (Z.eqb v kv); [now inversion H|exact (IH _ _ _ _ _ HA H)].
 - cbn [select_case_stmt]. exact (IH _ _ _ _ _ HA H).
Qed.

Fixpoint xexec (fuel:nat) (st:Stmt) (ov:Ov) {struct fuel} : option Ov :=
 match fuel with
 | O => Some ov
 | S f =>
  match st with
  | SSkip => Some ov
  | SAssign false rhs (LVar w r) =>
     match xeval F ov rhs with Some z => Some ((r,(w,norm w z))::ov) | None => None end
  | SAssign _ _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some ov' => xexec f st' ov' | None => None end) l (Some ov)
  | SIf g y n => match xeval F ov g with
     | Some z => xexec f (if Z.eqb z 0 then n else y) ov | None => None end
  | SCase scr arms => match xeval F ov scr with
     | Some v => match xselect ov v arms SSkip with
        | Some c => xexec f c ov | None => None end
     | None => None end
  end
 end.

Lemma agree_assign ov s w r v : Agree ov s0 s ->
 Agree ((r,(w,norm w v))::ov) s0 (apply_update s (resolve_update s (LVar w r) v)).
Proof.
 intros [H1 H2]. unfold apply_update,resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 split.
 - intros r' w' z' Hl. cbn [ov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr.
   + apply Nat.eqb_eq in Hr; subst. inversion Hl; subst.
     rewrite read_signal_write_same, norm_full_low_write.
     unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
   + rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
     exact (H1 _ _ _ Hl).
 - intros r' Hl. cbn [ov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
   exact (H2 _ Hl).
Qed.

Lemma fold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => xexec f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem xexec_sound : forall fuel st ov ov' es,
 xexec fuel st ov = Some ov' -> Agree ov s0 (blocking_state es) ->
 Agree ov' s0 (blocking_state (exec_stmt fuel st es)) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st ov ov' es H HA.
 - cbn in H. inversion H; subst. cbn. split; [exact HA|reflexivity].
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [xexec exec_stmt] in *.
   + inversion H; subst. split; [exact HA|reflexivity].
   + destruct nba; [discriminate|]. destruct lhs as [w r|]; [|discriminate].
     destruct (xeval F ov rhs) as [z|] eqn:Ez; [|discriminate]. inversion H; subst.
     rewrite (xeval_sound _ _ _ _ HA Ez). cbn [blocking_state pending_nba].
     split; [apply agree_assign; exact HA|reflexivity].
   + assert (Hgen: forall l ov ov' es,
        fold_left (fun o st' => match o with Some ov' => xexec f st' ov' | None => None end) l (Some ov) = Some ov' ->
        Agree ov s0 (blocking_state es) ->
        Agree ov' s0 (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es).
     { induction l0 as [|a rest IHl]; intros ov0 ov1 es0 H0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; [exact HA0|reflexivity].
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (xexec f a ov0) as [o1|] eqn:Ea; [|rewrite fold_none in H0; discriminate].
         destruct (IH _ _ _ es0 Ea HA0) as [HA1 HP1].
         destruct (IHl _ _ _ H0 HA1) as [HA2 HP2]. split; [exact HA2|congruence]. }
     exact (Hgen l ov ov' es H HA).
   + destruct (xeval F ov g) as [z|] eqn:Ez; [|discriminate].
     rewrite (xeval_sound _ _ _ _ HA Ez). exact (IH _ _ _ _ H HA).
   + destruct (xeval F ov scr) as [v|] eqn:Ev; [|discriminate].
     destruct (xselect ov v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite (xeval_sound _ _ _ _ HA Ev), (xselect_sound _ _ _ _ _ _ HA Ec).
     exact (IH _ _ _ _ H HA).
Qed.

Theorem xrun_process_sound p proc ov :
 xexec (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 forall r w z, ov_lookup ov r = Some (w,z) -> norm w (read_signal (run_process p s0 proc) r) = z.
Proof.
 intros H r w z Hl. rewrite run_process_nbfix. unfold run_process. cbn [process_body].
 destruct (xexec_sound _ _ _ _ {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|} H (agree_nil s0)) as [[HA1 _] HP].
 cbn [pending_nba] in HP. rewrite HP. cbn [apply_nba]. exact (HA1 _ _ _ Hl).
Qed.
End Sound.

(** Writer index.  [roots_unwrittenb] re-traverses every process body on each call, and the kernel
    checker works on unary naturals, so scanning all processes per root is very slow on a 2000-process design.
    The index [T] lists, for each root [r], the comb-order positions of the processes writing it
    (completeness is checked once, [tab_okb]); "unwritten by the prefix/suffix" is then a scan of a short list. *)
Definition wr_lt (T:list (list nat)) (r k:nat) : bool := forallb (fun j => Nat.ltb j k) (nth r T []).
Definition wr_ge (T:list (list nat)) (r k:nat) : bool := forallb (fun j => Nat.leb k j) (nth r T []).

Definition TabC (ps:list Process) (T:list (list nat)) : Prop :=
 forall j p r, nth_error ps j = Some p -> In r (process_writers p) -> In j (nth r T []).

Fixpoint tab_okb_from (j:nat) (ps:list Process) (T:list (list nat)) : bool :=
 match ps with
 | [] => true
 | p::ps' => forallb (fun r => existsb (Nat.eqb j) (nth r T [])) (process_writers p) && tab_okb_from (S j) ps' T
 end.
Definition tab_okb (ps:list Process) (T:list (list nat)) : bool := tab_okb_from 0 ps T.

Lemma tab_okb_from_sound : forall ps j0 T, tab_okb_from j0 ps T = true ->
 forall j p r, nth_error ps j = Some p -> In r (process_writers p) -> In (j0+j)%nat (nth r T []).
Proof.
 induction ps as [|q ps IH]; intros j0 T H j p r HN HI; [destruct j; discriminate|].
 cbn [tab_okb_from] in H. apply andb_true_iff in H as [H1 H2].
 destruct j; cbn in HN.
 - inversion HN; subst. rewrite forallb_forall in H1. specialize (H1 r HI).
   apply existsb_exists in H1 as [y [Hy E]]. apply Nat.eqb_eq in E. subst. rewrite Nat.add_0_r. exact Hy.
 - specialize (IH (S j0) T H2 j p r HN HI). replace (j0 + S j)%nat with (S j0 + j)%nat by lia. exact IH.
Qed.
Lemma tab_okb_sound ps T : tab_okb ps T = true -> TabC ps T.
Proof. intros H j p r HN HI. exact (tab_okb_from_sound ps 0 T H j p r HN HI). Qed.

Lemma in_firstn_idx : forall (ps:list Process) k p, In p (firstn k ps) -> exists i, (i < k)%nat /\ nth_error ps i = Some p.
Proof.
 induction ps as [|q ps IH]; intros k p H; destruct k; cbn in H; try contradiction.
 destruct H as [H|H].
 - subst. exists 0%nat. split; [lia|reflexivity].
 - destruct (IH _ _ H) as [i [A B]]. exists (S i). split; [lia|exact B].
Qed.
Lemma in_skipn_idx : forall (ps:list Process) k p, In p (skipn k ps) -> exists i, nth_error ps (k+i) = Some p.
Proof.
 induction ps as [|q ps IH]; intros k p H; destruct k; cbn in H; try contradiction.
 - destruct H as [H|H].
   + subst. exists 0%nat. reflexivity.
   + destruct (IH 0%nat p H) as [i B]. exists (S i). cbn. exact B.
 - destruct (IH _ _ H) as [i B]. exists i. cbn. exact B.
Qed.

Lemma unw_prefix ps T k r : TabC ps T -> wr_ge T r k = true -> roots_unwrittenb r (firstn k ps) = true.
Proof.
 intros HT H. unfold roots_unwrittenb. apply forallb_forall. intros p Hp.
 destruct (in_firstn_idx _ _ _ Hp) as [i [Hik Hi]].
 apply negb_true_iff. destruct (existsb (Nat.eqb r) (process_writers p)) eqn:E; [|reflexivity].
 apply existsb_exists in E as [y [Hy Ey]]. apply Nat.eqb_eq in Ey. subst y.
 pose proof (HT i p r Hi Hy) as Hin. unfold wr_ge in H. rewrite forallb_forall in H.
 pose proof (H i Hin) as Hle. apply Nat.leb_le in Hle. lia.
Qed.
Lemma unw_suffix ps T k r : TabC ps T -> wr_lt T r k = true -> roots_unwrittenb r (skipn k ps) = true.
Proof.
 intros HT H. unfold roots_unwrittenb. apply forallb_forall. intros p Hp.
 destruct (in_skipn_idx _ _ _ Hp) as [i Hi].
 apply negb_true_iff. destruct (existsb (Nat.eqb r) (process_writers p)) eqn:E; [|reflexivity].
 apply existsb_exists in E as [y [Hy Ey]]. apply Nat.eqb_eq in Ey. subst y.
 pose proof (HT (k+i)%nat p r Hi Hy) as Hin. unfold wr_lt in H. rewrite forallb_forall in H.
 pose proof (H _ Hin) as Hlt. apply Nat.ltb_lt in Hlt. lia.
Qed.

Lemma skipn_nth_cons : forall (ps:list Process) k p, nth_error ps k = Some p -> skipn k ps = p :: skipn (S k) ps.
Proof.
 induction ps as [|q ps IH]; intros k p H; destruct k; cbn in H |- *; try discriminate.
 - inversion H; subst; reflexivity.
 - apply IH, H.
Qed.

Definition facts_inputs_okb (F:Facts) (T:list (list nat)) (k:nat) : bool :=
 forallb (fun ez => forallb (fun wr => wr_ge T (snd wr) k || wr_lt T (snd wr) k)
   (expr_inputs (fst ez))) F.

(** Transfer to the combinational fixed point for the process at comb position [k]. *)
Theorem xrun_comb_lfp p ps T k proc F ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 xexec F (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 forall r w z, ov_lookup ov r = Some (w,z) -> wr_lt T r (S k) = true ->
 norm w (read_signal fixed r) = z.
Proof.
 intros HP HT HN Hok HFH HL Hx r w z Hl Hr.
 pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn k ps) proc (skipn (S k) ps) r seed fixed Horder (unw_suffix ps T (S k) r HT Hr) HL).
 refine (xrun_process_sound F (fold_left (run_process p) (firstn k ps) fixed) _ p proc ov Hx r w z Hl).
 intros e zz HI. unfold FactsHold in HFH.
 rewrite <- (HFH e zz HI). apply eval_expr_agree. intros wd x Hin.
 unfold facts_inputs_okb in Hok. rewrite forallb_forall in Hok.
 specialize (Hok (e,zz) HI). cbn [fst] in Hok. rewrite forallb_forall in Hok.
 specialize (Hok (wd,x) Hin). cbn [snd] in Hok.
 apply orb_true_iff in Hok as [Hok|Hok].
 - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hok))). reflexivity.
 - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
     (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hok) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity.
Qed.

Definition DecOut (s:State) (outs:list ((signal*nat)*Z)) : Prop :=
 forall t, In t outs -> norm (snd (fst t)) (read_signal s (fst (fst t))) = snd t.
End ExtendedSVSymExec.
Print Assumptions ExtendedSVSymExec.xeval_sound.
Print Assumptions ExtendedSVSymExec.xexec_sound.
Print Assumptions ExtendedSVSymExec.xrun_comb_lfp.
