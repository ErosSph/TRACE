(** Data-flow equations of combinational processes under constant control facts (template route, 2026-11-03).

    Generic, design independent.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

    [ExtendedSVSymExec] derives CONSTANT facts.  Operand multiplexers, copies and adders carry unknown data, so
    nothing constant comes out.  Here a blocking process is executed along the path that the (constant) facts
    select: every guard and case scrutinee must be decided by the facts (reading nothing the process wrote
    before), and each assignment [r = rhs] is recorded as the equation
        [norm w (r) = norm w (eval rhs')]     where rhs' = [simp F rhs]
    ([simp] resolves the ECond guards that the facts decide).  The right-hand side must read nothing that the
    process wrote earlier, so it is evaluated in the state in which the process starts.  Later writes of the same
    root replace the equation.  [eqchain] transfers the equations to the combinational fixed point exactly like
    [ExtendedSVFactChain.chain] (same pivot conditions, same writer table).  [resolve] follows copy equations
    [r = EVar x] so a generator can state "this wire is a copy of that wire" and have Coq check it by computation.
    Nothing is assumed: the facts are hypotheses of the final statement. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement
 ExtendedSVSymExec ExtendedSVFactChain ExtendedSVWordInvariant.
Local Open Scope Z_scope.
Module ExtendedSVSymAlias.

Definition Eqn := (nat * signal * Expr)%type.
Definition EqHold (s:State) (E:list Eqn) : Prop :=
 forall w r e, In (w,r,e) E -> norm w (read_signal s r) = norm w (eval_expr s e).

(** ---- specialisation of conditionals decided by constant facts ---- *)
Fixpoint simp (F:Facts) (e:Expr) : Expr :=
 match e with
 | EConst _ _ | EVar _ _ => e
 | ESel w b l => ESel w (simp F b) (simp F l)
 | EConcat w h l => EConcat w (simp F h) (simp F l)
 | EReplicate w c b => EReplicate w c (simp F b)
 | EExtend w sg b => EExtend w sg (simp F b)
 | EUnary w op b => EUnary w op (simp F b)
 | EBinary w op l r => EBinary w op (simp F l) (simp F r)
 | ECond w g y n =>
    match xeval F [] g with
    | Some z => let e' := simp F (if Z.eqb z 0 then n else y) in
        if Nat.eqb (expr_width e') w then e' else EExtend w false e'
    | None => ECond w (simp F g) (simp F y) (simp F n)
    end
 end.

Lemma simp_width F : forall e, expr_width (simp F e) = expr_width e.
Proof.
 induction e; cbn [simp expr_width]; try reflexivity.
 destruct (xeval F [] e1) as [z|]; [|reflexivity].
 destruct (Nat.eqb (expr_width (simp F (if Z.eqb z 0 then e3 else e2))) width) eqn:E.
 - apply Nat.eqb_eq in E. exact E.
 - reflexivity.
Qed.

Lemma value_norm s e : norm (expr_width e) (eval_expr s e) = eval_expr s e.
Proof. destruct e; cbn [expr_width eval_expr]; apply norm_idempotent. Qed.

Lemma simp_sound F s0 (HF:FactsHold s0 F) : forall e, eval_expr s0 (simp F e) = eval_expr s0 e.
Proof.
 induction e; cbn [simp]; try reflexivity.
 - cbn [eval_expr]. now rewrite IHe1, IHe2, ?simp_width.
 - cbn [eval_expr]. rewrite IHe1, IHe2. now rewrite ?simp_width.
 - cbn [eval_expr]. now rewrite IHe, ?simp_width.
 - cbn [eval_expr]. now rewrite IHe, ?simp_width.
 - cbn [eval_expr]. now rewrite IHe.
 - cbn [eval_expr]. now rewrite IHe1, IHe2, ?simp_width.
 - destruct (xeval F [] e1) as [z|] eqn:Ex.
   + pose proof (xeval_sound F s0 HF e1 [] s0 z (agree_nil s0) Ex) as Hz.
     cbn [eval_expr]. rewrite Hz.
     set (c := if Z.eqb z 0 then e3 else e2).
     assert (Hc : eval_expr s0 (simp F c) = eval_expr s0 c) by (subst c; destruct (Z.eqb z 0); [apply IHe3|apply IHe2]).
     assert (Hx : (if Z.eqb z 0 then eval_expr s0 e3 else eval_expr s0 e2) = eval_expr s0 c) by (subst c; destruct (Z.eqb z 0); reflexivity).
     rewrite Hx.
     destruct (Nat.eqb (expr_width (simp F c)) width) eqn:Ew.
     * apply Nat.eqb_eq in Ew. rewrite simp_width in Ew.
       rewrite Hc. rewrite <- Ew. symmetry. apply value_norm.
     * cbn [eval_expr]. rewrite Hc. reflexivity.
   + cbn [eval_expr]. now rewrite IHe1, IHe2, IHe3.
Qed.

Lemma simp_inputs F : forall e x, In x (expr_inputs (simp F e)) -> In x (expr_inputs e).
Proof.
 induction e; cbn [simp expr_inputs]; intros x H; try exact H;
  try (apply in_app_or in H as [H|H]; apply in_or_app; [left; auto|right; auto]);
  try auto.
 destruct (xeval F [] e1) as [z|].
 - set (c := if Z.eqb z 0 then e3 else e2) in *.
   assert (Hc : In x (expr_inputs (simp F c)) -> In x (expr_inputs c)) by (subst c; destruct (Z.eqb z 0); auto).
   destruct (Nat.eqb (expr_width (simp F c)) width).
   + apply Hc in H. subst c. destruct (Z.eqb z 0); apply in_or_app; right; apply in_or_app; [right|left]; exact H.
   + cbn [expr_inputs] in H. apply Hc in H. subst c. destruct (Z.eqb z 0); apply in_or_app; right; apply in_or_app; [right|left]; exact H.
 - apply in_app_or in H as [H|H]; [apply in_or_app; left; auto|].
   apply in_app_or in H as [H|H]; apply in_or_app; right; apply in_or_app; [left|right]; auto.
Qed.

(** ---- path execution ---- *)
Definition ceval (F:Facts) (ov:Ov) (e:Expr) : option Z :=
 if unwrittenb ov e then xeval F [] e else None.

Fixpoint cselect (F:Facts) (ov:Ov) (v:Z) (arms:list (option Expr * Stmt)) (d:Stmt) : option Stmt :=
 match arms with
 | [] => Some d
 | (None,b)::rest => cselect F ov v rest b
 | (Some k,b)::rest => match ceval F ov k with
    | Some kv => if Z.eqb v kv then Some b else cselect F ov v rest d
    | None => None end
 end.

Definition drop_root (r:signal) (acc:list Eqn) : list Eqn :=
 filter (fun q => negb (Nat.eqb (snd (fst q)) r)) acc.

Fixpoint pex (F:Facts) (fuel:nat) (st:Stmt) (ov:Ov) (acc:list Eqn) {struct fuel} : option (Ov * list Eqn) :=
 match fuel with
 | O => Some (ov,acc)
 | S f =>
  match st with
  | SSkip => Some (ov,acc)
  | SAssign false rhs (LVar w r) =>
     if unwrittenb ov rhs then Some ((r,(0%nat,0))::ov, (w,r,simp F rhs)::drop_root r acc) else None
  | SAssign _ _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some (ov',acc') => pex F f st' ov' acc' | None => None end) l (Some (ov,acc))
  | SIf g y n => match ceval F ov g with
     | Some z => pex F f (if Z.eqb z 0 then n else y) ov acc | None => None end
  | SCase scr arms => match ceval F ov scr with
     | Some v => match cselect F ov v arms SSkip with
        | Some c => pex F f c ov acc | None => None end
     | None => None end
  end
 end.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Definition AgreeE (ov:Ov) (acc:list Eqn) (s:State) : Prop :=
 (forall r, ov_lookup ov r = None -> read_signal s r = read_signal s0 r) /\
 (forall w r e, In (w,r,e) acc -> norm w (read_signal s r) = norm w (eval_expr s0 e)).

Lemma unwritten_agree ov e s : (forall r, ov_lookup ov r = None -> read_signal s r = read_signal s0 r) ->
 unwrittenb ov e = true -> eval_expr s e = eval_expr s0 e.
Proof.
 intros H Hu. apply eval_expr_agree. intros w x Hin. unfold unwrittenb in Hu. rewrite forallb_forall in Hu.
 specialize (Hu (w,x) Hin). cbn [snd] in Hu. destruct (ov_lookup ov x) eqn:Hl; [discriminate|].
 now rewrite (H x Hl).
Qed.

Lemma ceval_sound ov acc s e z : AgreeE ov acc s -> ceval F ov e = Some z -> eval_expr s e = z.
Proof.
 intros [H1 _] H. unfold ceval in H. destruct (unwrittenb ov e) eqn:Hu; [|discriminate].
 rewrite (unwritten_agree ov e s H1 Hu).
 exact (xeval_sound F s0 HF e [] s0 z (agree_nil s0) H).
Qed.

Lemma cselect_sound : forall arms ov acc s v d c, AgreeE ov acc s -> cselect F ov v arms d = Some c ->
 select_case_stmt s v arms d = c.
Proof.
 induction arms as [|[[k|] b] rest IH]; intros ov acc s v d c HA H; cbn [cselect] in H.
 - inversion H; reflexivity.
 - destruct (ceval F ov k) as [kv|] eqn:Ek; [|discriminate].
   cbn [select_case_stmt]. rewrite (ceval_sound _ _ _ _ _ HA Ek).
   destruct (Z.eqb v kv); [now inversion H|exact (IH _ _ _ _ _ _ HA H)].
 - cbn [select_case_stmt]. exact (IH _ _ _ _ _ _ HA H).
Qed.

Lemma agreeE_assign ov acc s w r rhs :
 unwrittenb ov rhs = true -> AgreeE ov acc s ->
 AgreeE ((r,(0%nat,0))::ov) ((w,r,simp F rhs)::drop_root r acc)
  (apply_update s (resolve_update s (LVar w r) (eval_expr s rhs))).
Proof.
 intros Hu [H1 H2]. unfold apply_update,resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 split.
 - intros r' Hl. cbn [ov_lookup] in Hl. destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   apply Nat.eqb_neq in Hr. rewrite read_signal_write_other by congruence. exact (H1 _ Hl).
 - intros w' r' e' Hin. destruct Hin as [Hin|Hin].
   + inversion Hin; subst. rewrite read_signal_write_same, norm_full_low_write.
     rewrite (unwritten_agree ov rhs s H1 Hu).
     rewrite (simp_sound F s0 HF rhs). unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
   + unfold drop_root in Hin. apply filter_In in Hin as [Hin Hneq]. cbn [snd fst] in Hneq.
     apply negb_true_iff in Hneq. apply Nat.eqb_neq in Hneq.
     rewrite read_signal_write_other by congruence. exact (H2 _ _ _ Hin).
Qed.

Lemma pex_fold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some (ov',acc') => pex F f st' ov' acc' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem pex_sound : forall fuel st ov acc ov' acc' es,
 pex F fuel st ov acc = Some (ov',acc') -> AgreeE ov acc (blocking_state es) ->
 AgreeE ov' acc' (blocking_state (exec_stmt fuel st es)) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st ov acc ov' acc' es H HA.
 - cbn in H. inversion H; subst. cbn. split; [exact HA|reflexivity].
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [pex exec_stmt] in *.
   + inversion H; subst. split; [exact HA|reflexivity].
   + destruct nba; [discriminate|]. destruct lhs as [w r|]; [|discriminate].
     destruct (unwrittenb ov rhs) eqn:Hu; [|discriminate]. inversion H; subst.
     cbn [blocking_state pending_nba]. split; [apply agreeE_assign; assumption|reflexivity].
   + assert (Hgen: forall l ov acc ov' acc' es,
        fold_left (fun o st' => match o with Some (ov',acc') => pex F f st' ov' acc' | None => None end) l (Some (ov,acc)) = Some (ov',acc') ->
        AgreeE ov acc (blocking_state es) ->
        AgreeE ov' acc' (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es).
     { induction l0 as [|a rest IHl]; intros ov0 acc0 ov1 acc1 es0 H0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; [exact HA0|reflexivity].
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (pex F f a ov0 acc0) as [[o1 a1]|] eqn:Ea; [|rewrite pex_fold_none in H0; discriminate].
         destruct (IH _ _ _ _ _ es0 Ea HA0) as [HA1 HP1].
         destruct (IHl _ _ _ _ _ H0 HA1) as [HA2 HP2]. split; [exact HA2|congruence]. }
     exact (Hgen l ov acc ov' acc' es H HA).
   + destruct (ceval F ov g) as [z|] eqn:Ez; [|discriminate].
     rewrite (ceval_sound _ _ _ _ _ HA Ez). exact (IH _ _ _ _ _ _ H HA).
   + destruct (ceval F ov scr) as [v|] eqn:Ev; [|discriminate].
     destruct (cselect F ov v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite (ceval_sound _ _ _ _ _ HA Ev), (cselect_sound _ _ _ _ _ _ _ HA Ec).
     exact (IH _ _ _ _ _ _ H HA).
Qed.

Theorem prun_sound p proc ov acc :
 pex F (statement_fuel p) (nbfix (process_body proc)) [] [] = Some (ov,acc) ->
 forall w r e, In (w,r,e) acc -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 intros H w r e Hin. rewrite run_process_nbfix. unfold run_process. cbn [process_body].
 assert (HA : AgreeE [] [] (blocking_state {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|})).
 { split; [intros; reflexivity|intros w0 r0 e0 H0; contradiction]. }
 destruct (pex_sound _ _ _ _ _ _ _ H HA) as [[_ HA2] HP].
 cbn [pending_nba] in HP. rewrite HP. cbn [apply_nba]. exact (HA2 _ _ _ Hin).
Qed.
End Sound.

(** ---- transfer to the combinational fixed point ---- *)
Definition eq_okb (T:list (list nat)) (k:nat) (q:Eqn) : bool :=
 wr_lt T (snd (fst q)) (S k) &&
 forallb (fun wr => wr_ge T (snd wr) k || wr_lt T (snd wr) k) (expr_inputs (snd q)).

Theorem prun_comb_lfp p ps T k proc F ov acc seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 pex F (statement_fuel p) (nbfix (process_body proc)) [] [] = Some (ov,acc) ->
 forall w r e, In (w,r,e) (filter (eq_okb T k) acc) -> norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN Hok HFH HL Hx w r e Hin.
 apply filter_In in Hin as [Hin Hq]. unfold eq_okb in Hq. cbn [snd fst] in Hq.
 apply andb_true_iff in Hq as [Hr Hq].
 pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn k ps) proc (skipn (S k) ps) r seed fixed Horder (unw_suffix ps T (S k) r HT Hr) HL).
 assert (HF0 : FactsHold (fold_left (run_process p) (firstn k ps) fixed) F).
 { intros e0 zz HI. unfold FactsHold in HFH.
   rewrite <- (HFH e0 zz HI). apply eval_expr_agree. intros wd x Hin'.
   unfold facts_inputs_okb in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (e0,zz) HI). cbn [fst] in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (wd,x) Hin'). cbn [snd] in Hok.
   apply orb_true_iff in Hok as [Hok|Hok].
   - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hok))). reflexivity.
   - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
       (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hok) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity. }
 rewrite (prun_sound F _ HF0 p proc ov acc Hx w r e Hin).
 f_equal. apply eval_expr_agree. intros wd x Hin'.
 rewrite forallb_forall in Hq. specialize (Hq (wd,x) Hin'). cbn [snd] in Hq.
 apply orb_true_iff in Hq as [Hq|Hq].
 - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hq))). reflexivity.
 - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
     (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hq) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity.
Qed.

(** ---- chain over comb positions ---- *)
Definition step_eqs (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (st:nat*list nat) : option (list Eqn) :=
 let k := fst st in
 match nth_error ps k with
 | None => None
 | Some proc =>
   match pex (filter (tail_okb T k) (pick F (snd st))) fuel (nbfix (process_body proc)) [] [] with
   | None => None
   | Some (_,acc) => Some (filter (eq_okb T k) acc)
   end
 end.

Fixpoint eqchain (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list (nat*list nat)) : option (list Eqn) :=
 match ks with
 | [] => Some []
 | k::rest => match step_eqs ps T fuel F k with
    | Some E => match eqchain ps T fuel F rest with Some E' => Some (E ++ E') | None => None end
    | None => None end
 end.

Theorem eqchain_sound p ps T fuel (ks:list (nat*list nat)) : forall F E seed fixed,
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> eqchain ps T fuel F ks = Some E -> EqHold fixed E.
Proof.
 induction ks as [|k rest IH]; intros F E seed fixed HP HT Hf HFH HL H; cbn [eqchain] in H.
 - inversion H; subst. intros w r e Hin. contradiction.
 - destruct (step_eqs ps T fuel F k) as [E1|] eqn:Hs; [|discriminate].
   destruct (eqchain ps T fuel F rest) as [E2|] eqn:Hc; [|discriminate]. inversion H; subst E; clear H.
   intros w r e Hin. apply in_app_or in Hin as [Hin|Hin].
   + unfold step_eqs in Hs. subst fuel.
     destruct (nth_error ps (fst k)) as [proc|] eqn:HN; [|discriminate].
     destruct (pex (filter (tail_okb T (fst k)) (pick F (snd k))) (statement_fuel p) (nbfix (process_body proc)) [] []) as [[ov acc]|] eqn:Hx; [|discriminate].
     inversion Hs; subst E1; clear Hs.
     set (F0 := filter (tail_okb T (fst k)) (pick F (snd k))) in *.
     assert (H0: FactsHold fixed F0).
     { intros e0 z HI. apply filter_In in HI as [HI _]. apply HFH, (pick_in _ _ _ HI). }
     assert (Hok: facts_inputs_okb F0 T (fst k) = true).
     { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT']. exact HT'. }
     exact (prun_comb_lfp p ps T (fst k) proc F0 ov acc seed fixed HP HT HN Hok H0 HL Hx w r e Hin).
   + exact (IH F E2 seed fixed HP HT Hf HFH HL Hc w r e Hin).
Qed.

(** ---- copy chains ---- *)
Fixpoint eq_find (E:list Eqn) (w:nat) (r:signal) : option Expr :=
 match E with
 | [] => None
 | (w',r',e)::t => if Nat.eqb w w' && Nat.eqb r r' then Some e else eq_find t w r
 end.

Lemma eq_find_sound E w r e s : EqHold s E -> eq_find E w r = Some e -> norm w (read_signal s r) = norm w (eval_expr s e).
Proof.
 induction E as [|[[w' r'] e'] t IH]; cbn [eq_find]; intros HE H; [discriminate|].
 destruct (Nat.eqb w w' && Nat.eqb r r') eqn:Hc.
 - apply andb_true_iff in Hc as [A B]. apply Nat.eqb_eq in A. apply Nat.eqb_eq in B. subst. inversion H; subst.
   apply HE. now left.
 - apply IH; [intros w1 r1 e1 Hi; apply HE; now right|exact H].
Qed.

(** [resolve E fuel w r]: follow the copy equations [r = EVar w x] (same width). *)
Fixpoint resolve (E:list Eqn) (fuel:nat) (w:nat) (r:signal) : signal :=
 match fuel with
 | O => r
 | S f => match eq_find E w r with
    | Some (EVar w' x) => if Nat.eqb w w' then resolve E f w x else r
    | _ => r
    end
 end.

Lemma resolve_sound E s : EqHold s E -> forall fuel w r, norm w (read_signal s r) = norm w (read_signal s (resolve E fuel w r)).
Proof.
 intros HE. induction fuel as [|f IH]; intros w r; cbn [resolve]; [reflexivity|].
 destruct (eq_find E w r) as [e|] eqn:Hf; [|reflexivity].
 destruct e; try reflexivity.
 destruct (Nat.eqb w width) eqn:Hw; [|reflexivity]. apply Nat.eqb_eq in Hw. subst.
 rewrite (eq_find_sound E _ _ _ s HE Hf). cbn [eval_expr]. rewrite norm_idempotent. apply IH.
Qed.

(** Statement forms the generators produce. *)
Definition copies_okb (E:list Eqn) (fuel:nat) (l:list (nat*signal*signal)) : bool :=
 forallb (fun t => Nat.eqb (resolve E fuel (fst (fst t)) (snd (fst t))) (snd t)) l.

Definition CopyHold (s:State) (l:list (nat*signal*signal)) : Prop :=
 forall w r x, In (w,r,x) l -> norm w (read_signal s r) = norm w (read_signal s x).

Definition eqs_okb (E:list Eqn) (l:list Eqn) : bool :=
 forallb (fun q => match eq_find E (fst (fst q)) (snd (fst q)) with
   | Some e => if expr_eq_dec e (snd q) then true else false | None => false end) l.

Theorem eqchain_out p ps T ks F0 copies eqs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T ->
 FactsHold fixed F0 -> CombLFP p seed fixed ->
 (match eqchain ps T (statement_fuel p) F0 ks with
  | Some E => copies_okb E 8 copies && eqs_okb E eqs | None => false end) = true ->
 CopyHold fixed copies /\ EqHold fixed eqs.
Proof.
 intros HP HT HFH HL H.
 destruct (eqchain ps T (statement_fuel p) F0 ks) as [E|] eqn:Hc; [|discriminate].
 apply andb_true_iff in H as [Hcp Hq].
 pose proof (eqchain_sound p ps T (statement_fuel p) ks F0 E seed fixed HP HT eq_refl HFH HL Hc) as HE.
 split.
 - intros w r x Hin. unfold copies_okb in Hcp. rewrite forallb_forall in Hcp.
   specialize (Hcp _ Hin). cbn [fst snd] in Hcp. apply Nat.eqb_eq in Hcp.
   rewrite (resolve_sound E fixed HE 8 w r), Hcp. reflexivity.
 - intros w r e Hin. unfold eqs_okb in Hq. rewrite forallb_forall in Hq.
   specialize (Hq _ Hin). cbn [fst snd] in Hq.
   destruct (eq_find E w r) as [e'|] eqn:Hf; [|discriminate].
   destruct (expr_eq_dec e' e) as [->|]; [|discriminate].
   exact (eq_find_sound E w r e fixed HE Hf).
Qed.
End ExtendedSVSymAlias.
Print Assumptions ExtendedSVSymAlias.eqchain_out.
Print Assumptions ExtendedSVSymAlias.eqchain_sound.
