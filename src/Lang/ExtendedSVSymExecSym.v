(** Symbolic execution of comb processes WITHOUT constant results (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [sxexec] runs a blocking comb process under expression-keyed constant facts (guards, case scrutinees and keys are decided by
    [xeval]; they may not read roots assigned earlier in the process) and returns an overlay root -> (width, EXPRESSION over the
    entry state): right-hand sides are substituted ([ssub]); a partial write [r[off +: w] = e] becomes the bit expression [patch].
    [sxrun_comb_lfp]: at a comb fixed point the root has the value of that expression (pivot theorems, same hypotheses as
    ExtendedSVSymExec.xrun_comb_lfp, plus [inputs_okb] on the expression).  [lane_wr]: lane read of a 32-bit lane write.
    Nothing is assumed. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement Lang.ExtendedSVSymExec Lang.ExtendedSVWordInvariant Lang.ExtendedSVFactChain.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement ExtendedSVSymExec ExtendedSVWordInvariant ExtendedSVFactChain.
Local Open Scope Z_scope.
Module ExtendedSVSymExecSym.

Definition SOv := list (signal * (nat * Expr)).
Fixpoint sov_lookup (ov:SOv) (r:signal) : option (nat*Expr) :=
 match ov with
 | [] => None
 | (r',v)::t => if Nat.eqb r r' then Some v else sov_lookup t r
 end.

Definition Agree_s (ov:SOv) (s0 s:State) : Prop :=
 (forall r w e, sov_lookup ov r = Some (w,e) -> norm w (read_signal s r) = norm w (eval_expr s0 e)) /\
 (forall r, sov_lookup ov r = None -> read_signal s r = read_signal s0 r).

Lemma agree_s_nil s0 : Agree_s [] s0 s0.
Proof. split; [intros r w e H; discriminate|intros; reflexivity]. Qed.

Lemma norm_mod w v : norm w v = v mod 2 ^ Z.of_nat w.
Proof.
 unfold norm, mask. assert (E : 2 ^ Z.of_nat w - 1 = Z.ones (Z.of_nat w)) by (rewrite Z.ones_equiv; lia).
 rewrite E. apply Z.land_ones. lia.
Qed.

Lemma norm_low w w' v : (w <= w')%nat -> norm w (norm w' v) = norm w v.
Proof.
 intro H. rewrite !norm_mod.
 rewrite (Znumtheory.Zmod_div_mod (2 ^ Z.of_nat w) (2 ^ Z.of_nat w') v); try (apply Z.pow_pos_nonneg; lia).
 - reflexivity.
 - exists (2 ^ (Z.of_nat w' - Z.of_nat w)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma norm_mask w v : norm w (Z.land v (mask w)) = norm w v.
Proof. unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.

Fixpoint ssub (ov:SOv) (e:Expr) : option Expr :=
 match e with
 | EConst _ _ => Some e
 | EVar w x => match sov_lookup ov x with
     | None => Some e
     | Some (w',e') => if Nat.leb w w' then Some (EBinary w BAnd e' (EConst w (mask w))) else None end
 | ESel w a b => match ssub ov a, ssub ov b with Some a', Some b' => Some (ESel w a' b') | _,_ => None end
 | EConcat w a b => match ssub ov a, ssub ov b with Some a', Some b' => Some (EConcat w a' b') | _,_ => None end
 | EReplicate w c a => match ssub ov a with Some a' => Some (EReplicate w c a') | _ => None end
 | EExtend w sg a => match ssub ov a with Some a' => Some (EExtend w sg a') | _ => None end
 | EUnary w op a => match ssub ov a with Some a' => Some (EUnary w op a') | _ => None end
 | EBinary w op a b => match ssub ov a, ssub ov b with Some a', Some b' => Some (EBinary w op a' b') | _,_ => None end
 | ECond w g a b => match ssub ov g, ssub ov a, ssub ov b with Some g', Some a', Some b' => Some (ECond w g' a' b') | _,_,_ => None end
 end.

Lemma ssub_sound ov s0 s : Agree_s ov s0 s -> forall e e', ssub ov e = Some e' ->
 eval_expr s e = eval_expr s0 e' /\ expr_width e' = expr_width e.
Proof.
 intros [HA1 HA2]. induction e; intros e' H; cbn [ssub] in H.
 - inversion H; subst. split; reflexivity.
 - destruct (sov_lookup ov id) as [[w' e0]|] eqn:Hl.
   + destruct (Nat.leb width w') eqn:Hle; [|discriminate]. inversion H; subst. apply Nat.leb_le in Hle.
     split; [|reflexivity]. cbn [eval_expr]. 
     rewrite <- (norm_low width w' (read_signal s id)) by exact Hle.
     rewrite (HA1 _ _ _ Hl). rewrite norm_low by exact Hle.
     assert (Hm : norm width (mask width) = mask width) by (unfold norm; rewrite Z.land_diag; reflexivity).
     rewrite Hm. rewrite norm_mask. reflexivity.
   + inversion H; subst. split; [|reflexivity]. cbn [eval_expr]. rewrite (HA2 _ Hl). reflexivity.
 - destruct (ssub ov e1) as [a'|] eqn:E1; [|discriminate]. destruct (ssub ov e2) as [b'|] eqn:E2; [|discriminate]. inversion H; subst.
   destruct (IHe1 _ eq_refl) as [A1 _], (IHe2 _ eq_refl) as [A2 _]. split; [cbn [eval_expr]; rewrite A1, A2; reflexivity|reflexivity].
 - destruct (ssub ov e1) as [a'|] eqn:E1; [|discriminate]. destruct (ssub ov e2) as [b'|] eqn:E2; [|discriminate]. inversion H; subst.
   destruct (IHe1 _ eq_refl) as [A1 _], (IHe2 _ eq_refl) as [A2 B2]. split; [cbn [eval_expr]; rewrite A1, A2, B2; reflexivity|reflexivity].
 - destruct (ssub ov e) as [a'|] eqn:E1; [|discriminate]. inversion H; subst.
   destruct (IHe _ eq_refl) as [A1 B1]. split; [cbn [eval_expr]; rewrite A1, B1; reflexivity|reflexivity].
 - destruct (ssub ov e) as [a'|] eqn:E1; [|discriminate]. inversion H; subst.
   destruct (IHe _ eq_refl) as [A1 B1]. split; [cbn [eval_expr]; rewrite A1, B1; reflexivity|reflexivity].
 - destruct (ssub ov e) as [a'|] eqn:E1; [|discriminate]. inversion H; subst.
   destruct (IHe _ eq_refl) as [A1 B1]. split; [cbn [eval_expr]; rewrite A1; reflexivity|reflexivity].
 - destruct (ssub ov e1) as [a'|] eqn:E1; [|discriminate]. destruct (ssub ov e2) as [b'|] eqn:E2; [|discriminate]. inversion H; subst.
   destruct (IHe1 _ eq_refl) as [A1 B1], (IHe2 _ eq_refl) as [A2 B2]. split; [cbn [eval_expr]; rewrite A1, A2, B1, B2; reflexivity|reflexivity].
 - destruct (ssub ov e1) as [g'|] eqn:E1; [|discriminate]. destruct (ssub ov e2) as [a'|] eqn:E2; [|discriminate].
   destruct (ssub ov e3) as [b'|] eqn:E3; [|discriminate]. inversion H; subst.
   destruct (IHe1 _ eq_refl) as [A1 _], (IHe2 _ eq_refl) as [A2 _], (IHe3 _ eq_refl) as [A3 _].
   split; [cbn [eval_expr]; rewrite A1, A2, A3; reflexivity|reflexivity].
Qed.

Lemma tb_ones n j : 0 <= n -> Z.testbit (Z.ones n) j = (0 <=? j) && (j <? n).
Proof.
 intro Hn. destruct (Z.ltb_spec j 0) as [Hj|Hj].
 - rewrite Z.testbit_neg_r by exact Hj. destruct (Z.leb_spec 0 j); [lia|reflexivity].
 - destruct (Z.leb_spec 0 j); [|lia]. destruct (Z.ltb_spec j n) as [H1|H1]; cbn.
   + apply Z.ones_spec_low; lia.
   + apply Z.ones_spec_high; lia.
Qed.

Lemma tb_mask w j : Z.testbit (2 ^ Z.of_nat w - 1) j = (0 <=? j) && (j <? Z.of_nat w).
Proof.
 assert (E : 2 ^ Z.of_nat w - 1 = Z.ones (Z.of_nat w)) by (rewrite Z.ones_equiv; lia). rewrite E.
 apply tb_ones. lia.
Qed.

Lemma tb_norm w x j : Z.testbit (norm w x) j = (0 <=? j) && (j <? Z.of_nat w) && Z.testbit x j.
Proof.
 unfold norm, mask. rewrite Z.land_spec, tb_mask.
 destruct (0 <=? j), (j <? Z.of_nat w), (Z.testbit x j); reflexivity.
Qed.

Lemma tb_shl x o j : 0 <= j -> Z.testbit (Z.shiftl x o) j = Z.testbit x (j - o).
Proof. intro H. apply Z.shiftl_spec. exact H. Qed.

Lemma tb_shl' x o j : 0 <= o -> Z.testbit (Z.shiftl x o) j = Z.testbit x (j - o).
Proof.
 intro H. destruct (Z.ltb_spec j 0) as [Hj|Hj].
 - rewrite Z.testbit_neg_r by exact Hj. rewrite Z.testbit_neg_r by lia. reflexivity.
 - apply Z.shiftl_spec. exact Hj.
Qed.

Lemma patch_arith W w R eo O V : (w <= W)%nat -> 0 <= O -> norm W R = norm W eo ->
 norm W (write_slice R (0 + O) (Z.of_nat w) (norm w V)) =
 norm W (Z.lor (norm W (Z.land eo (norm W (Z.lnot (norm W (Z.shiftl (norm W (2 ^ Z.of_nat w - 1)) O))))))
               (norm W (Z.shiftl (norm W (Z.land V (norm W (2 ^ Z.of_nat w - 1)))) O))).
Proof.
 intros Hw HO HR. apply Z.bits_inj'. intros n Hn.
 pose proof (f_equal (fun z => Z.testbit z n) HR) as HRn. cbn beta in HRn.
 unfold write_slice.
 repeat (first [ rewrite tb_norm in * | rewrite Z.lor_spec in * | rewrite Z.land_spec in * | rewrite Z.lnot_spec in * by lia
                | rewrite tb_shl' in * by lia | rewrite tb_mask in * ]).
 replace (n - (0 + O)) with (n - O) by lia.
 destruct (Z.leb_spec 0 n); [|lia].
 destruct (Z.ltb_spec n (Z.of_nat W)); cbn in HRn |- *; try reflexivity.
 assert (Hl : (n - O <? Z.of_nat W) = true) by (apply Z.ltb_lt; lia); rewrite Hl.
 destruct (Z.leb_spec 0 (n - O)); destruct (Z.ltb_spec (n - O) (Z.of_nat w)); cbn;
  destruct (Z.testbit R n); destruct (Z.testbit eo n); destruct (Z.testbit V (n - O)); cbn in *; try discriminate; try reflexivity.
Qed.


Lemma norm_nonneg w x : 0 <= norm w x.
Proof. unfold norm, mask. apply Z.land_nonneg. right. assert (0 < 2 ^ Z.of_nat w) by (apply Z.pow_pos_nonneg; lia). lia. Qed.
Lemma eval_nonneg s e : 0 <= eval_expr s e.
Proof. destruct e; cbn [eval_expr]; apply norm_nonneg. Qed.

Definition patch (W w : nat) (eo o e : Expr) : Expr :=
 EBinary W BOr (EBinary W BAnd eo (EUnary W UNot (EBinary W BShiftL (EConst W (2 ^ Z.of_nat w - 1)) o)))
   (EBinary W BShiftL (EBinary W BAnd e (EConst W (2 ^ Z.of_nat w - 1))) o).

(** xeval with short-circuit: [a & b] is 0 when either side is 0, and the selected arm of a decided conditional. *)
Fixpoint xeval2 (F:Facts) (e:Expr) : option Z :=
 match e with
 | EBinary w BAnd l r =>
     match xeval F [] e with
     | Some z => Some z
     | None => match xeval2 F l with Some 0 => Some 0 | _ => match xeval2 F r with Some 0 => Some 0 | _ => None end end
     end
 | ECond w g y n =>
     match xeval F [] e with
     | Some z => Some z
     | None => match xeval2 F g with
        | Some v => match (if Z.eqb v 0 then xeval2 F n else xeval2 F y) with Some u => Some (norm w u) | None => None end
        | None => match xeval2 F y, xeval2 F n with
           | Some u1, Some u2 => if Z.eqb u1 u2 then Some (norm w u1) else None
           | _, _ => None end end
     end
 | _ => xeval F [] e
 end.

Lemma xeval2_sound F s0 (HF : FactsHold s0 F) : forall e z, xeval2 F e = Some z -> eval_expr s0 e = z.
Proof.
 induction e as [w0 v0|w0 x0|w0 a IHa b IHb|w0 a IHa b IHb|w0 c a IHa|w0 sg a IHa|w0 op0 a IHa|w0 op0 a IHa b IHb|w0 g IHg a IHa b IHb];
  intros z H; cbn [xeval2] in H;
  try (exact (xeval_sound F s0 HF _ [] s0 z (agree_nil s0) H)).
 - destruct op0; try exact (xeval_sound F s0 HF _ [] s0 z (agree_nil s0) H).
   destruct (xeval F [] (EBinary w0 BAnd a b)) as [z0|] eqn:Hx.
   + inversion H as [Hz]. rewrite <- Hz. exact (xeval_sound F s0 HF _ [] s0 z0 (agree_nil s0) Hx).
   + assert (Hb : forall z, (match xeval2 F b with Some 0 => Some 0 | _ => None end) = Some z -> eval_expr s0 (EBinary w0 BAnd a b) = z).
     { intros z1 H1. destruct (xeval2 F b) as [[|pb|pb]|] eqn:E2; try discriminate.
       inversion H1; subst. cbn [eval_expr]. rewrite (IHb 0 eq_refl). unfold norm. rewrite ?Z.land_0_l, ?Z.land_0_r. try reflexivity. }
     destruct (xeval2 F a) as [[|pa|pa]|] eqn:E1.
     * inversion H; subst. cbn [eval_expr]. rewrite (IHa 0 eq_refl). unfold norm. rewrite ?Z.land_0_l, ?Z.land_0_r. try reflexivity.
     * exact (Hb z H).
     * exact (Hb z H).
     * exact (Hb z H).
 - destruct (xeval F [] (ECond w0 g a b)) as [z0|] eqn:Hx.
   + inversion H as [Hz]. rewrite <- Hz. exact (xeval_sound F s0 HF _ [] s0 z0 (agree_nil s0) Hx).
   + destruct (xeval2 F g) as [v|] eqn:E1.
   2:{ destruct (xeval2 F a) as [u1|] eqn:E2; [|discriminate]. destruct (xeval2 F b) as [u2|] eqn:E3; [|discriminate].
       destruct (Z.eqb u1 u2) eqn:Hu; [|discriminate]. apply Z.eqb_eq in Hu. subst u2. inversion H; subst.
       cbn [eval_expr]. rewrite (IHa u1 eq_refl), (IHb u1 eq_refl). destruct (Z.eqb (eval_expr s0 g) 0); reflexivity. }
     cbn [eval_expr]. rewrite (IHg v eq_refl).
     destruct (Z.eqb v 0) eqn:Hv.
     * destruct (xeval2 F b) as [u|] eqn:E3; [|discriminate]. inversion H; subst. rewrite (IHb u eq_refl). reflexivity.
     * destruct (xeval2 F a) as [u|] eqn:E2; [|discriminate]. inversion H; subst. rewrite (IHa u eq_refl). reflexivity.
Qed.

Definition guard_ok (ov:SOv) (e:Expr) : bool :=
 forallb (fun wr => negb (existsb (Nat.eqb (snd wr)) (map fst ov))) (expr_inputs e).

Lemma lookup_none ov r : existsb (Nat.eqb r) (map fst ov) = false -> sov_lookup ov r = None.
Proof.
 induction ov as [|[r' v] t IH]; cbn; intro H; [reflexivity|].
 apply orb_false_iff in H as [H1 H2]. rewrite H1. apply IH, H2.
Qed.

Lemma guard_agree ov s0 s e : guard_ok ov e = true -> Agree_s ov s0 s -> eval_expr s e = eval_expr s0 e.
Proof.
 intros Hg [_ HA2]. apply eval_expr_agree. intros w x Hin.
 unfold guard_ok in Hg. rewrite forallb_forall in Hg. specialize (Hg (w,x) Hin). cbn [snd] in Hg.
 apply negb_true_iff in Hg. rewrite (HA2 x (lookup_none ov x Hg)). reflexivity.
Qed.

Fixpoint sselect (F:Facts) (ov:SOv) (v:Z) (arms:list (option Expr * Stmt)) (d:Stmt) : option Stmt :=
 match arms with
 | [] => Some d
 | (None,b)::rest => sselect F ov v rest b
 | (Some k,b)::rest => if guard_ok ov k then
     match xeval2 F k with
     | Some kv => if Z.eqb v kv then Some b else sselect F ov v rest d
     | None => None end else None
 end.

Definition merge_entry (g':Expr) (oy on : SOv) (k:signal) : option (signal*(nat*Expr)) :=
 match sov_lookup oy k, sov_lookup on k with
 | Some (Wy,ey), Some (Wn,en) => if Nat.eqb Wy Wn then Some (k,(Wy, ECond Wy g' ey en)) else None
 | Some (Wy,ey), None => Some (k,(Wy, ECond Wy g' ey (EVar Wy k)))
 | None, Some (Wn,en) => Some (k,(Wn, ECond Wn g' (EVar Wn k) en))
 | None, None => None
 end.
Fixpoint merge_all (g':Expr) (oy on : SOv) (ks:list signal) : option SOv :=
 match ks with
 | [] => Some []
 | k::t => match merge_entry g' oy on k, merge_all g' oy on t with
     | Some a, Some b => Some (a::b) | _, _ => None end
 end.
Definition new_part (ov o : SOv) : SOv := firstn (length o - length ov) o.
Definition merge_if (g':Expr) (ov oy on : SOv) : option SOv :=
 match merge_all g' oy on (map fst (new_part ov oy) ++ map fst (new_part ov on)) with
 | Some m => Some (m ++ ov) | None => None end.

Fixpoint sxexec (F:Facts) (fuel:nat) (st:Stmt) (ov:SOv) {struct fuel} : option SOv :=
 match fuel with
 | O => Some ov
 | S f =>
  match st with
  | SSkip => Some ov
  | SAssign false rhs (LVar w r) =>
     match ssub ov rhs with Some e => Some ((r,(w,e))::ov) | None => None end
  | SAssign false rhs (LSel w (LVar W r) off) =>
     match ssub ov rhs, ssub ov off with
     | Some e, Some o =>
        match (match sov_lookup ov r with
               | Some (W',eo) => if Nat.eqb W' W then Some eo else None
               | None => Some (EVar W r) end) with
        | Some eo => if Nat.leb w W then Some ((r,(W, patch W w eo o e))::ov) else None
        | None => None end
     | _, _ => None end
  | SAssign _ _ _ => None
  | SSeq l => fold_left (fun o st' => match o with Some ov' => sxexec F f st' ov' | None => None end) l (Some ov)
  | SIf g y n => match (if guard_ok ov g then xeval2 F g else None) with
      | Some z => sxexec F f (if Z.eqb z 0 then n else y) ov
      | None => match ssub ov g, sxexec F f y ov, sxexec F f n ov with
          | Some g', Some oy, Some on => merge_if g' ov oy on
          | _, _, _ => None end end
  | SCase scr arms => if guard_ok ov scr then
      match xeval2 F scr with
      | Some v => match sselect F ov v arms SSkip with
         | Some c => sxexec F f c ov | None => None end
      | None => None end else None
  end
 end.

Lemma sov_lookup_app_l (a b : SOv) r : sov_lookup a r <> None -> sov_lookup (a ++ b) r = sov_lookup a r.
Proof. induction a as [|[k v] t IH]; cbn; intro H; [congruence|]. destruct (Nat.eqb r k); [reflexivity|exact (IH H)]. Qed.
Lemma sov_lookup_app_r (a b : SOv) r : sov_lookup a r = None -> sov_lookup (a ++ b) r = sov_lookup b r.
Proof. induction a as [|[k v] t IH]; cbn; intro H; [reflexivity|]. destruct (Nat.eqb r k); [discriminate|exact (IH H)]. Qed.

Definition Ext (ov o : SOv) : Prop := exists new, o = new ++ ov.
Lemma ext_refl ov : Ext ov ov. Proof. exists []. reflexivity. Qed.
Lemma ext_trans a b c : Ext a b -> Ext b c -> Ext a c.
Proof. intros [n1 ->] [n2 ->]. exists (n2 ++ n1). rewrite app_assoc. reflexivity. Qed.

Lemma lookup_app_nin : forall (new ov : SOv) r, ~ In r (map fst new) -> sov_lookup (new ++ ov) r = sov_lookup ov r.
Proof.
 induction new as [|[k v] t IH]; intros ov r H; cbn; [reflexivity|].
 destruct (Nat.eqb r k) eqn:E.
 - apply Nat.eqb_eq in E. subst. exfalso. apply H. left. reflexivity.
 - apply IH. intro Hin. apply H. right. exact Hin.
Qed.

Lemma new_part_ok new ov : new_part ov (new ++ ov) = new.
Proof.
 unfold new_part. rewrite app_length. replace (length new + length ov - length ov)%nat with (length new) by lia.
 rewrite firstn_app, Nat.sub_diag. cbn. rewrite app_nil_r. apply firstn_all.
Qed.

Section Ext.
Variable F : Facts.
Lemma fold_none_e : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => sxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem sxexec_ext : forall fuel st ov ov', sxexec F fuel st ov = Some ov' -> Ext ov ov'.
Proof.
 induction fuel as [|f IH]; intros st ov ov' H; cbn [sxexec] in H.
 - inversion H; subst. apply ext_refl.
 - destruct st as [|nba rhs lhs|l|g y n|scr arms].
   + inversion H; subst. apply ext_refl.
   + destruct nba; [discriminate|]. destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|discriminate]].
     * destruct (ssub ov rhs) as [e|]; [|discriminate]. inversion H; subst. exists [(r,(w,e))]. reflexivity.
     * destruct (ssub ov rhs) as [e|]; [|discriminate]. destruct (ssub ov off) as [o|]; [|discriminate].
       destruct (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) as [eo|]; [|discriminate].
       destruct (Nat.leb w W); [|discriminate]. inversion H; subst. exists [(r,(W, patch W w eo o e))]. reflexivity.
   + assert (Hgen : forall l ov ov', fold_left (fun o st' => match o with Some ov' => sxexec F f st' ov' | None => None end) l (Some ov) = Some ov' -> Ext ov ov').
     { induction l0 as [|a rest IHl]; intros ov0 ov1 H0.
       - cbn in H0. inversion H0; subst. apply ext_refl.
       - cbn in H0. destruct (sxexec F f a ov0) as [o1|] eqn:Ea; [|rewrite fold_none_e in H0; discriminate].
         exact (ext_trans _ _ _ (IH _ _ _ Ea) (IHl _ _ H0)). }
     exact (Hgen l ov ov' H).
   + destruct (if guard_ok ov g then xeval2 F g else None) as [z|].
     * exact (IH _ _ _ H).
     * destruct (ssub ov g) as [g'|]; [|discriminate]. destruct (sxexec F f y ov) as [oy|]; [|discriminate].
       destruct (sxexec F f n ov) as [on|]; [|discriminate]. unfold merge_if in H.
       destruct (merge_all g' oy on _) as [m|]; [|discriminate]. inversion H; subst. exists m. reflexivity.
   + destruct (guard_ok ov scr); [|discriminate]. destruct (xeval2 F scr) as [v|]; [|discriminate].
     destruct (sselect F ov v arms SSkip) as [c|]; [|discriminate]. exact (IH _ _ _ H).
Qed.
End Ext.

Lemma merge_all_lookup g' oy on : forall ks m, merge_all g' oy on ks = Some m ->
 (forall k, In k ks -> exists ent, sov_lookup m k = Some ent /\ merge_entry g' oy on k = Some (k, ent)) /\
 (forall k, ~ In k ks -> sov_lookup m k = None).
Proof.
 induction ks as [|k0 t IH]; intros m H; cbn [merge_all] in H.
 - inversion H; subst. split; [intros k [] |intros k _; reflexivity].
 - destruct (merge_entry g' oy on k0) as [a|] eqn:Ea; [|discriminate].
   destruct (merge_all g' oy on t) as [b|] eqn:Eb; [|discriminate]. inversion H; subst.
   destruct (IH b eq_refl) as [IH1 IH2]. destruct a as [ka enta].
   assert (Hk : ka = k0).
   { unfold merge_entry in Ea. destruct (sov_lookup oy k0) as [[Wy ey]|], (sov_lookup on k0) as [[Wn en]|]; try discriminate;
     try (destruct (Nat.eqb Wy Wn); [|discriminate]); inversion Ea; reflexivity. }
   subst ka. split.
   + intros k Hk. cbn [sov_lookup]. destruct (Nat.eqb k k0) eqn:E.
     * apply Nat.eqb_eq in E. subst k. exists enta. split; [reflexivity|exact Ea].
     * destruct Hk as [Hk|Hk]; [apply Nat.eqb_neq in E; congruence|exact (IH1 k Hk)].
   + intros k Hk. cbn [sov_lookup]. destruct (Nat.eqb k k0) eqn:E.
     * apply Nat.eqb_eq in E. subst. exfalso. apply Hk. left. reflexivity.
     * apply IH2. intro Hin. apply Hk. right. exact Hin.
Qed.

Lemma merge_if_sound s0 g' ov oy on ov' sy sn s' :
 merge_if g' ov oy on = Some ov' -> Ext ov oy -> Ext ov on -> Agree_s oy s0 sy -> Agree_s on s0 sn ->
 ((eval_expr s0 g' <> 0 /\ s' = sy) \/ (eval_expr s0 g' = 0 /\ s' = sn)) -> Agree_s ov' s0 s'.
Proof.
 intros Hm [ny Hy] [nn Hn] [Ay1 Ay2] [An1 An2] Hs. unfold merge_if in Hm.
 destruct (merge_all g' oy on _) as [m|] eqn:Hma; [|discriminate]. inversion Hm; subst ov'. clear Hm.
 rewrite Hy, new_part_ok in Hma. rewrite Hn, new_part_ok in Hma.
 destruct (merge_all_lookup g' (ny ++ ov) (nn ++ ov) _ m Hma) as [M1 M2].
 set (ks := map fst ny ++ map fst nn) in *.
 assert (Hy_ : oy = ny ++ ov) by exact Hy. assert (Hn_ : on = nn ++ ov) by exact Hn. subst oy on.
 split.
 - intros r w e Hl. destruct (in_dec Nat.eq_dec r ks) as [Hin|Hin].
   + destruct (M1 r Hin) as [ent [Hle Hme]]. rewrite sov_lookup_app_l in Hl by (rewrite Hle; discriminate).
     rewrite Hle in Hl. inversion Hl; subst ent. clear Hl.
     unfold merge_entry in Hme.
     destruct (sov_lookup (ny ++ ov) r) as [[Wy ey]|] eqn:Ly, (sov_lookup (nn ++ ov) r) as [[Wn en]|] eqn:Ln; try discriminate.
     * destruct (Nat.eqb Wy Wn) eqn:EW; [|discriminate]. apply Nat.eqb_eq in EW. subst Wn. inversion Hme; subst w e.
       destruct Hs as [[Hg ->]|[Hg ->]].
       -- cbn [eval_expr]. destruct (Z.eqb_spec (eval_expr s0 g') 0); [congruence|]. rewrite norm_idempotent. exact (Ay1 _ _ _ Ly).
       -- cbn [eval_expr]. destruct (Z.eqb_spec (eval_expr s0 g') 0); [|congruence]. rewrite norm_idempotent. exact (An1 _ _ _ Ln).
     * inversion Hme; subst w e. destruct Hs as [[Hg ->]|[Hg ->]].
       -- cbn [eval_expr]. destruct (Z.eqb_spec (eval_expr s0 g') 0); [congruence|]. rewrite norm_idempotent. exact (Ay1 _ _ _ Ly).
       -- cbn [eval_expr]. destruct (Z.eqb_spec (eval_expr s0 g') 0); [|congruence]. rewrite norm_idempotent.
          rewrite (An2 _ Ln). cbn [eval_expr]. rewrite norm_idempotent. reflexivity.
     * inversion Hme; subst w e. destruct Hs as [[Hg ->]|[Hg ->]].
       -- cbn [eval_expr]. destruct (Z.eqb_spec (eval_expr s0 g') 0); [congruence|]. rewrite norm_idempotent.
          rewrite (Ay2 _ Ly). cbn [eval_expr]. rewrite norm_idempotent. reflexivity.
       -- cbn [eval_expr]. destruct (Z.eqb_spec (eval_expr s0 g') 0); [|congruence]. rewrite norm_idempotent. exact (An1 _ _ _ Ln).
   + rewrite sov_lookup_app_r in Hl by exact (M2 r Hin).
     assert (Hny : ~ In r (map fst ny)) by (intro; apply Hin; apply in_or_app; left; assumption).
     assert (Hnn : ~ In r (map fst nn)) by (intro; apply Hin; apply in_or_app; right; assumption).
     destruct Hs as [[Hg ->]|[Hg ->]].
     * apply (Ay1 r w e). rewrite lookup_app_nin by exact Hny. exact Hl.
     * apply (An1 r w e). rewrite lookup_app_nin by exact Hnn. exact Hl.
 - intros r Hl. destruct (in_dec Nat.eq_dec r ks) as [Hin|Hin].
   + destruct (M1 r Hin) as [ent [Hle _]]. rewrite sov_lookup_app_l in Hl by (rewrite Hle; discriminate). rewrite Hle in Hl. discriminate.
   + rewrite sov_lookup_app_r in Hl by exact (M2 r Hin).
     assert (Hny : ~ In r (map fst ny)) by (intro; apply Hin; apply in_or_app; left; assumption).
     assert (Hnn : ~ In r (map fst nn)) by (intro; apply Hin; apply in_or_app; right; assumption).
     destruct Hs as [[Hg ->]|[Hg ->]].
     * apply Ay2. rewrite lookup_app_nin by exact Hny. exact Hl.
     * apply An2. rewrite lookup_app_nin by exact Hnn. exact Hl.
Qed.

Section Sound.
Variable F : Facts.
Variable s0 : State.
Hypothesis HF : FactsHold s0 F.

Lemma guard_val ov s g z : guard_ok ov g = true -> Agree_s ov s0 s -> xeval2 F g = Some z -> eval_expr s g = z.
Proof.
 intros Hg HA Hx. rewrite (guard_agree ov s0 s g Hg HA). exact (xeval2_sound F s0 HF g z Hx).
Qed.

Lemma sselect_sound : forall arms ov s v d c, Agree_s ov s0 s -> sselect F ov v arms d = Some c ->
 select_case_stmt s v arms d = c.
Proof.
 induction arms as [|[[k|] b] rest IH]; intros ov s v d c HA H; cbn [sselect] in H.
 - inversion H; reflexivity.
 - destruct (guard_ok ov k) eqn:Hg; [|discriminate]. destruct (xeval2 F k) as [kv|] eqn:Ek; [|discriminate].
   cbn [select_case_stmt]. rewrite (guard_val ov s k kv Hg HA Ek).
   destruct (Z.eqb v kv); [now inversion H|exact (IH _ _ _ _ _ HA H)].
 - cbn [select_case_stmt]. exact (IH _ _ _ _ _ HA H).
Qed.

Lemma agree_s_var ov s w r e rhs : Agree_s ov s0 s -> ssub ov rhs = Some e ->
 Agree_s ((r,(w,e))::ov) s0 (apply_update s (resolve_update s (LVar w r) (eval_expr s rhs))).
Proof.
 intros HA Hs. destruct (ssub_sound ov s0 s HA rhs e Hs) as [Hv _]. destruct HA as [H1 H2].
 unfold apply_update, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 split.
 - intros r' w' e' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr.
   + apply Nat.eqb_eq in Hr; subst. inversion Hl; subst.
     rewrite read_signal_write_same, norm_full_low_write. rewrite Hv. unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
   + rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
     exact (H1 _ _ _ Hl).
 - intros r' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
   exact (H2 _ Hl).
Qed.

Lemma agree_s_slice ov s W w r eo o e rhs off : Agree_s ov s0 s ->
 ssub ov rhs = Some e -> ssub ov off = Some o -> (w <= W)%nat ->
 (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) = Some eo ->
 Agree_s ((r,(W, patch W w eo o e))::ov) s0
   (apply_update s (resolve_update s (LSel w (LVar W r) off) (eval_expr s rhs))).
Proof.
 intros HA Hs Ho Hw Hold. destruct (ssub_sound ov s0 s HA rhs e Hs) as [Hv _].
 destruct (ssub_sound ov s0 s HA off o Ho) as [Hoff _].
 assert (HR : norm W (read_signal s r) = norm W (eval_expr s0 eo)).
 { destruct HA as [H1 H2]. destruct (sov_lookup ov r) as [[W' eo']|] eqn:Hl.
   - destruct (Nat.eqb W' W) eqn:HW; [|discriminate]. apply Nat.eqb_eq in HW; subst. inversion Hold; subst. exact (H1 _ _ _ Hl).
   - inversion Hold; subst. cbn [eval_expr]. rewrite (H2 _ Hl). unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. }
 destruct HA as [H1 H2].
 unfold apply_update, resolve_update. cbn [resolve_lvalue update_signal update_offset update_width update_value].
 rewrite Hoff.
 split.
 - intros r' w' e' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr.
   + apply Nat.eqb_eq in Hr; subst. inversion Hl; subst.
     rewrite read_signal_write_same. rewrite Hv.
     rewrite (patch_arith _ w (read_signal s r) (eval_expr s0 eo) (eval_expr s0 o) (eval_expr s0 e) Hw (eval_nonneg s0 o) HR) by lia.
     cbn [patch eval_expr]. rewrite norm_idempotent. reflexivity.
   + rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
     exact (H1 _ _ _ Hl).
 - intros r' Hl. cbn [sov_lookup] in Hl.
   destruct (Nat.eqb r' r) eqn:Hr; [discriminate|].
   rewrite read_signal_write_other by (intro E; apply Nat.eqb_neq in Hr; congruence).
   exact (H2 _ Hl).
Qed.

Lemma fold_none : forall (l:list Stmt) f, fold_left (fun o st' => match o with Some ov' => sxexec F f st' ov' | None => None end) l None = None.
Proof. induction l; intros; cbn; [reflexivity|apply IHl]. Qed.

Theorem sxexec_sound : forall fuel st ov ov' es,
 sxexec F fuel st ov = Some ov' -> Agree_s ov s0 (blocking_state es) ->
 Agree_s ov' s0 (blocking_state (exec_stmt fuel st es)) /\
 pending_nba (exec_stmt fuel st es) = pending_nba es.
Proof.
 induction fuel as [|f IH]; intros st ov ov' es H HA.
 - cbn in H. inversion H; subst. cbn. split; [exact HA|reflexivity].
 - destruct st as [|nba rhs lhs|l|g y n|scr arms]; cbn [sxexec exec_stmt] in *.
   + inversion H; subst. split; [exact HA|reflexivity].
   + destruct nba; [discriminate|]. destruct lhs as [w r|w base off]; [|destruct base as [W r|]; [|discriminate]].
     * destruct (ssub ov rhs) as [e|] eqn:Es; [|discriminate]. inversion H; subst.
       cbn [blocking_state pending_nba]. split; [exact (agree_s_var ov _ w r e rhs HA Es)|reflexivity].
     * destruct (ssub ov rhs) as [e|] eqn:Es; [|discriminate]. destruct (ssub ov off) as [o|] eqn:Eo; [|discriminate].
       destruct (match sov_lookup ov r with Some (W',eo') => if Nat.eqb W' W then Some eo' else None | None => Some (EVar W r) end) as [eo|] eqn:Eold; [|discriminate].
       destruct (Nat.leb w W) eqn:Hle; [|discriminate]. inversion H; subst. apply Nat.leb_le in Hle.
       cbn [blocking_state pending_nba]. split; [exact (agree_s_slice ov _ W w r eo o e rhs off HA Es Eo Hle Eold)|reflexivity].
   + assert (Hgen: forall l ov ov' es,
        fold_left (fun o st' => match o with Some ov' => sxexec F f st' ov' | None => None end) l (Some ov) = Some ov' ->
        Agree_s ov s0 (blocking_state es) ->
        Agree_s ov' s0 (blocking_state (fold_left (fun es' st' => exec_stmt f st' es') l es)) /\
        pending_nba (fold_left (fun es' st' => exec_stmt f st' es') l es) = pending_nba es).
     { induction l0 as [|a rest IHl]; intros ov0 ov1 es0 H0 HA0.
       - cbn in H0. inversion H0; subst. cbn. split; [exact HA0|reflexivity].
       - cbn [fold_left] in H0 |- *. cbn in H0.
         destruct (sxexec F f a ov0) as [o1|] eqn:Ea; [|rewrite fold_none in H0; discriminate].
         destruct (IH _ _ _ es0 Ea HA0) as [HA1 HP1].
         destruct (IHl _ _ _ H0 HA1) as [HA2 HP2]. split; [exact HA2|congruence]. }
     exact (Hgen l ov ov' es H HA).
   + destruct (if guard_ok ov g then xeval2 F g else None) as [z|] eqn:Ez.
     * destruct (guard_ok ov g) eqn:Hg; [|discriminate].
       rewrite (guard_val ov _ g z Hg HA Ez). exact (IH _ _ _ _ H HA).
     * destruct (ssub ov g) as [g'|] eqn:Eg; [|discriminate]. destruct (sxexec F f y ov) as [oy|] eqn:Ey; [|discriminate].
       destruct (sxexec F f n ov) as [on|] eqn:En; [|discriminate].
       destruct (IH y ov oy es Ey HA) as [Ay Py]. destruct (IH n ov on es En HA) as [An Pn].
       destruct (ssub_sound ov s0 _ HA g g' Eg) as [Hg _]. rewrite Hg.
       destruct (Z.eqb_spec (eval_expr s0 g') 0) as [Hz|Hz].
       -- split; [|exact Pn]. exact (merge_if_sound s0 g' ov oy on ov' _ _ _ H (sxexec_ext F _ _ _ _ Ey) (sxexec_ext F _ _ _ _ En) Ay An (or_intror (conj Hz eq_refl))).
       -- split; [|exact Py]. exact (merge_if_sound s0 g' ov oy on ov' _ _ _ H (sxexec_ext F _ _ _ _ Ey) (sxexec_ext F _ _ _ _ En) Ay An (or_introl (conj Hz eq_refl))).
   + destruct (guard_ok ov scr) eqn:Hg; [|discriminate]. destruct (xeval2 F scr) as [v|] eqn:Ev; [|discriminate].
     destruct (sselect F ov v arms SSkip) as [c|] eqn:Ec; [|discriminate].
     rewrite (guard_val ov _ scr v Hg HA Ev), (sselect_sound _ _ _ _ _ _ HA Ec).
     exact (IH _ _ _ _ H HA).
Qed.

Theorem sxrun_process_sound p proc ov :
 sxexec F (statement_fuel p) (process_body proc) [] = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> norm w (read_signal (run_process p s0 proc) r) = norm w (eval_expr s0 e).
Proof.
 intros H r w e Hl. unfold run_process.
 destruct (sxexec_sound _ _ _ _ {|blocking_state:=s0;pending_nba:=[];emitted_updates:=[]|} H (agree_s_nil s0)) as [[HA1 _] HP].
 cbn [pending_nba] in HP. rewrite HP. cbn [apply_nba]. exact (HA1 _ _ _ Hl).
Qed.
End Sound.

Definition inputs_okb (T:list (list nat)) (k:nat) (e:Expr) : bool :=
 forallb (fun wr => wr_ge T (snd wr) k || wr_lt T (snd wr) k) (expr_inputs e).

(** Transfer to the combinational fixed point: the value of a root written by the comb process at position [k]. *)
Theorem sxrun_comb_lfp p ps T k proc F ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F T k = true ->
 FactsHold fixed F -> CombLFP p seed fixed ->
 sxexec F (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 forall r w e, sov_lookup ov r = Some (w,e) -> wr_lt T r (S k) = true -> inputs_okb T k e = true ->
 norm w (read_signal fixed r) = norm w (eval_expr fixed e).
Proof.
 intros HP HT HN Hok HFH HL Hx r w e Hl Hr Hie.
 pose proof (eq_trans HP (split_at ps k proc HN)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn k ps) proc (skipn (S k) ps) r seed fixed Horder (unw_suffix ps T (S k) r HT Hr) HL).
 set (S0 := fold_left (run_process p) (firstn k ps) fixed).
 assert (Hagree : forall wd x, wr_ge T x k || wr_lt T x k = true -> norm wd (read_signal S0 x) = norm wd (read_signal fixed x)).
 { intros wd x Hc. unfold S0. apply orb_true_iff in Hc as [Hc|Hc].
   - rewrite (fold_run_process_preserves_root p (firstn k ps) x fixed (roots_unwrittenb_sound _ _ (unw_prefix ps T k x HT Hc))). reflexivity.
   - rewrite (actual_lfp_pivot_input p (firstn k ps) proc (skipn (S k) ps) x seed fixed Horder
       (eq_ind (skipn k ps) (fun l => roots_unwrittenb x l = true) (unw_suffix ps T k x HT Hc) _ (skipn_nth_cons ps k proc HN)) HL). reflexivity. }
 assert (HFS : FactsHold S0 F).
 { intros e0 zz HI. rewrite <- (HFH e0 zz HI). apply eval_expr_agree. intros wd x Hin.
   unfold facts_inputs_okb in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (e0,zz) HI). cbn [fst] in Hok. rewrite forallb_forall in Hok.
   specialize (Hok (wd,x) Hin). cbn [snd] in Hok. exact (Hagree wd x Hok). }
 rewrite run_process_nbfix. rewrite (sxrun_process_sound F S0 HFS p {| process_kind := process_kind proc; process_events := process_events proc; process_body := nbfix (process_body proc); process_source_line := process_source_line proc |} ov Hx r w e Hl).
 f_equal. apply eval_expr_agree. intros wd x Hin.
 unfold inputs_okb in Hie. rewrite forallb_forall in Hie. specialize (Hie (wd,x) Hin). cbn [snd] in Hie.
 exact (Hagree wd x Hie).
Qed.


Definition sx_new_facts (F0:Facts) (T:list (list nat)) (k:nat) (ov:SOv) : Facts :=
 flat_map (fun r => match sov_lookup ov r with
   | Some (w,e) => if wr_lt T r (S k) && inputs_okb T k e then
        match xeval2 F0 e with Some z => [(EVar w r, norm w z)] | None => [] end else []
   | None => [] end) (map fst ov).

Lemma sx_new_facts_sound p ps T k proc F0 ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F0 T k = true -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 sxexec F0 (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 FactsHold fixed (sx_new_facts F0 T k ov).
Proof.
 intros HP HT HN Hok HF HL Hx e0 z0 HI. unfold sx_new_facts in HI. apply in_flat_map in HI as [r [Hr HI]].
 destruct (sov_lookup ov r) as [[w e]|] eqn:Hl; [|contradiction].
 destruct (wr_lt T r (S k) && inputs_okb T k e) eqn:Hc; [|contradiction].
 apply andb_true_iff in Hc as [Hc1 Hc2].
 destruct (xeval2 F0 e) as [z|] eqn:Hxe; [|contradiction].
 destruct HI as [HI|[]]. inversion HI; subst e0 z0. cbn [eval_expr].
 rewrite (sxrun_comb_lfp p ps T k proc F0 ov seed fixed HP HT HN Hok HF HL Hx r w e Hl Hc1 Hc2).
 rewrite (xeval2_sound F0 fixed HF e z Hxe). reflexivity.
Qed.

Definition sx_step (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) : Facts :=
 match nth_error ps k with
 | None => F
 | Some proc =>
   let F0 := filter (tail_okb T k) F in
   match sxexec F0 fuel (nbfix (process_body proc)) [] with
   | None => F
   | Some ov => F ++ sx_new_facts F0 T k ov
   end
 end.

Lemma sx_step_sound p ps T fuel F k seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 FactsHold fixed F -> CombLFP p seed fixed -> FactsHold fixed (sx_step ps T fuel F k).
Proof.
 intros HP HT Hf HF HL. unfold sx_step. subst fuel.
 destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HF].
 set (F0 := filter (tail_okb T k) F).
 destruct (sxexec F0 (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HF].
 assert (H0 : FactsHold fixed F0) by (intros e z HI; apply filter_In in HI as [HI _]; apply HF, HI).
 assert (Hok : facts_inputs_okb F0 T k = true).
 { unfold facts_inputs_okb. apply forallb_forall. intros ez HI. apply filter_In in HI as [_ HT'].
   exact HT'. }
 intros e z HI. apply in_app_or in HI as [HI|HI]; [apply HF, HI|].
 exact (sx_new_facts_sound p ps T k proc F0 ov seed fixed HP HT HN Hok H0 HL Hx e z HI).
Qed.

Fixpoint sx_pass (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (ks:list nat) : Facts :=
 match ks with [] => F | k::t => sx_pass ps T fuel (sx_step ps T fuel F k) t end.
Fixpoint sx_run (ps:list Process) (T:list (list nat)) (fuel:nat) (rounds:nat) (F:Facts) : Facts :=
 match rounds with O => F | S r => sx_run ps T fuel r (sx_pass ps T fuel F (seq 0 (length ps))) end.

Lemma sx_pass_sound p ps T fuel seed fixed : filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 CombLFP p seed fixed -> forall ks F, FactsHold fixed F -> FactsHold fixed (sx_pass ps T fuel F ks).
Proof.
 intros HP HT Hf HL. induction ks as [|k t IH]; intros F HF; cbn [sx_pass]; [exact HF|].
 apply IH. exact (sx_step_sound p ps T fuel F k seed fixed HP HT Hf HF HL).
Qed.
Lemma sx_run_sound p ps T fuel seed fixed : filter is_comb (processes p) = ps -> TabC ps T -> fuel = statement_fuel p ->
 CombLFP p seed fixed -> forall rounds F, FactsHold fixed F -> FactsHold fixed (sx_run ps T fuel rounds F).
Proof.
 intros HP HT Hf HL. induction rounds as [|r IH]; intros F HF; cbn [sx_run]; [exact HF|].
 apply IH. exact (sx_pass_sound p ps T fuel seed fixed HP HT Hf HL _ F HF).
Qed.

Theorem sx_run_outs p ps T rounds F0 outs seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 outs_in_facts (sx_run ps T (statement_fuel p) rounds F0) outs = true -> DecOut fixed outs.
Proof.
 intros HP HT HF HL H. 
 pose proof (sx_run_sound p ps T (statement_fuel p) seed fixed HP HT eq_refl HL rounds F0 HF) as HF'.
 intros t Ht'. unfold outs_in_facts in H. rewrite forallb_forall in H. specialize (H t Ht').
 destruct (fact_find (sx_run ps T (statement_fuel p) rounds F0) (EVar (snd (fst t)) (fst (fst t)))) as [z|] eqn:Hf; [|discriminate].
 apply Z.eqb_eq in H. subst z.
 pose proof (fact_find_sound _ _ _ fixed HF' Hf) as Hv. cbn [eval_expr] in Hv. exact Hv.
Qed.

Definition lane (x j : Z) : Z := Z.land (Z.shiftr x (32 * j)) (2 ^ 32 - 1).
Lemma tb_m32 j : Z.testbit (2 ^ 32 - 1) j = (0 <=? j) && (j <? 32).
Proof. exact (tb_mask 32 j). Qed.

Ltac simp_bits := repeat (first [ rewrite tb_norm | rewrite Z.lor_spec | rewrite Z.land_spec | rewrite Z.lnot_spec by lia
                | rewrite tb_shl' by lia | rewrite tb_m32 | rewrite tb_mask ]).

Ltac cmp := repeat match goal with
 | |- context [(?x <=? ?y)] =>
    first [ let h := fresh in assert (h : (x <=? y) = true) by (apply Z.leb_le; lia); rewrite h; clear h
          | let h := fresh in assert (h : (x <=? y) = false) by (apply Z.leb_gt; lia); rewrite h; clear h ]
 | |- context [(?x <? ?y)] =>
    first [ let h := fresh in assert (h : (x <? y) = true) by (apply Z.ltb_lt; lia); rewrite h; clear h
          | let h := fresh in assert (h : (x <? y) = false) by (apply Z.ltb_ge; lia); rewrite h; clear h ]
 end.

Ltac simp2 := repeat (first [ rewrite tb_norm | rewrite Z.lor_spec | rewrite Z.land_spec | rewrite Z.lnot_spec by lia
                | rewrite tb_shl' by lia | rewrite Z.shiftr_spec by lia | rewrite tb_m32 | rewrite tb_mask ]).
Ltac dtb := repeat match goal with |- context [Z.testbit ?x ?y] => destruct (Z.testbit x y) end.

Lemma lane_wr R V a j : (a = 0 \/ a = 1) -> (j = 0 \/ j = 1) ->
 lane (norm 64 (write_slice R (0 + 32 * a) 32 (norm 32 V))) j =
 if Z.eqb j a then norm 32 V else lane (norm 64 R) j.
Proof.
 intros Ha Hj. apply Z.bits_inj'. intros m Hm.
 destruct Ha as [ -> | -> ]; destruct Hj as [ -> | -> ]; cbn [Z.eqb Pos.eqb]; cbv iota; unfold lane, write_slice; simp2; rewrite ?Z.add_0_l, ?Z.mul_0_r, ?Z.add_0_r, ?Z.add_simpl_r, ?Z.sub_0_r;
  change (Z.of_nat 64) with 64; change (Z.of_nat 32) with 32; destruct (Z.ltb_spec m 32); cmp; cbn [andb orb negb]; rewrite ?andb_false_r; cbn [andb orb negb]; dtb; reflexivity.
Qed.
End ExtendedSVSymExecSym.
Print Assumptions ExtendedSVSymExecSym.sxrun_comb_lfp.
Print Assumptions ExtendedSVSymExecSym.lane_wr.
Print Assumptions ExtendedSVSymExecSym.sx_run_outs.
