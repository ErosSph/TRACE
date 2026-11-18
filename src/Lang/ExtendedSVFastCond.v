(** Backward propagation through 1-bit conditionals (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [decomp2] = [ExtendedSVBackward.decomp] plus the rule for [ECond 1 g y n] with a constant arm that differs from the wanted value:
    the other arm is taken, i.e. [g] is decided and the remaining arm is decomposed further (e.g. [ECond g 1 X = 0] gives [g = 0] and [X = 0]).
    [fback2] / [frun2] / [check_shared2] mirror the ExtendedSVSymExecFast versions with [decomp2]. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay
 Lang.ExtendedSVBackOverlay Lang.ExtendedSVEval3 Lang.ExtendedSVBackward Lang.ExtendedSVExpressionFold Lang.ExtendedSVSymExecFast.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecOverlay ExtendedSVBackOverlay ExtendedSVEval3
 ExtendedSVBackward ExtendedSVExpressionFold ExtendedSVSymExecFast.
Local Open Scope Z_scope.
Module ExtendedSVFastCond.

Definition const1 (e:Expr) : option Z := match e with EConst 1%nat c => Some (norm 1 c) | _ => None end.

Fixpoint decomp2 (v:Z) (e:Expr) : Facts :=
  match e with
  | EBinary 1%nat BAnd a b =>
      if Z.eqb v 1 && Nat.eqb (expr_width a) 1 && Nat.eqb (expr_width b) 1 then decomp2 1 a ++ decomp2 1 b else [(e, v)]
  | EBinary 1%nat BOr a b =>
      if Z.eqb v 0 && Nat.eqb (expr_width a) 1 && Nat.eqb (expr_width b) 1 then decomp2 0 a ++ decomp2 0 b else [(e, v)]
  | EUnary 1%nat UNot a =>
      if (Z.eqb v 0 || Z.eqb v 1) && Nat.eqb (expr_width a) 1 then decomp2 (1 - v) a else [(e, v)]
  | ECond 1%nat g y n =>
      if (Z.eqb v 0 || Z.eqb v 1) && Nat.eqb (expr_width g) 1 && Nat.eqb (expr_width y) 1 && Nat.eqb (expr_width n) 1 then
        match const1 y with
        | Some c => if Z.eqb c (1 - v) then decomp2 0 g ++ decomp2 v n
                    else match const1 n with
                         | Some c' => if Z.eqb c' (1 - v) then decomp2 1 g ++ decomp2 v y else [(e, v)]
                         | None => [(e, v)] end
        | None => match const1 n with
                  | Some c' => if Z.eqb c' (1 - v) then decomp2 1 g ++ decomp2 v y else [(e, v)]
                  | None => [(e, v)] end
        end
      else [(e, v)]
  | _ => [(e, v)]
  end.

Lemma cond_split s g y n v : (v = 0 \/ v = 1) -> expr_width g = 1%nat -> expr_width y = 1%nat -> expr_width n = 1%nat ->
  eval_expr s (ECond 1%nat g y n) = v ->
  (eval_expr s g = 0 /\ eval_expr s n = v) \/ (eval_expr s g = 1 /\ eval_expr s y = v).
Proof.
  intros Hv Wg Wy Wn H. cbn [eval_expr] in H.
  destruct (eval_bit s g Wg) as [X|X]; destruct (eval_bit s y Wy) as [Y|Y]; destruct (eval_bit s n Wn) as [Z|Z];
    rewrite ?X, ?Y, ?Z in H; cbn in H; vm_compute in H; destruct Hv as [Hv0|Hv0]; subst v; try discriminate H;
    first [ (left; split; assumption) | (right; split; assumption) | (exfalso; lia) ].
Qed.

Lemma const1_eval s e c : const1 e = Some c -> eval_expr s e = c.
Proof. destruct e; cbn [const1]; try discriminate. destruct width; try discriminate. destruct width; try discriminate.
  intro H. inversion H; subst. reflexivity. Qed.

Lemma decomp2_sound s : forall e v, eval_expr s e = v -> FactsHold s (decomp2 v e).
Proof.
  induction e as [wc vc | wv xv | ws bs ls Ib1 Ib2 | wcc hc lc Ic1 Ic2 | wr cr br Ir | wex sgn bex Iex | wu opu e IHe | wb opb e1 IHe1 e2 IHe2 | wq gq IHg yq IHy nq IHn]; intros v H; cbn [decomp2].
  1-6: (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
  - (* unary *) destruct wu as [|[|w]]; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct opu; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct ((Z.eqb v 0 || Z.eqb v 1) && Nat.eqb (expr_width e) 1) eqn:C;
      [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
    apply andb_true_iff in C as [C W]. apply Nat.eqb_eq in W.
    cbn [eval_expr] in H.
    destruct (eval_bit s e W) as [X|X]; rewrite X in H; vm_compute in H; subst v;
      [apply (IHe 0 X) | apply (IHe 1 X)].
  - (* binary *) destruct wb as [|[|w]]; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct opb; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    + destruct (Z.eqb v 1 && Nat.eqb (expr_width e1) 1 && Nat.eqb (expr_width e2) 1) eqn:C;
        [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
      apply andb_true_iff in C as [C W2]. apply andb_true_iff in C as [C W1].
      apply Z.eqb_eq in C. apply Nat.eqb_eq in W1. apply Nat.eqb_eq in W2. rewrite C in H.
      cbn [eval_expr] in H.
      destruct (eval_bit s e1 W1) as [X|X]; destruct (eval_bit s e2 W2) as [Y|Y]; rewrite X, Y in H; try (vm_compute in H; discriminate H).
      intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHe1 1 X e0 z0 HI) | exact (IHe2 1 Y e0 z0 HI)].
    + destruct (Z.eqb v 0 && Nat.eqb (expr_width e1) 1 && Nat.eqb (expr_width e2) 1) eqn:C;
        [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
      apply andb_true_iff in C as [C W2]. apply andb_true_iff in C as [C W1].
      apply Z.eqb_eq in C. apply Nat.eqb_eq in W1. apply Nat.eqb_eq in W2. rewrite C in H.
      cbn [eval_expr] in H.
      destruct (eval_bit s e1 W1) as [X|X]; destruct (eval_bit s e2 W2) as [Y|Y]; rewrite X, Y in H; try (vm_compute in H; discriminate H).
      intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHe1 0 X e0 z0 HI) | exact (IHe2 0 Y e0 z0 HI)].
  - (* cond *)
    destruct wq as [|[|w]]; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct ((Z.eqb v 0 || Z.eqb v 1) && Nat.eqb (expr_width gq) 1 && Nat.eqb (expr_width yq) 1 && Nat.eqb (expr_width nq) 1) eqn:C;
      [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
    apply andb_true_iff in C as [C Wn]. apply andb_true_iff in C as [C Wy]. apply andb_true_iff in C as [C0 Wg].
    apply Nat.eqb_eq in Wn. apply Nat.eqb_eq in Wy. apply Nat.eqb_eq in Wg.
    assert (Hv : v = 0 \/ v = 1) by (apply orb_true_iff in C0 as [C0|C0]; apply Z.eqb_eq in C0; auto).
    pose proof (cond_split s gq yq nq v Hv Wg Wy Wn H) as Hs.
    assert (RA : forall c, const1 yq = Some c -> c = 1 - v -> eval_expr s gq = 0 /\ eval_expr s nq = v).
    { intros c Hc Hcv. destruct Hs as [Hs|[Hg Hy]]; [exact Hs|]. exfalso. rewrite (const1_eval s yq c Hc) in Hy. lia. }
    assert (RB : forall c, const1 nq = Some c -> c = 1 - v -> eval_expr s gq = 1 /\ eval_expr s yq = v).
    { intros c Hc Hcv. destruct Hs as [[Hg Hn]|Hs]; [|exact Hs]. exfalso. rewrite (const1_eval s nq c Hc) in Hn. lia. }
    assert (Hleaf : FactsHold s [(ECond 1%nat gq yq nq, v)]) by (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct (const1 yq) as [c|] eqn:Ey.
    + destruct (Z.eqb c (1 - v)) eqn:E1.
      * apply Z.eqb_eq in E1. destruct (RA c eq_refl E1) as [G N]. intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHg 0 G e0 z0 HI) | exact (IHn v N e0 z0 HI)].
      * destruct (const1 nq) as [c'|] eqn:En; [|exact Hleaf]. destruct (Z.eqb c' (1 - v)) eqn:E2; [|exact Hleaf].
        apply Z.eqb_eq in E2. destruct (RB c' eq_refl E2) as [G Y]. intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHg 1 G e0 z0 HI) | exact (IHy v Y e0 z0 HI)].
    + destruct (const1 nq) as [c'|] eqn:En; [|exact Hleaf]. destruct (Z.eqb c' (1 - v)) eqn:E2; [|exact Hleaf].
      apply Z.eqb_eq in E2. destruct (RB c' eq_refl E2) as [G Y]. intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHg 1 G e0 z0 HI) | exact (IHy v Y e0 z0 HI)].
Qed.

(** fast-store backward step with decomp2 *)
Definition back_one2 (T:list (list nat)) (k:nat) (fs:FS) (ov:SOv) (r:signal) : Facts :=
  match fs_find fs 1%nat r with
  | None => []
  | Some v =>
    match (if wr_lt T r (S k) then sov_lookup ov r else None) with
    | Some (1%nat, e) => if Nat.eqb (expr_width e) 1 && inputs_okb T k e then decomp2 v e else []
    | _ => []
    end
  end.

Lemma back_one2_sound p ps T k proc F0u fs ov seed fixed r :
  filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc -> CombLFP p seed fixed -> FactsHold fixed F0u -> SHold fixed fs ->
  oxexec (filter (tail_okb T k) F0u) (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
  FactsHold fixed (back_one2 T k fs ov r).
Proof.
  intros HP HT HN HL HF HS Hx. unfold back_one2.
  destruct (fs_find fs 1%nat r) as [v|] eqn:Hf; [|intros e z HI; destruct HI].
  destruct (wr_lt T r (S k)) eqn:Hr; [|intros e z HI; destruct HI].
  destruct (sov_lookup ov r) as [[w e]|] eqn:Hl; [|intros e0 z HI; destruct HI].
  destruct w as [|[|w]]; try (intros e0 z HI; destruct HI).
  destruct (Nat.eqb (expr_width e) 1 && inputs_okb T k e) eqn:C; [|intros e0 z HI; destruct HI].
  apply andb_true_iff in C as [W Hi]. apply Nat.eqb_eq in W.
  assert (Hv : eval_expr fixed (EVar 1%nat r) = v).
  { cbn [eval_expr]. destruct HS as [H1 _]. exact (H1 _ _ _ (find_in fs 1%nat r v Hf)). }
  pose proof (ox_sym_wire p ps T k proc F0u ov seed fixed r 1%nat e HP HT HN HL HF Hx Hl Hr Hi) as Hw.
  pose proof (eval_normalized fixed e) as En. rewrite W in En. rewrite En in Hw.
  apply (decomp2_sound fixed e v). rewrite <- Hw. cbn [eval_expr] in Hv. exact Hv.
Qed.

Definition fback2 (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (k:nat) : FS :=
  match nth_error ps k with
  | None => fs
  | Some proc =>
    let F0 := loc_facts T fs k (proc_roots proc) in
    match oxexec F0 fuel (nbfix (process_body proc)) [] with
    | None => fs
    | Some ov => add_facts fs (flat_map (back_one2 T k fs ov) (process_writers proc))
    end
  end.

Lemma fback2_sound p ps T fs k seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> SHold fixed fs ->
  SHold fixed (fback2 ps T (statement_fuel p) fs k).
Proof.
  intros HP HT HL HS. unfold fback2. destruct (nth_error ps k) as [proc|] eqn:HN; [|exact HS].
  destruct (oxexec (loc_facts T fs k (proc_roots proc)) (statement_fuel p) (nbfix (process_body proc)) []) as [ov|] eqn:Hx; [|exact HS].
  apply add_facts_hold; [exact HS|].
  intros e z HI. apply in_flat_map in HI as [r [_ HI]].
  exact (back_one2_sound p ps T k proc (plain_facts fs (proc_roots proc)) fs ov seed fixed r HP HT HN HL (plain_hold fixed fs _ HS) HS Hx e z HI).
Qed.

Definition frun2 (ps:list Process) (T:list (list nat)) (fuel:nat) (fs:FS) (sc:Script) : FS :=
  fold_left (fun (fs:FS) (st:bool*nat) => if fst st then fback2 ps T fuel fs (snd st) else fstep ps T fuel fs (snd st)) sc fs.

Lemma frun2_sound p ps T seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed ->
  forall sc fs, SHold fixed fs -> SHold fixed (frun2 ps T (statement_fuel p) fs sc).
Proof.
  intros HP HT HL. induction sc as [|[b k] t IH]; intros fs HS; cbn [frun2 fold_left]; [exact HS|].
  apply IH. destruct b; cbn [fst snd].
  - exact (fback2_sound p ps T fs k seed fixed HP HT HL HS).
  - exact (fstep_sound p ps T fs k seed fixed HP HT HL HS).
Qed.

(** shared-prefix cases over frun2 *)
Definition sh_store2 ps T fuel (sh:Shared) : FS := frun2 ps T fuel (add_facts fs_empty (sh_facts sh)) (sh_script sh).
Definition cs_store2 ps T fuel (s0:FS) (c:CaseF) : FS := frun2 ps T fuel (add_facts s0 (cf_facts c)) (cf_script c).
Definition check_shared2 ps T fuel (sh:Shared) (cs:list CaseF) : bool :=
  let s0 := sh_store2 ps T fuel sh in
  forallb (fun c => let fs := cs_store2 ps T fuel s0 c in outs_ok fs (cf_outs c) && exprs_ok fs (cf_exprs c)) cs.

Theorem shared2_sound p ps T sh cases seed fixed c :
  filter is_comb (processes p) = ps -> tab_okb ps T = true -> CombLFP p seed fixed ->
  check_shared2 ps T (statement_fuel p) sh cases = true -> In c cases -> FactsHold fixed (sh_facts sh) -> FactsHold fixed (cf_facts c) ->
  SHold fixed (cs_store2 ps T (statement_fuel p) (sh_store2 ps T (statement_fuel p) sh) c) /\ DecOut fixed (cf_outs c) /\ FactsHold fixed (cf_exprs c).
Proof.
  intros HP HT HL Hc Hin Hsh HF. unfold check_shared2 in Hc. fold (sh_store2 ps T (statement_fuel p) sh) in Hc.
  rewrite forallb_forall in Hc. specialize (Hc c Hin). apply andb_true_iff in Hc as [H1 H2].
  pose proof (frun2_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (sh_script sh) _ (shold_init fixed _ Hsh)) as H0.
  fold (sh_store2 ps T (statement_fuel p) sh) in H0.
  pose proof (frun2_sound p ps T seed fixed HP (tab_okb_sound ps T HT) HL (cf_script c) _ (add_facts_hold fixed _ _ H0 HF)) as HS.
  fold (cs_store2 ps T (statement_fuel p) (sh_store2 ps T (statement_fuel p) sh) c) in HS, H1, H2.
  exact (conj HS (conj (outs_ok_sound fixed _ _ HS H1) (exprs_ok_sound fixed _ _ HS H2))).
Qed.
End ExtendedSVFastCond.
Print Assumptions ExtendedSVFastCond.shared2_sound.
