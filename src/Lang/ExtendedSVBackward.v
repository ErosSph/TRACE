(** Backward fact propagation through the combinational cone (template route, additive; 2026-11-03).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    From a known value of a 1-bit wire (e.g. [id_valid_o = 1]) the wire expression of its comb process ([sx_wire], symbolic) is
    decomposed: [a & b = 1] gives [a = 1, b = 1]; [a | b = 0] gives [a = 0, b = 0]; [~a = v] gives [a = 1-v]; any other node is kept as
    an expression fact [(e, v)] (checked later by xeval2 / the case-expression check).  A SCRIPT interleaves forward steps
    ([sx_step], constants) and backward steps; both are sound at a comb fixed point, so any script is sound and the generator
    only records the productive steps. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecPhase Lang.ExtendedSVExpressionFold.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVSymExecPhase ExtendedSVExpressionFold.
Local Open Scope Z_scope.
Module ExtendedSVBackward.

Fixpoint decomp (v:Z) (e:Expr) : Facts :=
  match e with
  | EBinary 1%nat BAnd a b =>
      if Z.eqb v 1 && Nat.eqb (expr_width a) 1 && Nat.eqb (expr_width b) 1 then decomp 1 a ++ decomp 1 b else [(e, v)]
  | EBinary 1%nat BOr a b =>
      if Z.eqb v 0 && Nat.eqb (expr_width a) 1 && Nat.eqb (expr_width b) 1 then decomp 0 a ++ decomp 0 b else [(e, v)]
  | EUnary 1%nat UNot a =>
      if (Z.eqb v 0 || Z.eqb v 1) && Nat.eqb (expr_width a) 1 then decomp (1 - v) a else [(e, v)]
  | _ => [(e, v)]
  end.

Lemma bit01 x : norm 1 x = x -> x = 0 \/ x = 1.
Proof.
  unfold norm, mask. intro H. rewrite Z.sub_1_r, <- Z.ones_equiv, Z.land_ones in H by lia.
  change (2 ^ Z.of_nat 1) with 2 in H. pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

Lemma eval_bit s e : expr_width e = 1%nat -> eval_expr s e = 0 \/ eval_expr s e = 1.
Proof. intro W. pose proof (eval_normalized s e) as H. rewrite W in H. exact (bit01 _ H). Qed.

Lemma decomp_sound s : forall e v, eval_expr s e = v -> FactsHold s (decomp v e).
Proof.
  induction e as [wc vc | wv xv | ws bs ls Ib1 Ib2 | wcc hc lc Ic1 Ic2 | wr cr br Ir | wex sgn bex Iex | wu opu e IHe | wb opb e1 IHe1 e2 IHe2 | wq gq yq nq Iq1 Iq2 Iq3]; intros v H; cbn [decomp].
  1-6,9: (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
  - (* unary *)
    destruct wu as [|[|w]]; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct opu; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct ((Z.eqb v 0 || Z.eqb v 1) && Nat.eqb (expr_width e) 1) eqn:C;
      [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
    apply andb_true_iff in C as [C W]. apply Nat.eqb_eq in W.
    cbn [eval_expr] in H.
    destruct (eval_bit s e W) as [X|X]; rewrite X in H; vm_compute in H; subst v;
      [apply (IHe 0 X) | apply (IHe 1 X)].
  - (* binary *)
    destruct wb as [|[|w]]; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    destruct opb; try (intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H).
    + (* and *)
      destruct (Z.eqb v 1 && Nat.eqb (expr_width e1) 1 && Nat.eqb (expr_width e2) 1) eqn:C;
        [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
      apply andb_true_iff in C as [C W2]. apply andb_true_iff in C as [C W1].
      apply Z.eqb_eq in C. apply Nat.eqb_eq in W1. apply Nat.eqb_eq in W2. rewrite C in H.
      cbn [eval_expr] in H.
      destruct (eval_bit s e1 W1) as [X|X]; destruct (eval_bit s e2 W2) as [Y|Y]; rewrite X, Y in H; try (vm_compute in H; discriminate H).
      intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHe1 1 X e0 z0 HI) | exact (IHe2 1 Y e0 z0 HI)].
    + (* or *)
      destruct (Z.eqb v 0 && Nat.eqb (expr_width e1) 1 && Nat.eqb (expr_width e2) 1) eqn:C;
        [|intros e0 z0 HI; cbn in HI; destruct HI as [HI|[]]; injection HI as <- <-; exact H].
      apply andb_true_iff in C as [C W2]. apply andb_true_iff in C as [C W1].
      apply Z.eqb_eq in C. apply Nat.eqb_eq in W1. apply Nat.eqb_eq in W2. rewrite C in H.
      cbn [eval_expr] in H.
      destruct (eval_bit s e1 W1) as [X|X]; destruct (eval_bit s e2 W2) as [Y|Y]; rewrite X, Y in H; try (vm_compute in H; discriminate H).
      intros e0 z0 HI. apply in_app_or in HI as [HI|HI]; [exact (IHe1 0 X e0 z0 HI) | exact (IHe2 0 Y e0 z0 HI)].
Qed.

(** one backward step at the comb position [k] for the root [r]: uses the known value of [r] *)
Definition back_wire (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) (r:signal) : Facts :=
  match fact_find F (EVar 1%nat r) with
  | None => []
  | Some v =>
    match sx_wire ps fuel T F k r with
    | Some (1%nat, e) => if Nat.eqb (expr_width e) 1 && inputs_okb T k e then decomp v e else []
    | _ => []
    end
  end.

Lemma back_wire_sound p ps T seed fixed F k r :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
  FactsHold fixed (back_wire ps T (statement_fuel p) F k r).
Proof.
  intros HP HT HL HF. unfold back_wire.
  destruct (fact_find F (EVar 1%nat r)) as [v|] eqn:Hf; [|intros e z HI; destruct HI].
  destruct (sx_wire ps (statement_fuel p) T F k r) as [[w e]|] eqn:Hs; [|intros e0 z HI; destruct HI].
  destruct w as [|[|w]]; try (intros e0 z HI; destruct HI).
  destruct (Nat.eqb (expr_width e) 1 && inputs_okb T k e) eqn:C; [|intros e0 z HI; destruct HI].
  apply andb_true_iff in C as [W Hi]. apply Nat.eqb_eq in W.
  pose proof (fact_find_sound _ _ _ fixed HF Hf) as Hv. cbn [eval_expr] in Hv.
  pose proof (sym_wire_c p ps T k F seed fixed r 1%nat e HP HT HL HF Hs Hi) as Hw.
  pose proof (eval_normalized fixed e) as En. rewrite W in En. rewrite En in Hw.
  apply (decomp_sound fixed e v). rewrite <- Hw. exact Hv.
Qed.

Definition back_pos (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (k:nat) : Facts :=
  match nth_error ps k with
  | None => F
  | Some proc => F ++ flat_map (back_wire ps T fuel F k) (process_writers proc)
  end.

Lemma back_pos_sound p ps T seed fixed F k :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed -> FactsHold fixed F ->
  FactsHold fixed (back_pos ps T (statement_fuel p) F k).
Proof.
  intros HP HT HL HF. unfold back_pos. destruct (nth_error ps k) as [proc|]; [|exact HF].
  intros e z HI. apply in_app_or in HI as [HI|HI]; [apply HF, HI|].
  apply in_flat_map in HI as [r [_ HI]].
  exact (back_wire_sound p ps T seed fixed F k r HP HT HL HF e z HI).
Qed.

(** scripts: [(false,k)] forward step at k, [(true,k)] backward step at k *)
Definition Script := list (bool * nat).
Fixpoint run_script (ps:list Process) (T:list (list nat)) (fuel:nat) (F:Facts) (sc:Script) : Facts :=
  match sc with
  | [] => F
  | (b,k)::t => run_script ps T fuel (if b then back_pos ps T fuel F k else sx_step ps T fuel F k) t
  end.

Lemma run_script_sound p ps T seed fixed :
  filter is_comb (processes p) = ps -> TabC ps T -> CombLFP p seed fixed ->
  forall sc F, FactsHold fixed F -> FactsHold fixed (run_script ps T (statement_fuel p) F sc).
Proof.
  intros HP HT HL. induction sc as [|[b k] t IH]; intros F HF; cbn [run_script]; [exact HF|].
  apply IH. destruct b.
  - exact (back_pos_sound p ps T seed fixed F k HP HT HL HF).
  - exact (sx_step_sound p ps T (statement_fuel p) F k seed fixed HP HT eq_refl HF HL).
Qed.
End ExtendedSVBackward.
Print Assumptions ExtendedSVBackward.run_script_sound.
