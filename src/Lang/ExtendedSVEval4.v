(** 1-bit OR short-circuit on top of Eval3 (template route, additive; 2026-11-04).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    [simp4] = [ExtendedSVEval3.simp_f] plus: a 1-bit [a | b] with a side that simplifies to the constant 1 is the constant 1 (xeval2/xeval3 only
    short-circuit [&] with a 0 side).  [xeval4], [ox_new_facts4] (forward derived constants of a comb process with the stronger evaluator). *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymExecSym Lang.ExtendedSVExpressionFold
 Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVBackward Lang.ExtendedSVEval3.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymExecSym ExtendedSVExpressionFold ExtendedSVSymExecOverlay ExtendedSVBackward ExtendedSVEval3.
Local Open Scope Z_scope.
Module ExtendedSVEval4.
Definition ones1 (e:Expr) : bool := match e with EConst 1%nat c => Z.eqb (norm 1 c) 1 | _ => false end.
Lemma ones1_eval s e : ones1 e = true -> eval_expr s e = 1.
Proof. destruct e; cbn [ones1]; try discriminate. destruct width as [|[|w]]; try discriminate. intro H. apply Z.eqb_eq in H. cbn [eval_expr]. exact H. Qed.

Fixpoint simp4 (F:Facts) (e:Expr) : Expr :=
 match xeval2 F e with
 | Some z => EConst (expr_width e) z
 | None =>
   match e with
   | ESel w a b => ESel w (simp4 F a) (simp4 F b)
   | EConcat w a b => EConcat w (simp4 F a) (simp4 F b)
   | EReplicate w c a => EReplicate w c (simp4 F a)
   | EExtend w sg a => EExtend w sg (simp4 F a)
   | EUnary w op a => EUnary w op (simp4 F a)
   | EBinary w BAnd a b =>
       let a' := simp4 F a in let b' := simp4 F b in
       if zero_expressionb a' || zero_expressionb b' then EConst w 0 else EBinary w BAnd a' b'
   | EBinary w BOr a b =>
       let a' := simp4 F a in let b' := simp4 F b in
       if Nat.eqb w 1 && Nat.eqb (expr_width a) 1 && Nat.eqb (expr_width b) 1 && (ones1 a' || ones1 b') then EConst 1%nat 1 else EBinary w BOr a' b'
   | EBinary w op a b => EBinary w op (simp4 F a) (simp4 F b)
   | ECond w g y n => ECond w (simp4 F g) (simp4 F y) (simp4 F n)
   | _ => e
   end
 end.

Lemma simp4_width F : forall e, expr_width (simp4 F e) = expr_width e.
Proof.
 induction e; cbn [simp4]; match goal with |- context [xeval2 F ?x] => destruct (xeval2 F x) as [z|] end; try reflexivity.
 destruct op; cbn [expr_width]; try reflexivity.
 - destruct (zero_expressionb (simp4 F e1) || zero_expressionb (simp4 F e2)); reflexivity.
 - destruct (Nat.eqb width 1 && Nat.eqb (expr_width e1) 1 && Nat.eqb (expr_width e2) 1 && (ones1 (simp4 F e1) || ones1 (simp4 F e2))) eqn:C;
     [|reflexivity].
   apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C _]. apply Nat.eqb_eq in C. cbn [expr_width]. lia.
Qed.

Lemma const_case4 s e z : eval_expr s e = z -> eval_expr s (EConst (expr_width e) z) = eval_expr s e.
Proof. intro H. cbn [eval_expr]. rewrite <- H at 1. apply eval_normalized. Qed.

Lemma simp4_sound F s (HF : FactsHold s F) : forall e, eval_expr s (simp4 F e) = eval_expr s e.
Proof.
 induction e; cbn [simp4]; match goal with |- context [xeval2 F ?x] => let Hx := fresh "Hx" in destruct (xeval2 F x) as [z|] eqn:Hx end.
 all: try (exact (const_case4 s _ _ (xeval2_sound F s HF _ _ Hx))).
 - reflexivity.
 - reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2, simp4_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe, simp4_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe, simp4_width. reflexivity.
 - cbn [eval_expr]. rewrite IHe. reflexivity.
 - destruct op; try (cbn [eval_expr]; rewrite IHe1, IHe2, ?simp4_width; reflexivity).
   destruct (zero_expressionb (simp4 F e1) || zero_expressionb (simp4 F e2)) eqn:Hz.
   + apply orb_true_iff in Hz as [Hz|Hz].
     * rewrite (zero_expression_sound _ s Hz) in IHe1. cbn [eval_expr]. rewrite <- IHe1. rewrite Z.land_0_l. reflexivity.
     * rewrite (zero_expression_sound _ s Hz) in IHe2. cbn [eval_expr]. rewrite <- IHe2. rewrite Z.land_0_r. reflexivity.
   + cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
   + destruct (Nat.eqb width 1 && Nat.eqb (expr_width e1) 1 && Nat.eqb (expr_width e2) 1 && (ones1 (simp4 F e1) || ones1 (simp4 F e2))) eqn:C.
     * apply andb_true_iff in C as [C Hones]. apply andb_true_iff in C as [C W2]. apply andb_true_iff in C as [C W1]. apply Nat.eqb_eq in C. subst width.
       apply Nat.eqb_eq in W1. apply Nat.eqb_eq in W2.
       destruct (eval_bit s e1 W1) as [X|X]; destruct (eval_bit s e2 W2) as [Y|Y]; cbn [eval_expr];
         apply orb_true_iff in Hones as [Ho|Ho]; pose proof (ones1_eval s _ Ho) as Hv; rewrite ?IHe1, ?IHe2 in Hv; rewrite ?X, ?Y in *;
         first [ exfalso; lia | (vm_compute; reflexivity) | (vm_compute in Hv; try discriminate Hv; vm_compute; reflexivity) ].
     * cbn [eval_expr]. rewrite IHe1, IHe2. reflexivity.
 - cbn [eval_expr]. rewrite IHe1, IHe2, IHe3. reflexivity.
Qed.

Definition xeval4 (F:Facts) (e:Expr) : option Z := xeval2 F (simp4 F e).
Lemma xeval4_sound F s (HF : FactsHold s F) e z : xeval4 F e = Some z -> eval_expr s e = z.
Proof. unfold xeval4. intro H. rewrite <- (simp4_sound F s HF e). exact (xeval2_sound F s HF _ _ H). Qed.


Definition ox_new_facts4 (F0:Facts) (T:list (list nat)) (k:nat) (ov:SOv) : Facts :=
 flat_map (fun r => match sov_lookup ov r with
   | Some (w,e) => if wr_lt T r (S k) && inputs_okb T k e then
        match xeval4 F0 e with Some z => [(EVar w r, norm w z)] | None => [] end else []
   | None => [] end) (map fst ov).

Lemma ox_new_facts4_sound p ps T k proc F0 ov seed fixed :
 filter is_comb (processes p) = ps -> TabC ps T -> nth_error ps k = Some proc ->
 facts_inputs_okb F0 T k = true -> FactsHold fixed F0 -> CombLFP p seed fixed ->
 oxexec F0 (statement_fuel p) (nbfix (process_body proc)) [] = Some ov ->
 FactsHold fixed (ox_new_facts4 F0 T k ov).
Proof.
 intros HP HT HN Hok HF HL Hx e0 z0 HI. unfold ox_new_facts4 in HI. apply in_flat_map in HI as [r [Hr HI]].
 destruct (sov_lookup ov r) as [[w e]|] eqn:Hl; [|contradiction].
 destruct (wr_lt T r (S k) && inputs_okb T k e) eqn:Hc; [|contradiction].
 apply andb_true_iff in Hc as [Hc1 Hc2].
 destruct (xeval4 F0 e) as [z|] eqn:Hxe; [|contradiction].
 destruct HI as [HI|[]]. inversion HI; subst e0 z0. cbn [eval_expr].
 rewrite (oxrun_comb_lfp p ps T k proc F0 ov seed fixed HP HT HN Hok HF HL Hx r w e Hl Hc1 Hc2).
 rewrite (xeval4_sound F0 fixed HF e z Hxe). reflexivity.
Qed.
End ExtendedSVEval4.
Print Assumptions ExtendedSVEval4.ox_new_facts4_sound.
