(** Lift a proved whole-process output expression to the original LFP.
    Local execution and global sampling are separate checked obligations. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVExprAgreement.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVExprAgreement.
Module ExtendedSVExpressionBinding.

Definition expression_bindingb ps index root expression :=
 match nth_error ps index with
 | None => false
 | Some proc => roots_unwrittenb root (skipn (S index) ps) &&
   forallb (fun wr => roots_unwrittenb (snd wr) (firstn index ps) ||
     roots_unwrittenb (snd wr) (proc::skipn (S index) ps)) (expr_inputs expression)
 end.

Theorem checked_expression_binding p ps index proc width root expression seed fixed:
 filter is_comb(processes p)=ps -> nth_error ps index=Some proc ->
 (forall s,norm width(read_signal(run_process p s proc)root)=norm width(eval_expr s expression)) ->
 expression_bindingb ps index root expression=true -> CombLFP p seed fixed ->
 norm width(read_signal fixed root)=norm width(eval_expr fixed expression).
Proof.
 intros HP HN HE HC HL.
 unfold expression_bindingb in HC. rewrite HN in HC.
 apply andb_true_iff in HC as[HO HI].
 pose proof(eq_trans HP(split_at ps index proc HN))as Horder.
 rewrite(actual_lfp_pivot_output p(firstn index ps)proc(skipn(S index)ps)root seed fixed Horder HO HL).
 rewrite HE. f_equal. apply eval_expr_agree. intros w r HR.
 pose proof(proj1(forallb_forall _ _)HI(w,r)HR)as Hread.
 cbn[snd]in Hread. apply orb_true_iff in Hread as[Hread|Hread].
 - now rewrite(fold_run_process_preserves_root p(firstn index ps)r fixed
     (roots_unwrittenb_sound _ _ Hread)).
 - now rewrite(actual_lfp_pivot_input p(firstn index ps)proc(skipn(S index)ps)r seed fixed Horder Hread HL).
Qed.
End ExtendedSVExpressionBinding.
Print Assumptions ExtendedSVExpressionBinding.checked_expression_binding.
