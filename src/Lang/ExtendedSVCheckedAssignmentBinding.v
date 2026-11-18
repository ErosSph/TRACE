(** Checked ordered assignment equations at the original fixed point.
    Reuses the existing pivot/frame semantics, including expression inputs. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVAssignment
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot ExtendedSVCombConnection
 ExtendedSVCombCut ExtendedSVAssignment ExtendedSVExprAgreement ExtendedSVWordInvariant ListNotations.
Module ExtendedSVCheckedAssignmentBinding.
Definition assignment_bindingb ps index :=
 match nth_error ps index with
 |Some proc=>match process_body proc with
  |SAssign _ e(LVar w root)=>
   roots_unwrittenb root(skipn(S index)ps) &&
   forallb(fun wr=>roots_unwrittenb(snd wr)(firstn index ps) ||
     roots_unwrittenb(snd wr)(proc::skipn(S index)ps))(expr_inputs e)
  |_=>false end
 |None=>false end.
Theorem checked_assignment_binding p ps index proc nba e w root seed fixed :
 filter is_comb(processes p)=ps->nth_error ps index=Some proc->
 process_body proc=SAssign nba e(LVar w root)->assignment_bindingb ps index=true->
 (0<statement_fuel p)%nat->CombLFP p seed fixed->
 norm w(read_signal fixed root)=norm w(eval_expr fixed e).
Proof.
 intros HP HN HB HC HF HL.
 unfold assignment_bindingb in HC. rewrite HN,HB in HC.
 apply andb_true_iff in HC as[HO HI].
 pose proof(eq_trans HP(split_at ps index proc HN))as Horder.
 rewrite(actual_lfp_pivot_output p(firstn index ps)proc(skipn(S index)ps)root seed fixed Horder HO HL).
 rewrite(assignment_run_process p proc _ nba e(LVar w root)HB HF).
 unfold apply_update,resolve_update. cbn[resolve_lvalue update_signal update_offset update_width update_value].
 rewrite read_signal_write_same,norm_full_low_write,norm_idempotent.
 f_equal. apply eval_expr_agree. intros width r HR.
 pose proof(proj1(forallb_forall _ _)HI(width,r)HR)as HC.
 apply orb_true_iff in HC as[HC|HC].
 - rewrite(fold_run_process_preserves_root p(firstn index ps)r fixed(roots_unwrittenb_sound _ _ HC)). reflexivity.
 - rewrite(actual_lfp_pivot_input p(firstn index ps)proc(skipn(S index)ps)r seed fixed Horder HC HL). reflexivity.
Qed.
Print Assumptions checked_assignment_binding.
End ExtendedSVCheckedAssignmentBinding.
