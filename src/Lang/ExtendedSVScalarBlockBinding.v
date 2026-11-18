(** Ordered scalar-block output equations at the ORIGINAL combinational LFP.
    A proposed decomposition is checked as an all-state execution equality;
    local and global sampling/frame checks are independent Boolean facts. *)
From Coq Require Import List Bool ZArith Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVConstantRoot Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut
 Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement Lang.ExtendedSVWordInvariant.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot
 ExtendedSVCombConnection ExtendedSVCombCut ExtendedSVAssignment
 ExtendedSVExprAgreement ExtendedSVWordInvariant.
Module ExtendedSVScalarBlockBinding.

Definition scalar_fold_bindingb order index :=
 match nth_error order index with
 | Some proc => match process_body proc with
   | SAssign _ e (LVar _ root) =>
     roots_unwrittenb root (skipn (S index) order) &&
     forallb (fun wr => roots_unwrittenb (snd wr) (firstn index order)) (expr_inputs e)
   | _ => false end
 | None => false end.

Theorem checked_scalar_fold_binding p order index scalar nba e w root :
 nth_error order index=Some scalar ->
 process_body scalar=SAssign nba e (LVar w root) ->
 scalar_fold_bindingb order index=true -> (0<statement_fuel p)%nat -> forall s,
 norm w (read_signal (fold_left (run_process p) order s) root)=norm w (eval_expr s e).
Proof.
 intros HN HB HC HF s.
 unfold scalar_fold_bindingb in HC. rewrite HN,HB in HC.
 apply andb_true_iff in HC as [HO HI].
 rewrite (split_at order index scalar HN),fold_left_app. cbn [fold_left].
 rewrite (fold_run_process_preserves_root p (skipn (S index) order) root _
   (roots_unwrittenb_sound _ _ HO)).
 rewrite (assignment_run_process p scalar _ nba e (LVar w root) HB HF).
 unfold apply_update,resolve_update.
 cbn [resolve_lvalue update_signal update_offset update_width update_value].
 rewrite read_signal_write_same,norm_full_low_write,norm_idempotent.
 f_equal. apply eval_expr_agree. intros width r HR.
 pose proof (proj1 (forallb_forall _ _) HI (width,r) HR) as Hread.
 cbn [snd] in Hread.
 now rewrite (fold_run_process_preserves_root p (firstn index order) r s
   (roots_unwrittenb_sound _ _ Hread)).
Qed.

Definition scalar_block_bindingb ps process_index order scalar_index :=
 match nth_error ps process_index,nth_error order scalar_index with
 | Some proc,Some scalar => match process_body scalar with
   | SAssign _ e (LVar _ root) =>
     scalar_fold_bindingb order scalar_index &&
     roots_unwrittenb root (skipn (S process_index) ps) &&
     forallb (fun wr =>
       roots_unwrittenb (snd wr) (firstn process_index ps) ||
       roots_unwrittenb (snd wr) (proc::skipn (S process_index) ps)) (expr_inputs e)
   | _ => false end
 | _,_ => false end.

Theorem checked_scalar_block_binding p ps process_index proc order scalar_index
 scalar nba e w root seed fixed :
 filter is_comb (processes p)=ps -> nth_error ps process_index=Some proc ->
 nth_error order scalar_index=Some scalar ->
 process_body scalar=SAssign nba e (LVar w root) ->
 (forall s,run_process p s proc=fold_left (run_process p) order s) ->
 scalar_block_bindingb ps process_index order scalar_index=true ->
 (0<statement_fuel p)%nat -> CombLFP p seed fixed ->
 norm w (read_signal fixed root)=norm w (eval_expr fixed e).
Proof.
 intros HP Hproc Hscalar HB HD HC HF HL.
 unfold scalar_block_bindingb in HC. rewrite Hproc,Hscalar,HB in HC.
 apply andb_true_iff in HC as [HC HI]. apply andb_true_iff in HC as [Hlocal HO].
 pose proof (eq_trans HP (split_at ps process_index proc Hproc)) as Horder.
 rewrite (actual_lfp_pivot_output p (firstn process_index ps) proc
   (skipn (S process_index) ps) root seed fixed Horder HO HL).
 rewrite HD.
 rewrite (checked_scalar_fold_binding p order scalar_index scalar nba e w root
   Hscalar HB Hlocal HF).
 f_equal. apply eval_expr_agree. intros width r HR.
 pose proof (proj1 (forallb_forall _ _) HI (width,r) HR) as Hread.
 cbn [snd] in Hread. apply orb_true_iff in Hread as [Hread|Hread].
 - now rewrite (fold_run_process_preserves_root p (firstn process_index ps) r fixed
     (roots_unwrittenb_sound _ _ Hread)).
 - now rewrite (actual_lfp_pivot_input p (firstn process_index ps) proc
     (skipn (S process_index) ps) r seed fixed Horder Hread HL).
Qed.
End ExtendedSVScalarBlockBinding.
Print Assumptions ExtendedSVScalarBlockBinding.checked_scalar_fold_binding.
Print Assumptions ExtendedSVScalarBlockBinding.checked_scalar_block_binding.
