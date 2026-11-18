(** Multi-output observations at the ORIGINAL blocking process and LFP.
    All observed roots and retained input paths have checked frame conditions. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot
 Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut Lang.ExtendedSVExprAgreement
 Lang.ExtendedSVBlocking Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVBlockingObservation.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot ExtendedSVCombConnection
 ExtendedSVCombCut ExtendedSVExprAgreement ExtendedSVBlocking ExtendedSVAutoAdapterEffects ExtendedSVBlockingObservation.
Module ExtendedSVExpressionObservation.
Theorem actual_process_expression p proc plan width post before:
 blocking_onlyb(process_body proc)=true ->
 compile_effect(statement_fuel p)(process_body proc)=Some plan ->
 Observes plan width post before ->forall s,
 norm width(eval_expr(run_process p s proc)post)=norm width(eval_expr s before).
Proof.
 intros HB HC HO s;rewrite(blocking_run_process p proc s HB),(compile_effect_sound _ _ _ _ HC).
 exact(HO(initial_exec s)).
Qed.
Definition observation_bindingb ps index post before:=match nth_error ps index with
 |None=>false
 |Some proc=>
 forallb(fun wr=>roots_unwrittenb(snd wr)(skipn(S index)ps))(expr_inputs post)&&
 forallb(fun wr=>roots_unwrittenb(snd wr)(firstn index ps)||
   roots_unwrittenb(snd wr)(proc::skipn(S index)ps))(expr_inputs before)
 end.
Theorem checked_observation_binding p ps index proc width post before seed fixed:
 filter is_comb(processes p)=ps ->nth_error ps index=Some proc ->
 (forall s,norm width(eval_expr(run_process p s proc)post)=norm width(eval_expr s before)) ->
 observation_bindingb ps index post before=true ->CombLFP p seed fixed ->
 norm width(eval_expr fixed post)=norm width(eval_expr fixed before).
Proof.
 intros HP HN HE HC HL;unfold observation_bindingb in HC;rewrite HN in HC.
 apply andb_true_iff in HC as[HOut HIn].
 pose proof(eq_trans HP(split_at ps index proc HN))as HOrder.
 assert(HO:norm width(eval_expr fixed post)=
 norm width(eval_expr(run_process p(fold_left(run_process p)(firstn index ps)fixed)proc)post)).
 { f_equal;apply eval_expr_agree;intros w r HI.
   pose proof(proj1(forallb_forall _ _)HOut(w,r)HI)as HS;cbn[snd]in HS.
   exact(f_equal(norm w)(actual_lfp_pivot_output p(firstn index ps)proc(skipn(S index)ps)r seed fixed HOrder HS HL)). }
 etransitivity;[exact HO|];rewrite HE;f_equal;apply eval_expr_agree;intros w r HI.
 pose proof(proj1(forallb_forall _ _)HIn(w,r)HI)as HR;cbn[snd]in HR.
 apply orb_true_iff in HR as[HR|HR].
 - exact(f_equal(norm w)(fold_run_process_preserves_root p(firstn index ps)r fixed(roots_unwrittenb_sound _ _ HR))).
 - exact(f_equal(norm w)(actual_lfp_pivot_input p(firstn index ps)proc(skipn(S index)ps)r seed fixed HOrder HR HL)).
Qed.
End ExtendedSVExpressionObservation.
Print Assumptions ExtendedSVExpressionObservation.actual_process_expression.
Print Assumptions ExtendedSVExpressionObservation.checked_observation_binding.
