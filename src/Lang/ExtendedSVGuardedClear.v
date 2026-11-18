From Coq Require Import List ZArith Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVBlockingObservation Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVCombConnection Lang.ExtendedSVExprAgreement Lang.ExtendedSVConstantRoot Lang.ExtendedSVBlocking.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects
 ExtendedSVBlockingObservation ExtendedSVWordInvariant
 ExtendedSVCombConnection ExtendedSVExprAgreement ExtendedSVConstantRoot ExtendedSVBlocking.
Module ExtendedSVGuardedClear.

Definition Clears plan width root guard:=forall es,
 norm 1(eval_expr(blocking_state(eval_effect plan es))guard)<>0%Z ->
 norm width(read_signal(blocking_state(eval_effect plan es))root)=0%Z.

Inductive Frame(e:Expr):EffectPlan->Prop:=
| FrameEmpty:Frame e FEmpty
| FrameAssign:forall w r rhs,reads_unwrittenb r e=true ->Frame e(FAssign false rhs(LVar w r))
| FrameNil:Frame e(FSeq [])
| FrameCons:forall p ps,Frame e p ->Frame e(FSeq ps) ->Frame e(FSeq(p::ps))
| FrameIf:forall g y n,Frame e y ->Frame e n ->Frame e(FIf g y n).

Lemma frame_observes e p:Frame e p ->forall width,Observes p width e e.
Proof.
 intro H;induction H as[|w r rhs HC| |p ps HP IHP HT IHT|g y n HY IHY HN IHN];intro width.
 - apply empty.
 - now apply assignment_unread_checked.
 - apply seq_nil.
 - eapply seq_cons;[apply IHT|apply IHP].
 - intros es;cbn[eval_effect];destruct(Z.eqb(eval_expr(blocking_state es)g)0);[apply IHN|apply IHY].
Qed.

Lemma guard_clears width root guard yes:
 Observes yes width(EVar width root)(EConst width 0) ->
 Clears(FIf guard yes FEmpty)width root guard.
Proof.
 intros HO es HG;cbn[eval_effect]in HG|-*.
 destruct(Z.eqb(eval_expr(blocking_state es)guard)0)eqn:HE.
 - cbn[eval_effect]in HG;apply Z.eqb_eq in HE;rewrite HE in HG;unfold norm in HG;rewrite Z.land_0_l in HG;contradiction.
 - specialize(HO es);cbn[eval_expr]in HO;repeat rewrite norm_idempotent in HO.
   rewrite HO;unfold norm;apply Z.land_0_l.
Qed.

Lemma after_frame p suffix width root guard:
 Clears p width root guard ->Frame(EVar width root)(FSeq suffix) ->Frame guard(FSeq suffix) ->
 Clears(FSeq(p::suffix))width root guard.
Proof.
 intros HC HR HG es H;cbn[eval_effect fold_left]in H|-*.
 change(norm 1(eval_expr(blocking_state(eval_effect(FSeq suffix)(eval_effect p es)))guard)<>0%Z)in H.
 rewrite(frame_observes _ _ HG 1)in H.
 pose proof(frame_observes _ _ HR width(eval_effect p es))as HF.
 cbn[eval_expr]in HF;repeat rewrite norm_idempotent in HF.
 change(norm width(read_signal(blocking_state(eval_effect(FSeq suffix)(eval_effect p es)))root)=0%Z).
 rewrite HF;now apply HC.
Qed.

Lemma arbitrary_prefix prefix suffix width root guard:
 Clears(FSeq suffix)width root guard ->Clears(FSeq(prefix++suffix))width root guard.
Proof. intros H es;cbn[eval_effect];rewrite fold_left_app;apply(H(fold_left(fun s p=>eval_effect p s)prefix es)). Qed.

Lemma singleton_clear plan width root guard:
 Clears plan width root guard ->Clears(FSeq[plan])width root guard.
Proof. intros H es;cbn[eval_effect fold_left];apply H. Qed.

Theorem process_of_clear p proc plan width root guard:
 blocking_onlyb(process_body proc)=true ->
 compile_effect(statement_fuel p)(process_body proc)=Some plan ->
 Clears plan width root guard ->forall s,
 norm 1(eval_expr(run_process p s proc)guard)<>0%Z ->
 norm width(read_signal(run_process p s proc)root)=0%Z.
Proof.
 intros HB HC HP s;rewrite blocking_run_process by exact HB.
 rewrite(compile_effect_sound _ _ _ _ HC);apply HP.
Qed.

Theorem actual_lfp_clear p prefix proc suffix width root guard seed fixed:
 filter is_comb(processes p)=prefix++proc::suffix ->
 roots_unwrittenb root suffix=true ->
 forallb(fun wr=>roots_unwrittenb(snd wr)suffix)(expr_inputs guard)=true ->
 (forall s,norm 1(eval_expr(run_process p s proc)guard)<>0%Z ->
   norm width(read_signal(run_process p s proc)root)=0%Z) ->
 CombLFP p seed fixed ->norm 1(eval_expr fixed guard)<>0%Z ->norm width(read_signal fixed root)=0%Z.
Proof.
 intros HP HR HG HC HL HH.
 rewrite(actual_lfp_pivot_output p prefix proc suffix root seed fixed HP HR HL).
 apply HC.
 assert(HE:eval_expr fixed guard=eval_expr(run_process p(fold_left(run_process p)prefix fixed)proc)guard).
 { apply eval_expr_agree;intros w x HI.
   pose proof(proj1(forallb_forall _ _)HG(w,x)HI)as HX.
   exact(f_equal(norm w)(actual_lfp_pivot_output p prefix proc suffix x seed fixed HP HX HL)). }
 rewrite <- HE;exact HH.
Qed.
End ExtendedSVGuardedClear.
Print Assumptions ExtendedSVGuardedClear.arbitrary_prefix.
Print Assumptions ExtendedSVGuardedClear.guard_clears.
