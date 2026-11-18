(** Actual scalar producer idempotence without a Word/State-length assumption.
    Old high bits are retained by the ORIGINAL write_slice; overwrite algebra
    proves the second real run is identical. No trace/CPU output is substituted. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVAssignment Lang.ExtendedSVExprAgreement Lang.ExtendedSVCombIdempotence.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVAssignment
 ExtendedSVExprAgreement ExtendedSVCombIdempotence ListNotations.
Module ExtendedSVProducerAssignment.
Definition NoInputRoot root expr:=forall rw,In rw(expr_inputs expr)->snd rw<>root.
Definition no_input_rootb root expr :=
 forallb (fun rw=>negb(Nat.eqb(snd rw)root))(expr_inputs expr).
Lemma no_input_rootb_sound root expr:
 no_input_rootb root expr=true->NoInputRoot root expr.
Proof.
 intros H rw Hin. unfold no_input_rootb in H.
 apply forallb_forall with(x:=rw)in H;[|exact Hin].
 apply Bool.negb_true_iff in H. now apply Nat.eqb_neq.
Qed.
Lemma invisible_update_keeps_expression update expr state:
 NoInputRoot(update_signal update)expr->eval_expr(apply_update state update)expr=eval_expr state expr.
Proof.
 intro H. apply eval_expr_agree. intros width root Hin.
 rewrite read_signal_apply_update_other;[reflexivity|].
 intro E. apply(H(width,root)Hin). cbn. symmetry. exact E.
Qed.
Lemma identical_update_is_idempotent update state:
 apply_update(apply_update state update)update=apply_update state update.
Proof.
 destruct update as[root offset width value]. unfold apply_update.
 cbn[update_signal update_offset update_width update_value].
 rewrite read_signal_write_same,write_slice_overwrite,write_signal_write_same. reflexivity.
Qed.
Theorem actual_scalar_assignment_producer_idempotent p proc width root expr nba:
 process_body proc=SAssign nba expr(LVar width root)->
 (0<statement_fuel p)%nat->NoInputRoot root expr->ProducerIdempotent p proc.
Proof.
 intros Hbody Hfuel Hread state.
 rewrite !assignment_run_process with(nba:=nba)(rhs:=expr)(lhs:=LVar width root)by assumption.
 assert(Hvalue:eval_expr(apply_update state(resolve_update state(LVar width root)(eval_expr state expr)))expr=
 eval_expr state expr).
 { apply invisible_update_keeps_expression. cbn[resolve_update resolve_lvalue update_signal]. exact Hread. }
 cbn[resolve_update resolve_lvalue]in Hvalue|-*. rewrite Hvalue.
 apply identical_update_is_idempotent.
Qed.
Definition scalar_producerb proc :=match process_body proc with
 |SAssign _ expr(LVar _ root)=>no_input_rootb root expr
 |_=>false end.
Theorem scalar_producerb_sound p proc:
 (0<statement_fuel p)%nat->scalar_producerb proc=true->ProducerIdempotent p proc.
Proof.
 intros HF HC. destruct proc as[k ev body line].
 destruct body as[|nba expr lhs|ss|g y n|e arms];try discriminate.
 destruct lhs;try discriminate.
 eapply actual_scalar_assignment_producer_idempotent;
 [reflexivity|exact HF|]. now apply no_input_rootb_sound.
Qed.
End ExtendedSVProducerAssignment.
Print Assumptions ExtendedSVProducerAssignment.actual_scalar_assignment_producer_idempotent.
