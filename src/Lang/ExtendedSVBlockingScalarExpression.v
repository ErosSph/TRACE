(** Reuse the sampled scalar compiler for blocking logic only after checking
    that the retained inputs are not written by that logic. *)
From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVBlockingSnapshot Lang.ExtendedSVScalarExpression
 Lang.ExtendedSVAutoAdapterPlan Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVBlocking Lang.ExtendedSVWordInvariant.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVBlockingSnapshot
 ExtendedSVScalarExpression ExtendedSVAutoAdapterPlan ExtendedSVAutoAdapterEffects
 ExtendedSVBlocking ExtendedSVWordInvariant.
Module ExtendedSVBlockingScalarExpression.

Theorem checked_blocking_scalar_process p proc plan inputs root width
 snapshot_fuel expression_fuel expression :
 blocking_onlyb (process_body proc) = true ->
 compile_effect (statement_fuel p) (process_body proc) =
   Some (snapshot_effect snapshot_fuel plan) ->
 snapshot_safe snapshot_fuel inputs plan = true ->
 compile_scalar expression_fuel root width plan (EVar width root) =
   Some expression ->
 forall s, norm width (read_signal (run_process p s proc) root) =
   norm width (eval_expr s expression).
Proof.
 intros HB HC HS HE s.
 rewrite (actual_snapshot_process p proc snapshot_fuel inputs plan HB HC HS s).
 rewrite read_signal_apply_updates.
 eapply compile_scalar_sound; [exact HE|].
 cbn [eval_expr]. now rewrite norm_idempotent.
Qed.
End ExtendedSVBlockingScalarExpression.
Print Assumptions ExtendedSVBlockingScalarExpression.checked_blocking_scalar_process.
