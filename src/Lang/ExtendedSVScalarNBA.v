(** Scalar NBA projection with an opaque arbitrary execution prefix.
    Full-width LVar preserves high bits in the unbounded State representation;
    consequently this interface states a normalized projection. *)
From Coq Require Import ZArith List Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVWordInvariant Lang.ExtendedSVBitSlice Lang.ExtendedSVProcessSlice.
Import ExtendedSV ExtendedSVRootProjection ExtendedSVWordInvariant ExtendedSVBitSlice ExtendedSVProcessSlice ListNotations.
Module ExtendedSVScalarNBA.
Lemma scalar_slice_normalized old width value :
 norm width(write_slice old 0 (Z.of_nat width)value)=norm width value.
Proof.
 pose proof(read_slice_write_same old 0 (Z.of_nat width)value ltac:(lia) ltac:(lia)) as H.
 unfold read_slice in H. rewrite !Z.shiftr_0_r in H. exact H.
Qed.
Theorem scalar_nba_emitted_projection fuel es rhs width root value :
 norm width(apply_updates_root_value root value(emitted_updates
  (exec_stmt(S fuel)(SAssign true rhs(LVar width root))es)))=
 norm width(eval_expr(blocking_state es)rhs).
Proof.
 cbn[exec_stmt emitted_updates]. rewrite apply_root_app.
 cbn[apply_updates_root_value]. unfold apply_update_root_value,resolve_update.
 cbn[resolve_lvalue update_signal update_offset update_width update_value].
 rewrite Nat.eqb_refl,scalar_slice_normalized,norm_idempotent. reflexivity.
Qed.
End ExtendedSVScalarNBA.
Print Assumptions ExtendedSVScalarNBA.scalar_nba_emitted_projection.
