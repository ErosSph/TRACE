(** Ordered constant-writer certificates. Preserve the original comb order:
    later writers must be excluded, earlier writers need no restriction.
    [view] permits the actual port width normalization instead of silently
    assuming every raw state cell is already well formatted. *)
From Coq Require Import List Bool ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection.
Import ListNotations ExtendedSV ExtendedSVRootProjection.
Module ExtendedSVConstantRoot.
Definition roots_unwrittenb root order := forallb
 (fun proc => negb (existsb (Nat.eqb root) (process_writers proc))) order.
Lemma roots_unwrittenb_sound root order : roots_unwrittenb root order=true ->
 forall proc, In proc order -> ~ In root (process_writers proc).
Proof.
 intros H proc Hin Hwriter. unfold roots_unwrittenb in H.
 apply forallb_forall with (x:=proc) in H;[|exact Hin].
 apply Bool.negb_true_iff in H.
 assert (E:existsb (Nat.eqb root) (process_writers proc)=true).
 { apply existsb_exists. exists root. split;[exact Hwriter|apply Nat.eqb_refl]. }
 rewrite H in E. discriminate.
Qed.

Theorem ordered_comb_constant_root {A : Type} p prefix pivot suffix root
 (view : Z -> A) value :
 filter is_comb (processes p)=prefix++pivot::suffix ->
 roots_unwrittenb root suffix=true ->
 (forall s, view (read_signal (run_process p s pivot) root)=value) ->
 forall s, view (read_signal (comb_round p s) root)=value.
Proof.
 intros Horder Hsuffix Hpivot s. unfold comb_round. rewrite Horder,fold_left_app.
 cbn [fold_left]. rewrite fold_run_process_preserves_root.
 - apply Hpivot.
 - exact (roots_unwrittenb_sound root suffix Hsuffix).
Qed.

Theorem actual_lfp_constant_root {A : Type} p root (view : Z -> A) value :
 (forall s, view (read_signal (comb_round p s) root)=value) ->
 forall seed fixed, CombLFP p seed fixed -> view (read_signal fixed root)=value.
Proof.
 intros Hround seed fixed Hlfp. destruct Hlfp as [n fixed Hiter Hfixed].
 rewrite <-Hfixed. apply Hround.
Qed.
End ExtendedSVConstantRoot.
Print Assumptions ExtendedSVConstantRoot.ordered_comb_constant_root.
Print Assumptions ExtendedSVConstantRoot.actual_lfp_constant_root.
