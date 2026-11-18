(** Exact ordered-pivot connections at the ORIGINAL combinational fixed point.
    A producer need not be constant. No CPU expansion or statement reordering. *)
From Coq Require Import List.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVConstantRoot.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVConstantRoot.
Module ExtendedSVCombConnection.

Theorem actual_lfp_pivot_output p prefix pivot suffix root seed fixed :
 filter is_comb (processes p)=prefix++pivot::suffix ->
 roots_unwrittenb root suffix=true -> CombLFP p seed fixed ->
 read_signal fixed root =
 read_signal (run_process p (fold_left (run_process p) prefix fixed) pivot) root.
Proof.
 intros Horder Hsuffix Hlfp. destruct Hlfp as [n fixed Hiter Hfixed].
 transitivity (read_signal (comb_round p fixed) root).
 - now rewrite Hfixed.
 - unfold comb_round. rewrite Horder,fold_left_app. cbn [fold_left].
   apply fold_run_process_preserves_root.
   exact (roots_unwrittenb_sound root suffix Hsuffix).
Qed.

(** Signals not written by pivot or later processes have their final fixed-point
    value already at the pivot's input. They MAY be written in the prefix. *)
Theorem actual_lfp_pivot_input p prefix pivot suffix root seed fixed :
 filter is_comb (processes p)=prefix++pivot::suffix ->
 roots_unwrittenb root (pivot::suffix)=true -> CombLFP p seed fixed ->
 read_signal (fold_left (run_process p) prefix fixed) root = read_signal fixed root.
Proof.
 intros Horder Htail Hlfp. destruct Hlfp as [n fixed Hiter Hfixed].
 symmetry. transitivity (read_signal (comb_round p fixed) root).
 - now rewrite Hfixed.
 - unfold comb_round. rewrite Horder,fold_left_app.
   apply fold_run_process_preserves_root.
   exact (roots_unwrittenb_sound root (pivot::suffix) Htail).
Qed.
End ExtendedSVCombConnection.
Print Assumptions ExtendedSVCombConnection.actual_lfp_pivot_output.
Print Assumptions ExtendedSVCombConnection.actual_lfp_pivot_input.
