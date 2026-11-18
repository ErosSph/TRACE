(** Ordered EX bypass carries the current ID/EX arithmetic, not a guessed value. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCombCut Lang.ExtendedSVRootProjection
 Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiOperandCone
 Ex.External.CV32E40PAddiForwardCone Ex.External.CV32E40PAddiWritebackCone
 Ex.External.CV32E40PAddiFullCoreALU Ex.External.CV32E40PAddiEXOperandWiring
 Ex.External.CV32E40PAddiIDEXHold Ex.External.CV32E40PAddiAdder.
Import ListNotations ExtendedSV ExtendedSVCombCut ExtendedSVRootProjection
 CV32E40PExtendedAST CV32E40PAddiOperandCone CV32E40PAddiForwardCone
 CV32E40PAddiWritebackCone CV32E40PAddiFullCoreALU CV32E40PAddiEXOperandWiring
 CV32E40PAddiIDEXHold CV32E40PAddiAdder.
Local Open Scope Z_scope.
Module CV32E40PAddiEXForwardValue.
 Definition round3 ev pre := comb_iter cv32e40p_program 3 (write_signal pre (changed_signal ev) (new_value ev)).
 Lemma norm_add_normalize x y : norm 32 (x+y) = norm 32 (norm 32 x + norm 32 y).
 Proof. rewrite !norm_mod. apply Z.add_mod. vm_compute; discriminate. Qed.
 #[local] Opaque before_process comb_round read_signal.
 Theorem ex_forward_is_idex_sum ev pre :
 changed_signal ev <> 589%nat -> changed_signal ev <> 590%nat ->
 ScalarADD (round3 ev pre) -> ALUSelected (round (round3 ev pre)) ->
 norm 32 (read_signal (cut 1629 (round6 ev pre)) 695%nat) =
 norm 32 (norm 32 (read_signal pre 589%nat) + norm 32 (read_signal pre 590%nat)).
 Proof.
 intros Ha Hb Hscalar Hsel.
 unfold cut at 1. rewrite before_process_keeps_root by (vm_compute; reflexivity).
 change (norm 32 (read_signal (round (round (round (round3 ev pre)))) 695%nat) =
 norm 32 (norm 32 (read_signal pre 589%nat) + norm 32 (read_signal pre 590%nat))).
 rewrite round_forward, round_ex_alu by exact Hsel.
 rewrite round_alu_wire, fullcore_alu_scalar_add by exact Hscalar.
 rewrite norm_add_normalize.
 destruct (alu_cut_operands (round3 ev pre)) as [A B]. rewrite A,B.
 unfold round3.
 rewrite !comb_iter_preserves_unwritten_root by (apply idex_comb_unwritten; cbn [idex_roots In]; auto).
 rewrite !read_signal_write_other by assumption. reflexivity.
 Qed.
 Print Assumptions ex_forward_is_idex_sum.
End CV32E40PAddiEXForwardValue.
