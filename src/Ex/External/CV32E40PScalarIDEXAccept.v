(** General normal ID/EX sampling, no hardcoded ADD operator. Actual
    controller acceptance and trigger conditions remain explicit. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice
 Lang.ExtendedSVNBAProjection Ex.Generated.CV32E40PExtendedAST
 Ex.External.CV32E40PAddiIDEXHold Ex.External.CV32E40PAddiIDEXAccept.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
 ExtendedSVNBAProjection CV32E40PExtendedAST CV32E40PAddiIDEXHold CV32E40PAddiIDEXAccept.
Local Open Scope Z_scope.
Module CV32E40PScalarIDEXAccept.
 Definition accept_scalar_inputs s :=
   norm 1 (read_signal s 561%nat) = 1 /\
   norm 1 (read_signal s 662%nat) = 0 /\
   norm 1 (read_signal s 696%nat) = 0 /\
   norm 1 (read_signal s 586%nat) = 1 /\
   norm 1 (read_signal s 779%nat) = 1 /\
   norm 7 (read_signal s 780%nat) <> 22 /\ norm 7 (read_signal s 780%nat) <> 23.
 Definition scalar_field s root old := match root with
   | 601%nat => write_slice old 0 7 (norm 7 (read_signal s 780%nat))
   | _ => accepted_field s root old end.
 Lemma scalar_not_clip mux op : op <> 22 -> op <> 23 ->
   norm 1 (Z.land (norm 1 (boolz (norm 3 0 =? norm 3 mux)))
     (norm 1 (Z.lor (norm 1 (boolz (norm 7 22 =? op)))
                   (norm 1 (boolz (norm 7 23 =? op)))))) = 0.
 Proof.
   intros H22 H23. change (norm 7 22) with 22. change (norm 7 23) with 23.
   assert (E22 : (22 =? op) = false) by (apply Z.eqb_neq; congruence).
   assert (E23 : (23 =? op) = false) by (apply Z.eqb_neq; congruence).
   rewrite E22, E23. cbn [boolz]. change (norm 1 (Z.lor (norm 1 0) (norm 1 0))) with 0.
   rewrite Z.land_0_r. reflexivity.
 Qed.
 Lemma scalar_accept_projection s root old : accept_scalar_inputs s -> In root idex_roots ->
   apply_updates_root_value root old (process_updates cv32e40p_program s process_23) = scalar_field s root old.
 Proof.
   intros (Hr & Hmis & Hmult & Hid & Hen & H22 & H23) Hroot.
   rewrite process_nba_pruned_projection by exact actual_idex_is_nba.
   cbn [idex_roots In] in Hroot.
   repeat destruct Hroot as [Hroot|Hroot]; try contradiction; subst root;
     cbv beta iota zeta delta [cv32e40p_program statement_fuel process_23 process_body
       nba_root_pruned stmt_writers lvalue_root existsb Nat.eqb flat_map app orb
       fold_left apply_update_root_value resolve_update resolve_lvalue
       update_signal update_offset update_width update_value eval_expr];
     rewrite ?Hr, ?Hmis, ?Hmult, ?Hid, ?Hen;
     rewrite ?scalar_not_clip by assumption;
     cbn [Z.eqb]; repeat rewrite redundant_choice; rewrite ?norm_twice; reflexivity.
 Qed.
 Theorem fullcore_accepts_scalar_fields ev pre root :
   In root idex_roots -> changed_signal ev <> root ->
   accept_scalar_inputs (phase_driven_state cv32e40p_program ev pre) ->
   process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = true ->
   read_signal (PhaseSemantics cv32e40p_program ev pre) root =
     scalar_field (phase_driven_state cv32e40p_program ev pre) root (read_signal pre root).
 Proof.
   intros Hroot Hev Hin Hfire.
   rewrite phase_root_projection by (auto using idex_comb_unwritten).
   unfold phase_update_chain, selected_on_transition.
   rewrite process_slice_sound, filter_swap, idex_unique_writers by exact Hroot.
   cbn [filter]. rewrite Hfire. cbn [flat_map]. rewrite app_nil_r.
   now apply scalar_accept_projection.
 Qed.
 Print Assumptions fullcore_accepts_scalar_fields.
End CV32E40PScalarIDEXAccept.
