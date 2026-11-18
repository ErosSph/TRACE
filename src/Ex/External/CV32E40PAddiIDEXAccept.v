(** Normal ADD/ADDI ID-to-EX sampling, on the actual FullCore AST. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection
  Lang.ExtendedSVProcessSlice Lang.ExtendedSVNBAProjection.
Require Import Ex.Generated.CV32E40PExtendedAST Ex.External.CV32E40PAddiIDEXHold.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice
  ExtendedSVNBAProjection CV32E40PExtendedAST CV32E40PAddiIDEXHold.
Local Open Scope Z_scope.
Module CV32E40PAddiIDEXAccept.
  Definition accept_add_inputs (s : State) : Prop :=
    norm 1 (read_signal s 561%nat) = 1 /\
    norm 1 (read_signal s 662%nat) = 0 /\
    norm 1 (read_signal s 696%nat) = 0 /\
    norm 1 (read_signal s 586%nat) = 1 /\
    norm 1 (read_signal s 779%nat) = 1 /\
    norm 7 (read_signal s 780%nat) = 24.

  Definition accepted_field (s : State) (root : signal) (old : Z) : Z :=
    match root with
    | 589%nat => write_slice old 0 32 (norm 32 (read_signal s 844%nat))
    | 590%nat => write_slice old 0 32 (norm 32 (read_signal s 845%nat))
    | 598%nat => if norm 1 (read_signal s 774%nat) =? 0 then old
        else write_slice old 0 6 (norm 6 (read_signal s 773%nat))
    | 599%nat => write_slice old 0 1 (norm 1 (read_signal s 774%nat))
    | 600%nat => write_slice old 0 1 1
    | 601%nat => write_slice old 0 7 24
    | _ => old
    end.

  Lemma actual_idex_is_nba : nba_onlyb (process_body process_23) = true.
  Proof. reflexivity. Qed.
  Lemma redundant_choice : forall (b : bool) (v : Z), (if b then v else v) = v.
  Proof. intros [] v; reflexivity. Qed.
  Lemma norm_twice : forall w v, norm w (norm w v) = norm w v.
  Proof. intros. unfold norm. rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.
  Lemma add_not_clip : forall mux,
    norm 1 (Z.land (norm 1 (boolz (norm 3 0 =? norm 3 mux)))
      (norm 1 (Z.lor (norm 1 (boolz (norm 7 22 =? 24)))
                    (norm 1 (boolz (norm 7 23 =? 24)))))) = 0.
  Proof.
    intros. change (norm 1 (Z.land (norm 1 (boolz (norm 3 0 =? norm 3 mux))) 0) = 0).
    rewrite Z.land_0_r. reflexivity.
  Qed.

  Lemma accept_projection : forall s root old,
      accept_add_inputs s -> In root idex_roots ->
      apply_updates_root_value root old (process_updates cv32e40p_program s process_23) =
        accepted_field s root old.
  Proof.
    intros s root old (Hr & Hmis & Hmult & Hid & Hen & Hop) Hroot.
    rewrite process_nba_pruned_projection by exact actual_idex_is_nba.
    cbn [idex_roots In] in Hroot.
    repeat destruct Hroot as [Hroot|Hroot]; try contradiction; subst root;
      cbv beta iota zeta delta [cv32e40p_program statement_fuel process_23 process_body
        nba_root_pruned stmt_writers lvalue_root existsb Nat.eqb flat_map app orb
        fold_left apply_update_root_value resolve_update resolve_lvalue
        update_signal update_offset update_width update_value eval_expr];
      rewrite ?Hr, ?Hmis, ?Hmult, ?Hid, ?Hen, ?Hop;
      rewrite ?add_not_clip; cbn [Z.eqb]; repeat rewrite redundant_choice;
      rewrite ?norm_twice; reflexivity.
  Qed.
  Theorem fullcore_accepts_add_fields : forall ev pre root,
      In root idex_roots -> changed_signal ev <> root ->
      accept_add_inputs (phase_driven_state cv32e40p_program ev pre) ->
      process_matches_states pre (phase_driven_state cv32e40p_program ev pre) process_23 = true ->
      read_signal (PhaseSemantics cv32e40p_program ev pre) root =
        accepted_field (phase_driven_state cv32e40p_program ev pre) root (read_signal pre root).
  Proof.
    intros ev pre root Hroot Hev Hin Hfire.
    rewrite phase_root_projection by (auto using idex_comb_unwritten).
    unfold phase_update_chain, selected_on_transition.
    rewrite process_slice_sound, filter_swap, idex_unique_writers by exact Hroot.
    cbn [filter]. rewrite Hfire. cbn [flat_map]. rewrite app_nil_r.
    now apply accept_projection.
  Qed.
  Print Assumptions fullcore_accepts_add_fields.
End CV32E40PAddiIDEXAccept.
