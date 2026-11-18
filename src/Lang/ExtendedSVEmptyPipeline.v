(** Empty capture/metadata boot rules over original phase semantics. *)
From Coq Require Import ZArith List Bool.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVConstantRoot Lang.ExtendedSVProjectionOrigin
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCoveredField Lang.ExtendedSVBoundedCatalogPhase
 Lang.ExtendedSVCheckedPhaseReplay.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVRootProjection
 ExtendedSVProcessSlice ExtendedSVConstantRoot ExtendedSVProjectionOrigin ExtendedSVCaptureBirth
 ExtendedSVCoveredField ExtendedSVBoundedCatalogPhase.
Module ExtendedSVEmptyPipeline.
Theorem read_zero_seed count root:read_signal(repeat 0%Z count)root=0%Z.
Proof. induction count in root|-*;destruct root;cbn;auto. Qed.

Theorem recipe_origin_empty(Label:Type)s recipe:
 @recipe_origin Label s recipe None None=None.
Proof. induction recipe;cbn[recipe_origin];try reflexivity;destruct(Z.eqb _ 0);assumption. Qed.
Theorem phase_origin_empty(Label:Type)p proc recipe ev pre:
 @projection_phase_origin Label p proc recipe ev pre None None=None.
Proof. unfold projection_phase_origin;destruct(process_matches_states _ _ _);[apply recipe_origin_empty|reflexivity]. Qed.
Theorem ghost_empty_invalid p proc root word valid pc ev pre:
 norm 1(eval_expr(phase_driven_state p ev pre)valid)=0%Z->
 ghost_step p proc root word valid pc ev pre(Build_Ghost 0 None [])=Build_Ghost 0 None [].
Proof.
 intro H;unfold ghost_step,phase_decision;destruct(process_matches_states _ _ _);[|reflexivity].
 unfold decide;rewrite H;reflexivity.
Qed.
Theorem ghost_empty_idle p proc root word valid pc ev pre:
 process_matches_states pre(phase_driven_state p ev pre)proc=false->
 ghost_step p proc root word valid pc ev pre(Build_Ghost 0 None [])=Build_Ghost 0 None [].
Proof. intro H;unfold ghost_step,phase_decision;rewrite H;reflexivity. Qed.

Lemma all_unwritten_comb p root:roots_unwrittenb root(processes p)=true->comb_root_unwrittenb p root=true.
Proof.
 unfold roots_unwrittenb,comb_root_unwrittenb;intro H;apply forallb_forall.
 intros proc HP;apply filter_In in HP;exact(proj1(forallb_forall _ _)H proc(proj1 HP)).
Qed.
Theorem sampled_input p root ev pre:roots_unwrittenb root(processes p)=true->
 read_signal(phase_driven_state p ev pre)root=read_signal(write_signal pre(changed_signal ev)(new_value ev))root.
Proof. intro H;unfold phase_driven_state;apply lfp_candidate_preserves_unwritten_root;now apply all_unwritten_comb. Qed.
Lemma selected_updates_avoid p root pre sampled:roots_unwrittenb root(processes p)=true->
 updates_avoid root(flat_map(process_updates p sampled)(selected_on_transition p pre sampled)).
Proof.
 intros HW u HU HE. apply in_flat_map in HU as[proc[HP HU]].
 unfold selected_on_transition in HP;apply filter_In in HP.
 pose proof(roots_unwrittenb_sound _ _ HW proc(proj1 HP))as HN.
 apply HN. rewrite<-HE. exact(process_emitted_writers p sampled proc u HU).
Qed.
Theorem phase_input p root ev pre:roots_unwrittenb root(processes p)=true->
 read_signal(PhaseSemantics p ev pre)root=read_signal(write_signal pre(changed_signal ev)(new_value ev))root.
Proof.
 intro HW;unfold PhaseSemantics,phase_execute_order,execute_process_order.
 rewrite(lfp_candidate_preserves_unwritten_root p root(all_unwritten_comb p root HW)).
 rewrite read_signal_apply_updates.
 rewrite(apply_root_avoids _ _ _(selected_updates_avoid p root pre(phase_driven_state p ev pre)HW)).
 exact(sampled_input p root ev pre HW).
Qed.
Theorem catalog_shape_history p catalog(certificate:BoundedCatalogCertificate p catalog)events:
 Forall(CatalogEvent p catalog)events->forall pre,CatalogShape p catalog pre->
 CatalogShape p catalog(phase_run p events pre).
Proof.
 intro HE;induction HE as[|ev rest HE HR IH];intros pre HS;[exact HS|].
 cbn[phase_run];apply IH;exact(original_catalog_phase_shape p catalog certificate ev pre HE HS).
Qed.
Theorem empty_related_valid_zero(Label:Type)width root valid reference s:
 @ExtendedSVCoveredField.Related Label width root valid reference None s->norm 1(read_signal s valid)=0%Z.
Proof.
 intros[HC _];destruct(Z.eq_dec(norm 1(read_signal s valid))0)as[HZ|HN];[exact HZ|].
 destruct(HC HN)as[token H];discriminate.
Qed.
Theorem ready_from_preservation p (EventClass:Event->Prop)(StateInv:State->Prop)(Allowed:Event->State->Prop)
 (keep:forall ev pre,EventClass ev->StateInv pre->Allowed ev pre /\StateInv(PhaseSemantics p ev pre))events:
 Forall EventClass events->forall pre,StateInv pre->ExtendedSVCheckedPhaseReplay.Ready p Allowed events pre.
Proof.
 intro HE;induction HE as[|ev rest HE HR IH];intros pre HI;[exact I|].
 destruct(keep ev pre HE HI)as[HA Hpost];split;[exact HA|exact(IH _ Hpost)].
Qed.
Print Assumptions recipe_origin_empty.
Print Assumptions read_zero_seed.
Print Assumptions phase_origin_empty.
Print Assumptions ghost_empty_invalid.
Print Assumptions ghost_empty_idle.
Print Assumptions all_unwritten_comb.
Print Assumptions sampled_input.
Print Assumptions phase_input.
Print Assumptions catalog_shape_history.
Print Assumptions empty_related_valid_zero.
Print Assumptions ready_from_preservation.
End ExtendedSVEmptyPipeline.
