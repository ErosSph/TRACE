(** Bootstrap a real bounded-catalog runtime from explicit environment data.
    No previous CPU invariant, boot theorem or changed initial state. *)
From Coq Require Import ZArith List Bool PeanoNat.
Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVDependencyPropagation Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase
 Lang.ExtendedSVConstrainedRuntime Lang.ExtendedSVCheckedPhaseReplay.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant
 ExtendedSVDependencyPropagation ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.
Module ExtendedSVBootstrap.
Definition input_rootb p catalog root:=
 Nat.ltb root(signal_count p)&&forallb(fun wr=>negb(Nat.eqb(snd wr)root))(catalog_outputs catalog).
Theorem checked_input_root p catalog root old value:input_rootb p catalog root=true->
 CatalogEvent p catalog {|changed_signal:=root;old_value:=old;new_value:=value|}.
Proof.
 unfold input_rootb;rewrite andb_true_iff;intros[HB HO];split.
 - now apply Nat.ltb_lt.
 - intros w r HI. apply forallb_forall with(x:=(w,r))in HO;[|exact HI].
   apply negb_true_iff in HO. now apply Nat.eqb_neq in HO.
Qed.
Theorem zero_seed_shape p catalog:CatalogShape p catalog(repeat 0%Z(signal_count p)).
Proof. split;[apply repeat_length|]. intros w r _;apply zero_state_word. Qed.
Definition seed_writes seed(writes:list(nat*Z)):=
 fold_left(fun state wr=>write_signal state(fst wr)(snd wr))writes seed.

Section Checked.
Variable p:Program.
Variable catalog:Catalog.
Variable certificate:BoundedCatalogCertificate p catalog.
Theorem checked_writes_shape writes:
 Forall(fun wr=>input_rootb p catalog(fst wr)=true)writes->forall seed,
 CatalogShape p catalog seed->CatalogShape p catalog(seed_writes seed writes).
Proof.
 intro HW;induction HW as[|wr rest Hroot HW IH];intros seed HS;[exact HS|].
 change(CatalogShape p catalog(seed_writes(write_signal seed(fst wr)(snd wr))rest)).
 apply IH. exact(input_shape p catalog
 {|changed_signal:=fst wr;old_value:=0%Z;new_value:=snd wr|}seed
 (checked_input_root p catalog(fst wr)0%Z(snd wr)Hroot)HS).
Qed.
Theorem checked_seed_shape writes:
 Forall(fun wr=>input_rootb p catalog(fst wr)=true)writes->
 CatalogShape p catalog(seed_writes(repeat 0%Z(signal_count p))writes).
Proof. intro HW;apply checked_writes_shape;[exact HW|apply zero_seed_shape]. Qed.
Theorem catalog_phase_evidence ev pre:CatalogEvent p catalog ev->CatalogShape p catalog pre->
 CombLFP p(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state p ev pre) /\
 (exists seed,CombLFP p seed(PhaseSemantics p ev pre)) /\CatalogShape p catalog(PhaseSemantics p ev pre).
Proof.
 intros HE HS;destruct(original_catalog_phase p catalog certificate ev pre HE HS)as[HL[HP _]].
 split;[exact HL|]. split.
 - exists(execute_process_order p(phase_driven_state p ev pre)
    (selected_on_transition p pre(phase_driven_state p ev pre)));exact HP.
 - exact(original_catalog_phase_shape p catalog certificate ev pre HE HS).
Qed.
Theorem catalog_ready events:Forall(CatalogEvent p catalog)events->forall pre,
 ExtendedSVCheckedPhaseReplay.Ready p(fun ev _=>CatalogEvent p catalog ev)events pre.
Proof.
 intro HE;induction HE as[|ev rest HE HR IH];intro pre;[exact I|].
 split;[exact HE|apply IH].
Qed.
Theorem checked_boot_runtime events pre:events<>[]->Forall(CatalogEvent p catalog)events->
 CatalogShape p catalog pre->CatalogShape p catalog(phase_run p events pre) /\
 exists seed,CombLFP p seed(phase_run p events pre).
Proof.
 intros HN HE HS. exact(ExtendedSVConstrainedRuntime.nonempty_history_runtime p
 (CatalogShape p catalog)(fun ev _=>CatalogEvent p catalog ev)catalog_phase_evidence
 events pre HN(catalog_ready events HE pre)HS).
Qed.
End Checked.
Print Assumptions checked_input_root.
Print Assumptions zero_seed_shape.
Print Assumptions checked_writes_shape.
Print Assumptions checked_seed_shape.
Print Assumptions catalog_phase_evidence.
Print Assumptions catalog_ready.
Print Assumptions checked_boot_runtime.
End ExtendedSVBootstrap.
