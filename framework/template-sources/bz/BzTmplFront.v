(** Bzeeno goal_front and goal_admission (tools/cpu_tmpl_bzarch.py; hand-written glue over BzTmplFrontFacts).
    The statements are the goals of BzTmplDefs (= the goals of the step module).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Lia.
From ITree Require Import ITree ITreeFacts.
Require Import Ex.External.CPUGeneratedJointTemplate Ex.External.CPUGeneratedJointITree Ex.External.CPUPipelineQueue Ex.External.CPUPipelineStages
 Ex.External.CPUPipelineStagesContext Ex.External.CPUPipelineMultiRetire Ex.External.CPUPipelineCycle Ex.External.CPUPipelineStaged
 Ex.External.CPUPipelineStagedContext Ex.External.CPUPipelineCycle2 Ex.External.CPUPipelineObligations Ex.External.CPUPipelineObligationsM
 Ex.External.CV32E40PTwoCommitITreeInterface Ex.RvCore.FormalSpec Lang.ExtendedSV Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBankOperand
 Lang.ExtendedSVRootProjection Lang.ExtendedSVSeqTree Lang.ExtendedSVStallFlush Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Lang.ExtendedSVPackedROM
 Ex.External.CPUProgramROM Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUISARegView Ex.External.CPUJumpFamilyProgramExecution
 GeneratedRuntimeInput.ConfiguredAST GeneratedWriteValidityBoot.WriteValidityBoot
 GeneratedClockCycleJoint.CycleJoint GeneratedSeedBoot.FrozenEnvironment
 GeneratedCapturedHistoryBoot.CapturedHistoryBoot TmplBzEnv.BzTmplEnv TmplBzShape.BzTmplShape
 TmplBzRank.BzTmplRank TmplBzDefs.BzTmplDefs TmplBzPhase.BzTmplPhase TmplBzInv.BzTmplInv TmplBzValid.BzTmplValid TmplBzXfer.BzTmplXfer TmplBzFrame.BzTmplFrame
 TmplBzIfId.BzTmplIfId TmplBzFetch.BzTmplFetch TmplBzExGen.BzTmplExGen TmplBzExIface.BzTmplExIface TmplBzTrCore.BzTmplTrCore TmplBzNState.BzTmplNState TmplBzFrontFacts.BzTmplFrontFacts TmplBzEdge.BzTmplEdge
 GeneratedJumpITree.JumpITree Ex.External.CV32E40PDataOpProgramScope
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Spec.Decode.
Import ListNotations CPUGeneratedJointTemplate CPUGeneratedJointITree CPUPipelineQueue CPUPipelineStages
 CPUPipelineStagesContext CPUPipelineMultiRetire CPUPipelineCycle CPUPipelineStaged
 CPUPipelineStagedContext CPUPipelineCycle2 CPUPipelineObligations CPUPipelineObligationsM
 CV32E40PTwoCommitITreeInterface ExtendedSV ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase ExtendedSVWordInvariant ExtendedSVBankAlignment ExtendedSVRootProjection ExtendedSVSeqTree.
Local Open Scope itree_scope.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplFront.
Module Ph := TmplBzPhase.BzTmplPhase.BzTmplPhase.
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Sh := TmplBzShape.BzTmplShape.BzTmplShape.
Module Va := TmplBzValid.BzTmplValid.BzTmplValid.
Module Xf := TmplBzXfer.BzTmplXfer.BzTmplXfer.
Module Fr := TmplBzFrame.BzTmplFrame.BzTmplFrame.
Module Co := TmplBzTrCore.BzTmplTrCore.BzTmplTrCore.
Module FF := TmplBzFrontFacts.BzTmplFrontFacts.BzTmplFrontFacts.
Module Ft := TmplBzFetch.BzTmplFetch.BzTmplFetch.
Module If := TmplBzIfId.BzTmplIfId.BzTmplIfId.
Module Ed := TmplBzEdge.BzTmplEdge.BzTmplEdge.
Module PD := Ex.External.CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
Import BzTmplDefs.
Lemma comb_unw_330 : comb_root_unwrittenb P 330%nat = true. Proof. vm_compute; reflexivity. Qed.
Section Skeleton.
Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.
Local Notation uw := word.unsigned.

Lemma words_word (words : list Z) : PD.check_program words = true -> Forall (Word 32) words.
Proof. intro HC. apply Forall_forall. intros x Hx. apply In_nth with (d := 0) in Hx as [n [Hn Hnth]].
 destruct (PD.checked_entry words n HC Hn) as [i [_ [[H0 H1] _]]]. rewrite <- Hnth. unfold Word. rewrite norm_mod. symmetry. apply Z.mod_small. split; [exact H0|exact H1]. Qed.

(** the IF/ID registers and the fetch pc after the cycle *)
Lemma new_ifid words events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> Sh.stallD words events = 1 ->
 norm 1 (read_signal (Ph.fall_state words events) 141%nat) = (if Z.eqb (Sh.flushD words events) 0 then 1 else 0) /\
 (Sh.flushD words events = 0 -> norm 32 (read_signal (Ph.fall_state words events) 139%nat) = norm 32 (read_signal (En.rs words events) 119%nat) /\
    norm 32 (read_signal (Ph.fall_state words events) 138%nat) = norm 32 (read_signal (Sh.drv words events) 27%nat) /\
    norm 32 (read_signal (Ph.fall_state words events) 140%nat) = norm 32 (read_signal (Sh.drv words events) 137%nat)) /\
 (Sh.flushD words events <> 0 -> norm 32 (read_signal (Ph.fall_state words events) 139%nat) = 0 /\
    norm 32 (read_signal (Ph.fall_state words events) 138%nat) = 0 /\ norm 32 (read_signal (Ph.fall_state words events) 140%nat) = 28691) /\
 norm 32 (read_signal (Ph.fall_state words events) 119%nat) = norm 32 (read_signal (Sh.drv words events) 130%nat).
Proof.
 intros HE HB Hn. destruct (Ph.cycle_hyps words events HE HB) as [[seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]] [[seed2 [Hc2 [Hv2 [H02 [H12 [HW2 [HL2 HD2]]]]]]] _]].
 pose proof (conj Hc (conj Hv (conj H0 (conj H1 (conj HW (conj HL HD)))))) as HH.
 assert (V141 := Va.valid_141 F.rise (En.rs words events) seed (Sh.flushD words events) (Sh.stallD words events) Hc Hv H0 H1 HW HL HD eq_refl eq_refl).
 assert (X119 := Xf.xfer_119 F.rise (En.rs words events) seed (Sh.stallD words events) HH eq_refl).
 assert (X138 := Xf.xfer_138 F.rise (En.rs words events) seed (Sh.flushD words events) (Sh.stallD words events) HH eq_refl eq_refl).
 assert (X139 := Xf.xfer_139 F.rise (En.rs words events) seed (Sh.flushD words events) (Sh.stallD words events) HH eq_refl eq_refl).
 assert (X140 := Xf.xfer_140 F.rise (En.rs words events) seed (Sh.flushD words events) (Sh.stallD words events) HH eq_refl eq_refl).
 rewrite Hn in V141, X119, X138, X139, X140. cbn [Z.eqb] in X119.
 rewrite <- Ph.rise_state_eq in V141, X119, X138, X139, X140. rewrite Ph.fall_state_eq.
 set (mid := Ph.rise_state words events) in *.
 rewrite (Fr.fall_frame_141 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2), (Fr.fall_frame_139 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_138 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2), (Fr.fall_frame_140 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2),
   (Fr.fall_frame_119 F.fall mid seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2).
 split; [|split; [|split]].
 - rewrite V141. destruct (Z.eqb (Sh.flushD words events) 0); reflexivity.
 - intro Hf. rewrite Hf in X138, X139, X140, V141. cbn [Z.eqb] in X138, X139, X140. rewrite X139, X138, X140. split; [reflexivity|]. split; reflexivity.
 - intro Hf. apply Z.eqb_neq in Hf. rewrite Hf in X138, X139, X140. rewrite X139, X138, X140. split; [|split]; reflexivity.
 - exact X119.
Qed.

Local Notation Cyc := JumpITree.actual_cycle.

(** facts about the physical state shared by front and admission *)
Lemma phys_facts (words:list Z)(HC:PD.check_program words=true) s retired frontier :
 staged_physical (design words HC) s retired frontier ->
 Forall GeneratedWriteValidityBoot.WriteValidityBoot.Environment s /\
 Forall (CatalogEvent P Cat) s /\ ClockBoundary (En.rs words s) /\ BzTmplInv.Struct (En.rs words s) /\ Sh.stallD words s = 1 /\
 (exists index, PD.AtProgram words index frontier) /\ FF.FrontFacts words s frontier.
Proof.
 intros HP. unfold staged_physical in HP. destruct HP as [HA [HF HSR]]. cbn[design sd_arch sd_front sd_stages sd_stage sd_effect] in HA, HF, HSR.
 destruct HF as [HEnv [HB [HS [HAtF H119]]]]. pose proof (Forall_impl _ (fun ev H => proj1 H) HEnv) as HE.
 pose proof (BzTmplNState.n_one_state words s HE HB HS) as Hn.
 repeat (split; [assumption|]). exact (FF.front_facts words HC s retired frontier HE HB HS HA HAtF H119 HSR).
Qed.

(** the fetched word and the sequential successor at the driven state *)
Lemma fetch_new words (HC:PD.check_program words=true) events idx :
 Forall GeneratedWriteValidityBoot.WriteValidityBoot.Environment events -> Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) ->
 norm 32 (read_signal (En.rs words events) 119%nat) = 4 * Z.of_nat idx -> (idx < length words)%nat ->
 norm 32 (read_signal (Sh.drv words events) 137%nat) = nth idx words 0 /\ norm 32 (read_signal (Sh.drv words events) 27%nat) = norm 32 (4 * Z.of_nat idx + 4).
Proof.
 intros HEnv HE HB H119 Hidx.
 destruct (En.env_rise_hyps words events HE HB) as [seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]].
 pose proof (PD.checked_length words HC) as Hlen.
 assert (Hd119 : norm 32 (read_signal (Sh.drv words events) 119%nat) = 4 * Z.of_nat idx).
 { change (Sh.drv words events) with (phase_driven_state P F.rise (En.rs words events)).
   rewrite (driven_unchanged P F.rise (En.rs words events) 119%nat Fr.comb_unw_119 ltac:(rewrite Hc; discriminate)). exact H119. }
 assert (HR : read_signal (Sh.drv words events) 330%nat = ExtendedSVPackedROM.pack words).
 { change (Sh.drv words events) with (phase_driven_state P F.rise (En.rs words events)).
   rewrite (driven_unchanged P F.rise (En.rs words events) 330%nat comb_unw_330 ltac:(rewrite Hc; discriminate)).
   exact (Ft.rom_inv words events HEnv). }
 split.
 - rewrite (Ft.fetch_word (write_signal (En.rs words events) (changed_signal F.rise) (new_value F.rise)) (Sh.drv words events) words idx HD HR (words_word words HC) ltac:(lia) Hd119).
   destruct (PD.checked_entry words idx HC Hidx) as [i [_ [[H0' H1'] _]]]. rewrite norm_mod. apply Z.mod_small. split; assumption.
 - exact (TmplBzExGen.BzTmplExGen.BzTmplExGen.if_p4 (write_signal (En.rs words events) (changed_signal F.rise) (new_value F.rise)) (Sh.drv words events) _ HD Hd119).
Qed.

Theorem admission_proved (words:list Z)(HC:PD.check_program words=true): goal_admission words HC.
Proof.
 unfold goal_admission. intros s retired frontier HP.
 destruct (phys_facts words HC s retired frontier HP) as [HEnv [HE [HB [HS [Hn [HAtF HFF]]]]]].
 destruct HFF as [FP [F163 [F164 [FC1 FC2]]]].
 unfold shape_admission, plan_shape, plan_next. cbn[design sd_effect sd_stage sd_stages sd_step].
 destruct (Z.eqb (Sh.flushD words s) 0) eqn:Ef.
 - apply Z.eqb_eq in Ef. cbn[shape_admitted].
   destruct HAtF as [idx HAt].
   assert (Ht : BzTmplInv.rg (En.rs words s) 119 32 = uw (getPc frontier)) by exact (FC1 Ef).
   destruct (PD.checked_run1_total words idx frontier HC HAt) as [after Hrun].
   split.
   + unfold checked_pc_effect. rewrite Ht, Z.eqb_refl. rewrite Hrun. reflexivity.
   + change (pred (length (BzTmplInv.stages words s))) with 2%nat.
     change (BzTmplInv.stage_rel words (Cyc s) 2 (BzTmplInv.rg (En.rs words s) 119 32) frontier) with
       (BzTmplInv.StageID words (En.rs words (Cyc s)) (BzTmplInv.rg (En.rs words s) 119 32) frontier).
     destruct (new_ifid words s HE HB Hn) as [N141 [Nf0 [Nf1 N119]]].
     destruct (Nf0 Ef) as [N139 [N138 N140]].
     destruct HAt as [Hidx [Hpc [Hmem HNX]]]. pose proof (conj Hidx (conj Hpc (conj Hmem HNX))) as HAt.
     assert (Hpc' : BzTmplInv.rg (En.rs words s) 119 32 = 4 * Z.of_nat idx) by (rewrite Ht; exact Hpc).
     destruct (fetch_new words HC s idx HEnv HE HB Hpc' Hidx) as [Hf137 Hf27].
     rewrite Ef in N141. cbn [Z.eqb] in N141.
     assert (Hq : Z.to_nat (BzTmplInv.rg (En.rs words s) 119 32 / 4) = idx) by (rewrite Hpc'; rewrite Z.mul_comm, Z.div_mul by lia; apply Nat2Z.id).
     unfold BzTmplInv.StageID, BzTmplInv.rg, BzTmplInv.Dom, BzTmplInv.iword in *.
     refine (conj N141 (conj _ (conj _ (conj _ _)))).
     * exact N139.
     * refine (eq_trans N140 _). rewrite Hf137, Hq. destruct (PD.checked_entry words idx HC Hidx) as [i [_ [Hb _]]]. rewrite norm_mod. symmetry. apply Z.mod_small. split; [exact (proj1 Hb)|exact (proj2 Hb)].
     * refine (eq_trans N138 _). rewrite Hf27, Hpc'. reflexivity.
     * rewrite Hq. split; [exact HAt|exact Ht].
 - cbn[shape_admitted]. reflexivity.
Qed.

Lemma d130_ntaken words events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> norm 2 (read_signal (Sh.drv words events) 159%nat) = 0 ->
 norm 32 (read_signal (Sh.drv words events) 130%nat) = norm 32 (norm 32 (read_signal (En.rs words events) 119%nat) + 4).
Proof.
 intros HE HB H159. destruct (En.env_rise_hyps words events HE HB) as [seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]].
 rewrite (TmplBzExIface.BzTmplExIface.BzTmplExIface.ntaken_e3 (write_signal (En.rs words events) (changed_signal F.rise) (new_value F.rise)) (Sh.drv words events) HD H159).
 change (Sh.drv words events) with (phase_driven_state P F.rise (En.rs words events)).
 rewrite (driven_unchanged P F.rise (En.rs words events) 119%nat Fr.comb_unw_119 ltac:(rewrite Hc; discriminate)). reflexivity.
Qed.

Theorem front_proved (words:list Z)(HC:PD.check_program words=true): goal_front words HC.
Proof.
 unfold goal_front. intros s retired frontier HP.
 destruct (phys_facts words HC s retired frontier HP) as [HEnv [HE [HB [HS [Hn [HAtF HFF]]]]]].
 destruct HFF as [FP [F163 [F164 [FC1 FC2]]]].
 cbn[design sd_front sd_step]. unfold plan_next.
 pose proof HS as HSfull.
 destruct (Ph.cycle_hyps words s HE HB) as [_ [_ [HBnew _]]].
 pose proof (Co.post_holds words s HE HB Hn) as HPo.
 change (Co.Post (En.rs words s) (Sh.drv words s) (Ph.fall_state words s)) in HPo.
 destruct (new_ifid words s HE HB Hn) as [N141 [Nf0 [Nf1 N119]]].
 destruct HS as [HS1 [HS2 [HS3 [HS4 [[HS5a HS5b] HS6]]]]].
 pose proof (If.ifid_idle_step words s HE HB HS1) as HIdle.
 assert (Hlegal : exists i, Decode.decode Decode.RV32I (BzTmplInv.rg (Ph.fall_state words s) 140 32) = Decode.IInstruction i /\ PD.legal_instruction i = true).
 { destruct (Z.eqb (Sh.flushD words s) 0) eqn:Ef.
   - apply Z.eqb_eq in Ef. destruct (Nf0 Ef) as [_ [_ N140]]. destruct HAtF as [idx HAt].
     assert (Ht : norm 32 (read_signal (En.rs words s) 119%nat) = 4 * Z.of_nat idx) by (rewrite (FC1 Ef); exact (proj1 (proj2 HAt))).
     destruct (fetch_new words HC s idx HEnv HE HB Ht (proj1 HAt)) as [Hf137 _].
     destruct (PD.checked_entry words idx HC (proj1 HAt)) as [i [Hd [Hb [Hl _]]]]. exists i. split; [|exact Hl].
     unfold BzTmplInv.rg. rewrite N140, Hf137. exact Hd.
   - apply Z.eqb_neq in Ef. destruct (Nf1 Ef) as [_ [_ N140]]. exists (Decode.Andi 0 0 0). split; [|reflexivity].
     unfold BzTmplInv.rg. rewrite N140. vm_compute. reflexivity. }
 refine (conj _ (conj _ (conj _ (conj _ _)))).
 - unfold JumpITree.actual_cycle. apply Forall_app. split.
   + apply Forall_app. split; [exact HEnv|]. constructor; [apply CycleJoint.scheduled_event_allowed; cbn; auto|constructor].
   + constructor; [apply CycleJoint.scheduled_event_allowed; cbn; auto|constructor].
 - exact HBnew.
 - unfold BzTmplInv.Struct. refine (conj _ (conj _ (conj _ (conj _ (conj _ Hlegal))))).
   + exact HIdle.
   + intro H250. unfold BzTmplInv.rg in H250 |- *.
     pose proof (eq_trans (eq_sym (Co.p250 _ _ _ HPo)) H250) as P250.
     assert (H141 : BzTmplInv.rg (En.rs words s) 141 1 = 0) by exact P250.
     destruct (HS1 H141) as [Hnop _]. unfold BzTmplInv.rg, BzTmplInv.nop_word in Hnop.
     refine (conj (eq_trans (Co.p244 _ _ _ HPo) _) (conj (eq_trans (Co.p233 _ _ _ HPo) _) (eq_trans (Co.p232 _ _ _ HPo) _))).
     * rewrite Hnop. vm_compute. reflexivity.
     * exact F163.
     * exact F164.
   + intro H286. unfold BzTmplInv.rg in H286 |- *.
     pose proof (eq_trans (eq_sym (Co.p286 _ _ _ HPo)) H286) as P286.
     assert (H250 : BzTmplInv.rg (En.rs words s) 250 1 = 0) by exact P286.
     destruct (HS2 H250) as [A [B C]]. unfold BzTmplInv.rg in A, B, C.
     refine (conj (eq_trans (Co.p283 _ _ _ HPo) A) (conj (eq_trans (Co.p278 _ _ _ HPo) B) (eq_trans (Co.p277 _ _ _ HPo) C))).
   + intro H141'. unfold BzTmplInv.rg in H141' |- *.
     pose proof (eq_trans (eq_sym N141) H141') as Hq1.
     destruct (Z.eqb (Sh.flushD words s) 0) eqn:Ef; [|discriminate Hq1].
     apply Z.eqb_eq in Ef. destruct (Nf0 Ef) as [N139 _].
     refine (eq_trans N119 _). rewrite (d130_ntaken words s HE HB (FP Ef)). f_equal. f_equal. exact (eq_sym N139).
   + split.
     * unfold BzTmplInv.rg. exact (eq_trans (Co.p232 _ _ _ HPo) F164).
     * unfold BzTmplInv.rg. exact (eq_trans (Co.p277 _ _ _ HPo) HS5a).
 - destruct (Z.eqb (Sh.flushD words s) 0) eqn:Ef.
   + apply Z.eqb_eq in Ef. destruct HAtF as [idx HAt]. destruct (PD.checked_run1_total words idx frontier HC HAt) as [after Hrun].
     destruct (PD.checked_run1_stays_in_program words idx frontier after HC HAt Hrun) as [nx [HN _]].
     exists nx. rewrite Hrun. exact HN.
   + exact HAtF.
 - intro H141'. unfold BzTmplInv.rg in H141' |- *.
   pose proof (eq_trans (eq_sym N141) H141') as Hq1.
   destruct (Z.eqb (Sh.flushD words s) 0) eqn:Ef; [discriminate Hq1|].
   apply Z.eqb_neq in Ef. exact (eq_trans N119 (FC2 Ef)).
Qed.
End Skeleton.
End BzTmplFront.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplFront.admission_proved.
Print Assumptions BzTmplFront.front_proved.
