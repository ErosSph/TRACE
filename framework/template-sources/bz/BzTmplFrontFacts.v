(** Bzeeno goal_front / goal_admission, the ID-stage facts at the driven rising-edge state against the ISA frontier
    (hand-written glue over BzTmplId / BzTmplSel / BzTmplNext and the transport modules).
    FrontFacts: for a physical state the controller outputs (flush => pcsrc = 0, no store/load) and the frontier pc:
      flush = 0 -> the fetch pc 119 is the pc of the ISA frontier;   flush <> 0 -> the redirect target (wire 130) is the pc of the ISA frontier.
    The forwarding of the operands over the MEM and EX stages follows BzTmplTrans.transport_core (CPUPipelineStages.forwarding_correct).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBankOperand
 GeneratedClockCycleJoint.CycleJoint GeneratedRuntimeInput.ConfiguredAST GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment
 TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv TmplBzPhase.BzTmplPhase TmplBzInv.BzTmplInv TmplBzShape.BzTmplShape TmplBzNState.BzTmplNState TmplBzCtlIn.BzTmplCtlIn
 TmplBzLink.BzTmplLink TmplBzTrIsa.BzTmplTrIsa TmplBzTrCore.BzTmplTrCore TmplBzTrCls.BzTmplTrCls TmplBzTrans.BzTmplTrans TmplBzDisp2.BzTmplDisp2
 TmplBzId.BzTmplId TmplBzSel.BzTmplSel TmplBzNext.BzTmplNext TmplBzIsa.BzTmplIsa
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext
 Ex.External.CPUGeneratedJointITree Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUISARegView Ex.External.CV32E40PReq40StateRel
 Ex.External.CPUClassTableInverse Ex.External.CPUISABranchFamilyEffects
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Spec.Decode.
Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase ExtendedSVBankOperand CV32E40PReq40StateRel
 CPUGeneratedJointTemplate CPUPipelineQueue.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplFrontFacts.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Module Ph := TmplBzPhase.BzTmplPhase.BzTmplPhase.
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Ed := TmplBzEdge.BzTmplEdge.BzTmplEdge.
Module Sh := TmplBzShape.BzTmplShape.BzTmplShape.
Module Ci := TmplBzCtlIn.BzTmplCtlIn.BzTmplCtlIn.
Module Lk := TmplBzLink.BzTmplLink.BzTmplLink.
Module Is := TmplBzTrIsa.BzTmplTrIsa.BzTmplTrIsa.
Module Co := TmplBzTrCore.BzTmplTrCore.BzTmplTrCore.
Module Cl := TmplBzTrCls.BzTmplTrCls.BzTmplTrCls.
Module Tr := TmplBzTrans.BzTmplTrans.BzTmplTrans.
Module Dp := TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Module Id := TmplBzId.BzTmplId.BzTmplId.
Module Sl := TmplBzSel.BzTmplSel.BzTmplSel.
Module Nx := TmplBzNext.BzTmplNext.BzTmplNext.
Module PD := Ex.External.CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.
Module J := Ex.External.CPUGeneratedJointITree.CPUGeneratedJointITree.
Module V := Ex.External.CPUISARegView.CPUISARegView.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Module Pst := Ex.External.CPUPipelineStages.CPUPipelineStages.
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
Section FF.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Local Notation uw := word.unsigned.

Definition FrontFacts (words : list Z) (events : list Event) (frontier : FormalSpec.State) : Prop :=
 (Sh.flushD words events = 0 -> norm 2 (read_signal (Sh.drv words events) 159%nat) = 0) /\
 norm 1 (read_signal (Sh.drv words events) 163%nat) = 0 /\ norm 1 (read_signal (Sh.drv words events) 164%nat) = 0 /\
 (Sh.flushD words events = 0 -> norm 32 (read_signal (En.rs words events) 119%nat) = uw (getPc frontier)) /\
 (Sh.flushD words events <> 0 -> norm 32 (read_signal (Sh.drv words events) 130%nat) = uw (getPc frontier)).

Lemma opsok_of D c w i : Decode.decode Decode.RV32I w = Decode.IInstruction i -> PD.legal_instruction i = true ->
 (forall r, r = bitSlice w 15 20 -> norm 32 (read_signal D 204%nat) = uw (formal_register_word c r)) ->
 (forall r, r = bitSlice w 20 25 -> norm 32 (read_signal D 210%nat) = uw (formal_register_word c r)) -> Nx.OpsOK D c i.
Proof. intros Hdec Hleg HA HB. destruct i; try (vm_compute in Hleg; discriminate Hleg); cbn [Nx.OpsOK]; try exact I.
 all: first [ exact I | (destruct (BzTmplIsa.branch_fields w CPUISABranchFamilyEffects.BranchEq _ _ _ Hdec) as [R1 R2]; split; [exact (HA _ R1)|exact (HB _ R2)]) | (destruct (BzTmplIsa.branch_fields w CPUISABranchFamilyEffects.BranchNe _ _ _ Hdec) as [R1 R2]; split; [exact (HA _ R1)|exact (HB _ R2)]) | (destruct (BzTmplIsa.branch_fields w CPUISABranchFamilyEffects.BranchLt _ _ _ Hdec) as [R1 R2]; split; [exact (HA _ R1)|exact (HB _ R2)]) | (destruct (BzTmplIsa.branch_fields w CPUISABranchFamilyEffects.BranchGe _ _ _ Hdec) as [R1 R2]; split; [exact (HA _ R1)|exact (HB _ R2)]) | (destruct (BzTmplIsa.branch_fields w CPUISABranchFamilyEffects.BranchLtu _ _ _ Hdec) as [R1 R2]; split; [exact (HA _ R1)|exact (HB _ R2)]) | (destruct (BzTmplIsa.branch_fields w CPUISABranchFamilyEffects.BranchGeu _ _ _ Hdec) as [R1 R2]; split; [exact (HA _ R1)|exact (HB _ R2)]) | (destruct (Inv.inv_Jalr w _ _ _ Hdec) as [[_ [R1 _]] _]; exact (HA _ R1)) ]. Qed.

Lemma bit_cases (x : Z) : norm 1 x = 0 \/ norm 1 x = 1.
Proof. pose proof (norm_bounds 1 x) as H. cbn in H. lia. Qed.

Theorem front_facts words (HC : PD.check_program words = true) events retired frontier :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> BzTmplInv.Struct (En.rs words events) ->
 BzTmplInv.arch_rel words events retired -> (exists index, PD.AtProgram words index frontier) ->
 (BzTmplInv.rg (En.rs words events) 141 1 = 0 -> BzTmplInv.rg (En.rs words events) 119 32 = uw (getPc frontier)) ->
 Pst.StagesRel J.checked_pc_effect (BzTmplInv.stage_rel words events) 0 retired (BzTmplInv.stages words events) frontier ->
 FrontFacts words events frontier.
Proof.
 intros HE HB HS HAr HAtF H119 HSR.
 destruct (En.env_rise_hyps words events HE HB) as [seed0 [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]].
 pose proof (Ed.prim_driven F.rise (En.rs words events) Hc) as [_ D1].
 pose proof (Co.dsame_holds words events HE HB) as HDS.
 pose proof HS as HSfull.
 set (S := En.rs words events) in *. set (D := Sh.drv words events) in *.
 set (seedD := write_signal S (changed_signal En.F.rise) (new_value En.F.rise)) in *.
 assert (HD' : CombLFP P seedD D) by exact HD.
 destruct HAr as [HRF _].
 assert (HRF' : RFRel (read_signal S 319%nat) (V.isa_view retired)) by exact HRF.
 destruct HS as [HS1 [HS2 [HS3 [HS4 [[HS5a HS5b] [i [Hdec Hleg]]]]]]].
 assert (H153 : norm 1 (read_signal D 153%nat) = 0) by (rewrite (Ci.ctlin_153 seedD D HD'), (Co.d232 _ _ HDS); exact HS5a).
 assert (H151 : norm 1 (read_signal D 151%nat) = 0) by (rewrite (Ci.ctlin_151 seedD D HD'), (Co.d277 _ _ HDS); exact HS5b).
 assert (H142 : norm 1 (read_signal D 142%nat) = 1).
 { rewrite (Ci.ctlin_142 seedD D HD'). change (norm 1 (read_signal (phase_driven_state P F.rise S) 1%nat) = 1). rewrite D1, H1. reflexivity. }
 set (w := BzTmplInv.rg S 140 32) in *.
 assert (Hw : norm 32 (read_signal D 140%nat) = w) by (rewrite (Co.d140 _ _ HDS); reflexivity).
 pose proof (Id.ic_all seedD D w i HD' Hw H153 H151 H142 Hdec Hleg) as HIC.
 pose proof (Sl.sel_all seedD D w i HD' Hw H153 H151 H142 Hdec Hleg) as [HSA HSB].
 pose proof HIC as HIC0. destruct HIC0 as [H163 [H164 _]].
 refine (conj _ (conj H163 (conj H164 _))).
 { intro Hf. exact (Id.ic_fp D i Hleg HIC Hf). }
 destruct (Z.eqb (BzTmplInv.rg S 141 1) 0) eqn:E141.
 - apply Z.eqb_eq in E141. pose proof (HS1 E141) as [Hnop _].
   assert (Hd28 : Decode.decode Decode.RV32I 28691 = Decode.IInstruction (Decode.Andi 0 0 0)) by (vm_compute; reflexivity).
   unfold BzTmplInv.nop_word in Hnop. rewrite Hnop in Hdec. rewrite Hd28 in Hdec. injection Hdec as Hi. subst i.
   destruct HIC as [_ [_ [_ [A _]]]]. cbn in A.
   split.
   + intros _. exact (H119 E141).
   + intro Hf. exfalso. apply Hf. exact A.
 - assert (E141' : BzTmplInv.rg S 141 1 = 1) by (pose proof (norm_bounds 1 (read_signal S 141%nat)) as Hb; unfold BzTmplInv.rg in *; apply Z.eqb_neq in E141; cbn in Hb; lia).
   change (BzTmplInv.stages words events) with ([BzTmplInv.tok S 286 287; BzTmplInv.tok S 250 245] ++ [BzTmplInv.tok S 141 139]) in HSR.
   destruct (Pst.app_split _ _ _ _ _ _ _ HSR) as [c2 [HSR1 HSR2]].
   replace (BzTmplInv.tok S 141 139) with (Some (BzTmplInv.rg S 139 32)) in HSR2 by (unfold BzTmplInv.tok; rewrite E141; reflexivity).
   cbn [length] in HSR2.
   destruct (Pst.sr_some_inv _ _ _ _ _ _ _ HSR2) as [c3 [Heff [HR HSR3]]].
   pose proof (Pst.sr_nil_inv _ _ _ _ _ HSR3) as Hfr. subst c3.
   set (t := BzTmplInv.rg S 139 32) in *.
   unfold BzTmplInv.stage_rel in HR. change (BzTmplInv.StageID words S t c2) in HR.
   destruct HR as [_ [H139 [H140 [H138 Hdom]]]].
   pose proof Hdom as Hdom0. destruct Hdom0 as [HAt Htc].
   assert (HWp : forall k t' c' y, (k < 2)%nat /\ BzTmplInv.stage_rel words events k t' c' -> J.checked_pc_effect t' c' = Some y ->
                forall r, V.isa_view y r = Is.upd (Co.Wpay S (norm 32 (read_signal D 259%nat)) k) r (V.isa_view c' r)).
   { intros k t' c' y [Hk2 HRk] HEf r. destruct k as [|[|k']]; [|  | lia].
     - unfold BzTmplInv.stage_rel in HRk. change (BzTmplInv.StageMEM words S t' c') in HRk.
       destruct HRk as [_ [_ [H283 [_ [_ [Hd' [i' [Hdec' Hm]]]]]]]].
       destruct Hd' as [HAt' Ht']. pose proof (Tr.legal_at words HC t' c' i' (conj HAt' Ht') Hdec') as Hleg'.
       pose proof (Is.isa_eff words HC t' c' y i' HAt' Ht' HEf Hdec' r) as Heff'.
       cbn [Co.Wpay]. rewrite (Tr.W0_eq words S c' t' i' Hleg' Hm H283 Hdec'). exact Heff'.
     - unfold BzTmplInv.stage_rel in HRk. change (BzTmplInv.StageEX words S t' c') in HRk.
       destruct HRk as [_ [_ [_ [H244' [_ [_ [Hd' [i' [Hdec' Hex']]]]]]]]].
       destruct Hd' as [HAt' Ht']. pose proof (Tr.legal_at words HC t' c' i' (conj HAt' Ht') Hdec') as Hleg'.
       pose proof (Is.isa_eff words HC t' c' y i' HAt' Ht' HEf Hdec' r) as Heff'.
       cbn [Co.Wpay]. rewrite (Tr.W1_eq words S c' t' i' Hleg' Hex' H244' Hdec' (norm 32 (read_signal D 259%nat)) (fun Hd' => Cl.exval_all seedD D S c' i' Hleg' Hd' HD' HDS Hex')). exact Heff'. }
   assert (HSR' : Pst.StagesRel J.checked_pc_effect (fun k t' c' => (k < 2)%nat /\ BzTmplInv.stage_rel words events k t' c') 0 retired [BzTmplInv.tok S 286 287; BzTmplInv.tok S 250 245] c2).
   { refine (Pst.relabel J.checked_pc_effect (BzTmplInv.stage_rel words events) _ 0 _ 0 retired c2 HSR1 _).
     intros k t' c' _ Hk2 HRk. cbn [length] in Hk2. cbv beta. rewrite Nat.sub_0_r. split; [lia|exact HRk]. }
   pose proof (Pst.forwarding_correct J.checked_pc_effect V.isa_view Z.eqb _ (Co.Wpay S (norm 32 (read_signal D 259%nat))) 0 retired _ c2 HSR' HWp) as Hfw.
   assert (Hfw2 : forall r, uw (formal_register_word c2 r) = Is.upd (Co.W1 S (norm 32 (read_signal D 259%nat))) r (Is.upd (Co.W0 S) r (V.isa_view retired r))).
   { intro r. rewrite (V.view_formal c2 r), (Hfw r). apply Co.fwd_two. exact HSfull. }
   assert (HAf : forall r, r = bitSlice w 15 20 -> norm 32 (read_signal D 204%nat) = uw (formal_register_word c2 r)).
   { intros r Hr.
     assert (Hr' : norm 5 (read_signal D 146%nat) = r).
     { rewrite (Lk.link_rs1 seedD D HD'), (Co.d140 _ _ HDS), Hr, (V.bs_norm w 15 20 ltac:(lia) ltac:(lia)). reflexivity. }
     rewrite (Hfw2 r). exact (Co.opnd_A seedD D S retired r HD' HDS HRF' HSA Hr'). }
   assert (HBf : forall r, r = bitSlice w 20 25 -> norm 32 (read_signal D 210%nat) = uw (formal_register_word c2 r)).
   { intros r Hr.
     assert (Hr' : norm 5 (read_signal D 147%nat) = r).
     { rewrite (Lk.link_rs2 seedD D HD'), (Co.d140 _ _ HDS), Hr, (V.bs_norm w 20 25 ltac:(lia) ltac:(lia)). reflexivity. }
     rewrite (Hfw2 r). exact (Co.opnd_B seedD D S retired r HD' HDS HRF' HSB Hr'). }
   pose proof (opsok_of D c2 w i Hdec Hleg HAf HBf) as HOps.
   destruct (J.checked_pc_effect_sound t c2 frontier Heff) as [Hrun _].
   assert (Ht : norm 32 (read_signal D 139%nat) = t) by (rewrite (Co.d139 _ _ HDS); exact H139).
   assert (Hiw : BzTmplInv.iword words t = w) by (symmetry; exact H140).
   destruct (Nx.next_pc seedD D words HC t c2 frontier i w HD' Hw Ht Hdec Hiw HIC HOps HAt Htc Hrun) as [NP1 NP2].
   split.
   + intro Hf. assert (HG : BzTmplInv.rg S 119 32 = uw (getPc frontier)) by (rewrite (HS4 E141'); symmetry; exact (NP1 Hf)). exact HG.
   + intro Hf. symmetry. exact (NP2 Hf).
Qed.
End FF.
End BzTmplFrontFacts.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplFrontFacts.opsok_of.
Print Assumptions BzTmplFrontFacts.front_facts.
