(** Bzeeno goal_arch, RF and RAM layer (hand-written core, tools/cpu_tmpl_bzgate.py).
    One cycle `events ++ [rise] ++ [fall]` from a clock boundary: the RF bank after the fall is the old bank view with the
    MEM token's write (old EX/MEM registers 279/283/284, mem2reg 277 = 0) applied, or unchanged when 279 = 0 or rd = 0;
    the RAM root 327 is unchanged when the old EX/MEM wmem 278 = 0.
    Reused low-level facts: none beyond the accepted template modules (BzTmplPhase uses Phase.original_phase, logged there).
    proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVRootProjection Lang.ExtendedSVStallFlush Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankOperand Lang.ExtendedSVSeqTree
 Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase GeneratedRuntimeInput.ConfiguredAST
 GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment GeneratedClockCycleJoint.CycleJoint
 TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv TmplBzPhase.BzTmplPhase TmplBzXfer.BzTmplXfer TmplBzFrame.BzTmplFrame
 TmplBzRFFall.BzTmplRFFall TmplBzRam.BzTmplRam TmplBzArchCopy.BzTmplArchCopy.
Import ListNotations ExtendedSV ExtendedSVRootProjection ExtendedSVStallFlush ExtendedSVSeqTree ExtendedSVWordInvariant ExtendedSVBankAlignment ExtendedSVBankOperand ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplArchRF.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Module Ph := TmplBzPhase.BzTmplPhase.BzTmplPhase.
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Xf := TmplBzXfer.BzTmplXfer.BzTmplXfer.
Module Fr := TmplBzFrame.BzTmplFrame.BzTmplFrame.
Module RFF := TmplBzRFFall.BzTmplRFFall.BzTmplRFFall.
Module Rm := TmplBzRam.BzTmplRam.BzTmplRam.
Module Cp := TmplBzArchCopy.BzTmplArchCopy.BzTmplArchCopy.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.

Lemma bit_cases (x : Z) : norm 1 x = 0 \/ norm 1 x = 1.
Proof. pose proof (norm_bounds 1 x) as H. cbn in H. lia. Qed.
Lemma guard_ne d : eval_expr d (EBinary 1 BAnd (EVar 1 315%nat) (EBinary 1 BNeq (EConst 5 0) (EVar 5 314%nat))) <> 0 <->
 (norm 1 (read_signal d 315%nat) = 1 /\ norm 5 (read_signal d 314%nat) <> 0).
Proof. cbn [eval_expr]. change (norm 5 0) with 0.
 destruct (bit_cases (read_signal d 315%nat)) as [H|H]; rewrite H.
 - assert (L : norm 1 (Z.land 0 (norm 1 (boolz (negb (Z.eqb 0 (norm 5 (read_signal d 314%nat))))))) = 0) by (rewrite Z.land_0_l; reflexivity).
   rewrite L. split; [intro X; exfalso; apply X; reflexivity|intros [X _]; discriminate X].
 - destruct (Z.eqb 0 (norm 5 (read_signal d 314%nat))) eqn:E.
   + apply Z.eqb_eq in E. assert (L : norm 1 (Z.land 1 (norm 1 (boolz (negb true)))) = 0) by (vm_compute; reflexivity).
     rewrite L. split; [intro X; exfalso; apply X; reflexivity|intros [_ X]; exfalso; apply X; lia].
   + apply Z.eqb_neq in E. assert (L : norm 1 (Z.land 1 (norm 1 (boolz (negb false)))) = 1) by (vm_compute; reflexivity).
     rewrite L. split; [intros _; split; [reflexivity|lia]|intros _ X; discriminate X].
Qed.

Section Cycle.
Variable words : list Z.
Local Notation rs := (En.rs words).


(** Facts of the cycle at the falling event, from a clock boundary. *)
Lemma rf_cycle events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (rs events) ->
 forall view, RFRel (read_signal (rs events) 319%nat) view ->
 (norm 1 (read_signal (rs events) 279%nat) = 1 -> norm 5 (read_signal (rs events) 283%nat) <> 0 -> norm 1 (read_signal (rs events) 277%nat) = 0 ->
   RFRel (read_signal (Ph.fall_state words events) 319%nat)
     (fun i => if Z.eqb i (norm 5 (read_signal (rs events) 283%nat)) then norm 32 (read_signal (rs events) 284%nat) else view i)) /\
 ((norm 1 (read_signal (rs events) 279%nat) = 0 \/ norm 5 (read_signal (rs events) 283%nat) = 0) ->
   RFRel (read_signal (Ph.fall_state words events) 319%nat) view).
Proof.
 intros HE HB view HR.
 destruct (Ph.cycle_hyps words events HE HB) as [[seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]] [[seed2 [Hc2 [Hv2 [H02 [H12 [HW2 [HL2 HD2]]]]]]] _]].
 pose proof (conj Hc (conj Hv (conj H0 (conj H1 (conj HW (conj HL HD)))))) as HH.
 set (mid := Ph.rise_state words events) in *.
 assert (Hmid : mid = PhaseSemantics P F.rise (rs events)) by exact (Ph.rise_state_eq words events).
 assert (R319 : read_signal mid 319%nat = read_signal (rs events) 319%nat).
 { rewrite Hmid. exact (Fr.rise_frame_319 F.rise (rs events) seed Hc Hv H0 H1 HW HL HD). }
 assert (M303 : norm 1 (read_signal mid 303%nat) = norm 1 (read_signal (rs events) 277%nat)) by (rewrite Hmid; exact (Xf.xfer_303 F.rise (rs events) seed HH)).
 assert (M304 : norm 1 (read_signal mid 304%nat) = norm 1 (read_signal (rs events) 279%nat)) by (rewrite Hmid; exact (Xf.xfer_304 F.rise (rs events) seed HH)).
 assert (M305 : norm 5 (read_signal mid 305%nat) = norm 5 (read_signal (rs events) 283%nat)) by (rewrite Hmid; exact (Xf.xfer_305 F.rise (rs events) seed HH)).
 assert (M306 : norm 32 (read_signal mid 306%nat) = norm 32 (read_signal (rs events) 284%nat)) by (rewrite Hmid; exact (Xf.xfer_306 F.rise (rs events) seed HH)).
 set (Df := phase_driven_state P F.fall mid) in *.
 set (seedf := write_signal mid (changed_signal F.fall) (new_value F.fall)) in *.
 assert (Hne : forall R, R <> 0%nat -> changed_signal F.fall <> R) by (intros R HR0; rewrite Hc2; auto).
 assert (U : forall R, comb_root_unwrittenb P R = true -> R <> 0%nat -> read_signal Df R = read_signal mid R).
 { intros R Hu HR0. exact (driven_unchanged P F.fall mid R Hu (Hne R HR0)). }
 destruct (TmplBzEdge.BzTmplEdge.BzTmplEdge.prim_driven F.fall mid Hc2) as [_ D1]. fold Df in D1.
 split.
 - intros H279 H283 H277.
   assert (G : eval_expr Df (EBinary 1 BAnd (EVar 1 315%nat) (EBinary 1 BNeq (EConst 5 0) (EVar 5 314%nat))) <> 0).
   { apply guard_ne. split.
     + rewrite (Cp.ctch_315 seedf Df HD2), (U 304%nat Fr.comb_unw_304 ltac:(discriminate)), M304. exact H279.
     + rewrite (Cp.ctch_314 seedf Df HD2), (U 305%nat Fr.comb_unw_305 ltac:(discriminate)), M305. exact H283. }
   assert (G1 : eval_expr Df (EVar 1 311%nat) <> 0).
   { cbn [eval_expr]. rewrite (Cp.ctch_311 seedf Df HD2), D1, H12. vm_compute. discriminate. }
   assert (Hd316 : norm 32 (read_signal Df 316%nat) = norm 32 (read_signal (rs events) 284%nat)).
   { rewrite (Cp.ctch_316 seedf Df HD2), (Cp.eq_w68 seedf Df HD2). unfold Cp.orig_w68. cbn [eval_expr].
     rewrite (Cp.ctch_109 seedf Df HD2), (Cp.ctch_113 seedf Df HD2), (Cp.ctch_108 seedf Df HD2).
     rewrite (U 303%nat Fr.comb_unw_303 ltac:(discriminate)), (U 307%nat Fr.comb_unw_307 ltac:(discriminate)), (U 306%nat Fr.comb_unw_306 ltac:(discriminate)).
     rewrite M303, H277. cbn. rewrite !norm_idempotent. rewrite M306. reflexivity. }
   pose proof (RFF.rf_rel_step_fall F.fall mid seed2 view Hc2 Hv2 H02 H12 HW2 HL2 HD2 G1 G ltac:(rewrite R319; exact HR)) as Hrel.
   rewrite Ph.fall_state_eq. 
   cbn [eval_expr] in Hrel. fold Df in Hrel. rewrite Hd316 in Hrel.
   rewrite (Cp.ctch_314 seedf Df HD2), (U 305%nat Fr.comb_unw_305 ltac:(discriminate)), M305 in Hrel.
   rewrite norm_idempotent in Hrel. exact Hrel.
 - intros Hoff.
   assert (G : eval_expr Df (EBinary 1 BAnd (EVar 1 315%nat) (EBinary 1 BNeq (EConst 5 0) (EVar 5 314%nat))) = 0).
   { destruct (Z.eq_dec (eval_expr Df (EBinary 1 BAnd (EVar 1 315%nat) (EBinary 1 BNeq (EConst 5 0) (EVar 5 314%nat)))) 0) as [E|E]; [exact E|].
     exfalso. apply guard_ne in E as [E1 E2].
     rewrite (Cp.ctch_315 seedf Df HD2), (U 304%nat Fr.comb_unw_304 ltac:(discriminate)), M304 in E1.
     rewrite (Cp.ctch_314 seedf Df HD2), (U 305%nat Fr.comb_unw_305 ltac:(discriminate)), M305 in E2.
     destruct Hoff as [Hoff|Hoff]; congruence. }
   assert (G1 : eval_expr Df (EVar 1 311%nat) <> 0).
   { cbn [eval_expr]. rewrite (Cp.ctch_311 seedf Df HD2), D1, H12. vm_compute. discriminate. }
   rewrite Ph.fall_state_eq.
   exact (RFF.rf_rel_off_fall F.fall mid seed2 view Hc2 Hv2 H02 H12 HW2 HL2 HD2 G1 G ltac:(rewrite R319; exact HR)).
Qed.

(** RAM root unchanged when the old EX/MEM wmem is 0. *)
Lemma ram_cycle events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (rs events) -> norm 1 (read_signal (rs events) 278%nat) = 0 ->
 read_signal (Ph.fall_state words events) 327%nat = read_signal (rs events) 327%nat.
Proof.
 intros HE HB H278.
 destruct (Ph.cycle_hyps words events HE HB) as [[seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]] [[seed2 [Hc2 [Hv2 [H02 [H12 [HW2 [HL2 HD2]]]]]]] _]].
 assert (Hz : norm 1 (read_signal (phase_driven_state P F.rise (rs events)) 321%nat) = 0).
 { rewrite (Cp.ctch_321 _ _ HD). rewrite (driven_unchanged P F.rise (rs events) 278%nat Fr.comb_unw_278 ltac:(rewrite Hc; discriminate)). exact H278. }
 pose proof (Rm.ram_hold F.rise (rs events) seed Hc Hv H0 H1 HW HL HD Hz) as Hram.
 rewrite Ph.fall_state_eq. 
 rewrite (Fr.fall_frame_327 F.fall (Ph.rise_state words events) seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2).
 rewrite Ph.rise_state_eq. exact Hram.
Qed.
End Cycle.
End BzTmplArchRF.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplArchRF.guard_ne.
Print Assumptions BzTmplArchRF.rf_cycle.
Print Assumptions BzTmplArchRF.ram_cycle.
