#!/usr/bin/env python3
"""D step of the Bzeeno template route: generic staged obligations (mode plan, tools/cpu_pipeline_skeleton.py) instantiated with the INV of
BzTmplInv (Runtime = list Event, sd_step = JumpITree.actual_cycle, sd_commits = JumpITree.actual_observer words, token = pc).  The rank is a
Section variable (to be supplied by the rank module).  PROVED here: goal_startup, goal_observer.  The other goals are the premises of `assembled`.
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_pipeline_skeleton as sk

PROVED = r'''
Local Notation R := BzTmplInv.rg.
Lemma envs_of_physical (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true) s retired frontier:
 staged_physical (design words HC) s retired frontier ->
 Forall GeneratedWriteValidityBoot.WriteValidityBoot.Environment s /\ GeneratedClockCycleJoint.CycleJoint.ClockBoundary (BzTmplEnv.rs words s).
Proof. intros [_ [Hf _]]. cbn[design sd_front] in Hf. unfold BzTmplInv.front_rel in Hf. destruct Hf as [HE [HB _]]. split; assumption. Qed.
Lemma startup_proved (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true): goal_startup words HC.
Proof. unfold goal_startup. reflexivity. Qed.
Lemma shape_proved (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true): goal_shape words HC.
Proof. unfold goal_shape. intros s retired frontier HP.
 destruct (envs_of_physical words HC s retired frontier HP) as [HE HB].
 pose proof HP as [_ [Hf _]]. cbn[design sd_front] in Hf. unfold BzTmplInv.front_rel in Hf. destruct Hf as [_ [_ [HS _]]].
 pose proof (Forall_impl _ (fun ev H => proj1 H) HE) as HC2.
 pose proof (BzTmplNState.n_one_state words s HC2 HB HS) as Hn.
 pose proof (BzTmplShape.stages_after_cycle words s HC2 HB Hn) as Hsh.
 cbn[design sd_stages sd_step]. unfold plan_shape. unfold BzTmplInv.stages. cbn zeta.
 destruct (Z.eqb (BzTmplShape.flushD words s) 0) eqn:Ef; cbn[shape_post app tl]; unfold JumpITree.actual_cycle;
 exact Hsh. Qed.
Lemma observer_proved (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true): goal_observer words HC.
Proof. unfold goal_observer. intros s retired frontier HP.
 destruct (envs_of_physical words HC s retired frontier HP) as [HE HB].
 destruct (BzTmplPhase.cycle_hyps words s (Forall_impl _ (fun ev H => proj1 H) HE) HB) as [[seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]] _].
 set (D := phase_driven_state BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program GeneratedSeedBoot.FrozenEnvironment.rise (BzTmplEnv.rs words s)).
 pose proof (BzTmplValid.valid_308 GeneratedSeedBoot.FrozenEnvironment.rise (BzTmplEnv.rs words s) seed (norm 1 (read_signal D 157%nat)) (norm 1 (read_signal D 156%nat)) Hc Hv H0 H1 HW HL HD eq_refl eq_refl) as V308.
 pose proof (BzTmplXfer.xfer_309 GeneratedSeedBoot.FrozenEnvironment.rise (BzTmplEnv.rs words s) seed (conj Hc (conj Hv (conj H0 (conj H1 (conj HW (conj HL HD))))))) as X309.
 cbn[design sd_commits sd_stages]. unfold JumpITree.actual_observer.
 change (JumpITree.runtime_state words (s ++ [GeneratedCapturedHistoryBoot.CapturedHistoryBoot.F.rise])) with (BzTmplPhase.rise_state words s).
 rewrite BzTmplPhase.rise_state_eq. rewrite V308, X309.
 unfold plan_shape, BzTmplInv.stages, BzTmplInv.tok, BzTmplInv.rg. cbn zeta.
 destruct (Z.eqb (BzTmplShape.flushD words s) 0); cbn[shape_retiring app hd opt];
 destruct (Z.eqb (norm 1 (read_signal (BzTmplEnv.rs words s) 286%nat)) 0); unfold observe; cbn[opt]; reflexivity. Qed.
'''

NEWL = r'''
Lemma rank_proved (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true): goal_rank words HC.
Proof. unfold goal_rank, OrderedWaitDecreases. intros s isa [frontier [HP _]] HSil.
 destruct (envs_of_physical words HC s isa frontier HP) as [HE HB].
 pose proof HP as [_ [Hf _]]. cbn[design sd_front] in Hf. unfold BzTmplInv.front_rel in Hf. destruct Hf as [_ [_ [HS _]]].
 pose proof (Forall_impl _ (fun ev H => proj1 H) HE) as HC2.
 pose proof (BzTmplNState.n_one_state words s HC2 HB HS) as Hn.
 destruct HS as [Hidle _].
 pose proof (BzTmplIfId.rank_premises_of_idle words s HC2 HB Hidle Hn) as HRP.
 assert (HS308 : norm 1 (read_signal (BzTmplEnv.rs words (s ++ [GeneratedSeedBoot.FrozenEnvironment.rise])) 308%nat) = 0).
 { unfold JumpITree.actual_observer in HSil.
   destruct (Z.eqb (norm 1 (read_signal (JumpITree.runtime_state words (s ++ [GeneratedCapturedHistoryBoot.CapturedHistoryBoot.F.rise])) 308%nat)) 0) eqn:E;
   [apply Z.eqb_eq in E; exact E | discriminate]. }
 exact (BzTmplRank.tmpl_rank_decreases words s HC2 HB HRP HS308). Qed.
Lemma init_view (words:list Z) i : CPUISARegView.isa_view (JumpITree.initial words) i = 0.
Proof. unfold CPUISARegView.isa_view, CPUISARegView.regs_view. cbn. destruct (Z.eqb i 0); [reflexivity|]. rewrite map.get_empty. reflexivity. Qed.
Lemma boot_proved (words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true): goal_boot words HC.
Proof. unfold goal_boot. set (img := ExtendedSVPackedROM.pack words).
 assert (Hrs : BzTmplEnv.rs words [] = GeneratedSeedBoot.FrozenEnvironment.boot img) by reflexivity.
 assert (H141 := BzTmplReset.boot_valid_141 img). assert (H250 := BzTmplReset.boot_valid_250 img). assert (H286 := BzTmplReset.boot_valid_286 img).
 refine (staged_initial (design words HC) [] (JumpITree.initial words) 3%nat _ _ _).
 - cbn[design sd_stages]. unfold BzTmplInv.stages, BzTmplInv.tok, BzTmplInv.rg. cbn zeta. rewrite Hrs. rewrite H141, H250, H286. reflexivity.
 - cbn[design sd_arch]. unfold BzTmplInv.arch_rel. rewrite Hrs. split; [|reflexivity].
   assert (Hv : CPUISARegView.isa_view (JumpITree.initial words) = (fun _ => 0)) by (apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intro i; apply init_view).
   rewrite Hv. exact (BzTmplReset.boot_rf img).
 - cbn[design sd_front]. unfold BzTmplInv.front_rel. rewrite Hrs. cbv zeta.
   split; [constructor|]. split; [exact (BzTmplReset.boot_clock_boundary img)|]. split.
   + unfold BzTmplInv.Struct, BzTmplInv.rg. split; [exact (BzTmplIfId.ifid_idle_boot img)|]. split.
     * intros _. exact (conj (BzTmplReset.boot_reset_244 img) (conj (BzTmplReset.boot_reset_233 img) (BzTmplReset.boot_reset_232 img))).
     * split.
       { intros _. exact (conj (BzTmplReset.boot_reset_283 img) (conj (BzTmplReset.boot_reset_278 img) (BzTmplReset.boot_reset_277 img))). }
       split; [intro H; rewrite H141 in H; discriminate|]. split; [exact (conj (BzTmplReset.boot_reset_232 img) (BzTmplReset.boot_reset_277 img))|].
       rewrite (BzTmplReset.boot_reset_140 img). eexists; split; vm_compute; reflexivity.
   + split; [exists 0%nat; exact (CPUJumpFamilyProgramExecution.checked_original_initial words HC)|].
     intros _. unfold BzTmplInv.rg. rewrite (BzTmplReset.boot_reset_119 img).
     unfold JumpITree.initial. cbn [FormalSpec.initial_state getPc]. symmetry. change (word.unsigned (@word.of_Z 32 word 0) = 0). rewrite word.unsigned_of_Z. reflexivity. Qed.
'''


def build():
    m = dict(design='Bzeeno (template route, tools/cpu_tmpl_bzdstep.py)', module='BzTmplStep', mode='plan',
             requires=['Lang.ExtendedSV', 'Ex.External.CPUProgramROM', 'Ex.External.CPUJumpFamilyProgramDomain', 'Ex.External.CPUISARegView',
                       'GeneratedRuntimeInput.ConfiguredAST', 'GeneratedWriteValidityBoot.WriteValidityBoot', 'GeneratedClockCycleJoint.CycleJoint',
                       'GeneratedSeedBoot.FrozenEnvironment', 'GeneratedCapturedHistoryBoot.CapturedHistoryBoot',
                       'TmplBzEnv.BzTmplEnv', 'TmplBzShape.BzTmplShape', 'TmplBzRank.BzTmplRank', 'TmplBzIfId.BzTmplIfId', 'TmplBzReset.BzTmplReset', 'Ex.External.CPUJumpFamilyProgramExecution', 'Lang.ExtendedSVPackedROM', 'Lang.ExtendedSVWordInvariant', 'riscv.Spec.Decode', 'Ex.External.CPUISARegView', 'TmplBzNState.BzTmplNState', 'TmplBzPhase.BzTmplPhase', 'TmplBzValid.BzTmplValid', 'TmplBzXfer.BzTmplXfer', 'TmplBzInv.BzTmplInv',
                       'GeneratedJumpITree.JumpITree', 'coqutil.Word.Interface', 'coqutil.Word.Bitwidth', 'coqutil.Map.Interface', 'coqutil.Byte', 'riscv.Utility.Utility'],
             imports=['ExtendedSV'], module_prelude=[], prelude=['Require Coq.Logic.FunctionalExtensionality.', 'Local Open Scope Z_scope.'],
             params='(words:list Z)(HC:CPUJumpFamilyProgramDomain.check_program words=true)', args='words HC', runtime='list Event', token='Z',
             context='Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}\n {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.',
             fields=dict(step='JumpITree.actual_cycle', commits='JumpITree.actual_observer words', effect='checked_pc_effect', pc='fun pc=>pc',
                         effect_sound='checked_pc_effect_sound', stages='BzTmplInv.stages words', arch='BzTmplInv.arch_rel words',
                         front='BzTmplInv.front_rel words', stage='BzTmplInv.stage_rel words'),
             plan_shape='fun events=>if Z.eqb (BzTmplShape.flushD words events) 0 then Advance (Some (BzTmplInv.rg (BzTmplEnv.rs words events) 119 32)) else Advance None',
             plan_next='fun (events:list Event) (_:FormalSpec.State) (f:FormalSpec.State)=>if Z.eqb (BzTmplShape.flushD words events) 0 then snd (FormalSpec.run1 f) else f',
             rank='(@BzTmplRank.tmpl_rank_ev FormalSpec.State words)', boot='[]', initial='JumpITree.initial words', reset='[]', proof_author='LLM-generated: Claude Code (claude-sonnet-5-5)')
    body = sk.skeleton(m)
    k = body.index('(** All goals together give the refinement from actual reset. *)')
    body = body[:k] + PROVED + NEWL + '\n' + body[k:]
    body = body.replace('Print Assumptions BzTmplStep.assembled.',
                        'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\nPrint Assumptions BzTmplStep.assembled.\nPrint Assumptions BzTmplStep.startup_proved.\nPrint Assumptions BzTmplStep.observer_proved.\nPrint Assumptions BzTmplStep.shape_proved.\nPrint Assumptions BzTmplStep.rank_proved.\nPrint Assumptions BzTmplStep.boot_proved.')
    return body


if __name__ == '__main__':
    Path(sys.argv[1]).write_text(build())
