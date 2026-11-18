#!/usr/bin/env python3
"""Bzeeno transport, assembly (module BzTmplTrans): the per-index transport of the staged INV over one cycle (shape_transport_ctx for the
Advance shape, which is the only shape the plan uses): EX -> MEM (exval/exmem) and ID -> EX (controller outputs, forwarded operands
with CPUPipelineStages.forwarding_correct, immediate, compare bit).  Hand-written glue over the generated per-class lemmas.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'

TEXT = r"""(** Bzeeno transport (goal_transport core), tools/cpu_tmpl_bztrans_main.py.  proof_author: @AUTHOR@; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBankOperand
 GeneratedClockCycleJoint.CycleJoint GeneratedRuntimeInput.ConfiguredAST GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment
 TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv TmplBzPhase.BzTmplPhase TmplBzInv.BzTmplInv TmplBzShape.BzTmplShape TmplBzNState.BzTmplNState TmplBzCtlIn.BzTmplCtlIn
 TmplBzLink.BzTmplLink TmplBzTrIsa.BzTmplTrIsa TmplBzTrCore.BzTmplTrCore TmplBzTrCls.BzTmplTrCls TmplBzDisp2.BzTmplDisp2
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUPipelineQueue Ex.External.CPUPipelineStages Ex.External.CPUPipelineStagesContext
 Ex.External.CPUGeneratedJointITree Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUISARegView Ex.External.CV32E40PReq40StateRel
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Spec.Decode.
Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase ExtendedSVBankOperand CV32E40PReq40StateRel
 CPUGeneratedJointTemplate CPUPipelineQueue.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplTrans.
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
Module Dp := TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Module PD := Ex.External.CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.
Module J := Ex.External.CPUGeneratedJointITree.CPUGeneratedJointITree.
Module V := Ex.External.CPUISARegView.CPUISARegView.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Module Pst := Ex.External.CPUPipelineStages.CPUPipelineStages.
Module Psc := Ex.External.CPUPipelineStagesContext.CPUPipelineStagesContext.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
Section Main.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Local Notation uw := word.unsigned.
Variable words : list Z.
Hypothesis HC : PD.check_program words = true.

(** the instruction at a token's cut *)
Lemma decode_at t (c : FormalSpec.State) : BzTmplInv.Dom words t c -> exists i, Decode.decode Decode.RV32I (BzTmplInv.iword words t) = Decode.IInstruction i /\ PD.legal_instruction i = true.
Proof. intros [HAt _]. destruct (PD.checked_entry words (Z.to_nat (t / 4)) HC (proj1 HAt)) as [i [Hd [_ [Hl _]]]].
 exists i. split; [|exact Hl]. unfold BzTmplInv.iword. rewrite (Is.word_norm words _ HC (proj1 HAt)). exact Hd. Qed.
Lemma legal_at t (c : FormalSpec.State) i : BzTmplInv.Dom words t c -> Decode.decode Decode.RV32I (BzTmplInv.iword words t) = Decode.IInstruction i -> PD.legal_instruction i = true.
Proof. intros Hd H. destruct (decode_at t c Hd) as [i0 [H0 Hl]]. rewrite H in H0. injection H0 as <-. exact Hl. Qed.

Lemma ExCl_w (S : State) (c : FormalSpec.State) i : PD.legal_instruction i = true -> BzTmplInv.ExCl S c i ->
 norm 1 (read_signal S 236%nat) = if Is.dwr i then 1 else 0.
Proof. intros Hleg H. destruct i; try (vm_compute in Hleg; discriminate Hleg); cbn [BzTmplInv.ExCl] in H;
 repeat match goal with H : _ /\ _ |- _ => destruct H | H : exists _, _ |- _ => let b := fresh "b" in destruct H as [b H] end; cbn [Is.dwr]; assumption. Qed.
Lemma MemCl_dest (S : State) (c : FormalSpec.State) i : Is.dwr i = true -> BzTmplInv.MemCl S c i -> norm 1 (read_signal S 279%nat) = 1 /\ norm 32 (read_signal S 284%nat) = uw (Is.dval c i).
Proof. destruct i; cbn [Is.dwr]; try discriminate; intros _ H; exact H. Qed.
Lemma MemCl_br (S : State) (c : FormalSpec.State) i : Is.dwr i = false -> PD.legal_instruction i = true -> BzTmplInv.MemCl S c i -> norm 1 (read_signal S 279%nat) = 0.
Proof. destruct i; cbn [Is.dwr]; intros Hd Hleg H; try discriminate Hd; try (vm_compute in Hleg; discriminate Hleg); exact H. Qed.
Lemma MemCl_mk (S : State) (c : FormalSpec.State) i : PD.legal_instruction i = true ->
 (Is.dwr i = true -> norm 1 (read_signal S 279%nat) = 1 /\ norm 32 (read_signal S 284%nat) = uw (Is.dval c i)) ->
 (Is.dwr i = false -> norm 1 (read_signal S 279%nat) = 0) -> BzTmplInv.MemCl S c i.
Proof. intros Hleg H1 H0. destruct i; try (vm_compute in Hleg; discriminate Hleg); first [ exact (H1 eq_refl) | exact (H0 eq_refl) ]. Qed.

(** EX -> MEM for one token *)
Lemma exmem seed (D S S1 : State) (c : FormalSpec.State) i : PD.legal_instruction i = true -> CombLFP P seed D -> Co.DSame D S -> Co.Post S D S1 ->
 BzTmplInv.ExCl S c i -> BzTmplInv.MemCl S1 c i.
Proof. intros Hleg HL HS HP Hex. pose proof (ExCl_w S c i Hleg Hex) as Hw. apply MemCl_mk; [exact Hleg| |].
 - intro Hd. rewrite Hd in Hw. split.
   + rewrite (Co.p279 _ _ _ HP). exact Hw.
   + rewrite (Co.p284 _ _ _ HP). pose proof (Cl.exval_all seed D S c i Hleg Hd HL HS Hex) as Hv. exact Hv.
 - intro Hd. rewrite Hd in Hw. rewrite (Co.p279 _ _ _ HP). exact Hw. Qed.

(** write payloads of the older stages equal the ISA register effect of their token *)
Lemma W0_eq (S : State) (c : FormalSpec.State) t i : PD.legal_instruction i = true -> BzTmplInv.MemCl S c i -> norm 5 (read_signal S 283%nat) = bitSlice (BzTmplInv.iword words t) 7 12 ->
 Decode.decode Decode.RV32I (BzTmplInv.iword words t) = Decode.IInstruction i -> Co.W0 S = Is.dpay c i.
Proof. intros Hleg Hm H283 Hdec. unfold Is.dpay. destruct (Is.dwr i) eqn:Hd.
 - destruct (MemCl_dest S c i Hd Hm) as [H279 H284]. pose proof (Cl.rd_inv _ i Hdec Hd) as Hrd.
   unfold Co.W0. rewrite H279, H283, <- Hrd, H284. rewrite Co.n50. unfold Is.wr.
   rewrite (Z.eqb_sym 0 (Is.drd i)). destruct (Z.eqb (Is.drd i) 0); reflexivity.
 - pose proof (MemCl_br S c i Hd Hleg Hm) as H279. unfold Co.W0. rewrite H279. reflexivity. Qed.
Lemma W1_eq (S : State) (c : FormalSpec.State) t i : PD.legal_instruction i = true -> BzTmplInv.ExCl S c i -> norm 5 (read_signal S 244%nat) = bitSlice (BzTmplInv.iword words t) 7 12 ->
 Decode.decode Decode.RV32I (BzTmplInv.iword words t) = Decode.IInstruction i -> forall vex, (Is.dwr i = true -> vex = uw (Is.dval c i)) -> Co.W1 S vex = Is.dpay c i.
Proof. intros Hleg Hex H244 Hdec vex Hv. pose proof (ExCl_w S c i Hleg Hex) as Hw. unfold Is.dpay. destruct (Is.dwr i) eqn:Hd.
 - pose proof (Cl.rd_inv _ i Hdec Hd) as Hrd. unfold Co.W1. rewrite Hw, H244, <- Hrd, (Hv eq_refl). rewrite Co.n50. unfold Is.wr.
   rewrite (Z.eqb_sym 0 (Is.drd i)). destruct (Z.eqb (Is.drd i) 0); reflexivity.
 - unfold Co.W1. rewrite Hw. reflexivity. Qed.
"""

MAIN = r"""
Local Notation Cyc events := ((events ++ [F.rise]) ++ [F.fall]).

Theorem transport_core events retired (adm : option Z) :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> BzTmplInv.Struct (En.rs words events) ->
 BzTmplInv.arch_rel words events retired ->
 Psc.shape_transport_ctx J.checked_pc_effect (Pst.Advance adm) (BzTmplInv.stage_rel words events) (BzTmplInv.stage_rel words (Cyc events)) retired (BzTmplInv.stages words events).
Proof.
 intros HE HB HS HAr.
 pose proof (BzTmplNState.n_one_state words events HE HB HS) as Hn.
 assert (Hn' : Sh.stallD words events = 1) by exact Hn.
 pose proof (Co.post_holds words events HE HB Hn') as HP.
 pose proof (Co.dsame_holds words events HE HB) as HDS.
 destruct (En.env_rise_hyps words events HE HB) as [seed0 [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]].
 pose proof (Ed.prim_driven F.rise (En.rs words events) Hc) as [_ D1].
 change (Co.Post (En.rs words events) (Sh.drv words events) (Ph.fall_state words events)) in HP.
 set (S := En.rs words events) in *. set (D := Sh.drv words events) in *.
 set (S1 := Ph.fall_state words events) in *.
 set (seedD := write_signal S (changed_signal En.F.rise) (new_value En.F.rise)) in *.
 assert (HD' : CombLFP P seedD D) by exact HD.
 destruct HAr as [HRF _].
 assert (HRF' : RFRel (read_signal S 319%nat) (V.isa_view retired)) by exact HRF.
 destruct HS as [HS1 [HS2 [HS3 [HS4 [[HS5a HS5b] HS6]]]]].
 pose proof (conj HS1 (conj HS2 (conj HS3 (conj HS4 (conj (conj HS5a HS5b) HS6))))) as HSfull.
 unfold Psc.shape_transport_ctx, Psc.TransportFrom. intros l1 t l2 c Hold Hk HSR HR.
 destruct l1 as [|a l1]; [cbn in Hk; lia|].
 destruct l1 as [|b l1].
 - (* EX -> MEM *)
   cbn [length Nat.sub] in *. unfold BzTmplInv.stage_rel in HR |- *. cbn [length Nat.sub] in *.
   change (BzTmplInv.StageMEM words S1 t c). change (BzTmplInv.StageEX words S t c) in HR.
   destruct HR as [H250 [H245 [H249 [H244 [H233 [H232 [Hdom [i [Hdec Hex]]]]]]]]].
   unfold BzTmplInv.rg in *.
   pose proof (legal_at t c i Hdom Hdec) as Hleg.
   unfold BzTmplInv.StageMEM, BzTmplInv.rg.
   split; [rewrite (Co.p286 _ _ _ HP); exact H250|]. split; [rewrite (Co.p287 _ _ _ HP); exact H245|].
   split; [rewrite (Co.p283 _ _ _ HP), H244; reflexivity|]. split; [rewrite (Co.p278 _ _ _ HP); exact H233|]. split; [rewrite (Co.p277 _ _ _ HP); exact H232|].
   split; [exact Hdom|]. exists i. split; [exact Hdec|]. exact (exmem seedD D S S1 c i Hleg HD' HDS HP Hex).
 - destruct l1 as [|x l1]; [|exfalso; unfold BzTmplInv.stages in Hold; apply (f_equal (@length _)) in Hold; rewrite app_length in Hold; cbn in Hold; lia].
   (* ID -> EX *)
   cbn [length Nat.sub] in *. unfold BzTmplInv.stage_rel in HR |- *. cbn [length Nat.sub] in *.
   change (BzTmplInv.StageEX words S1 t c). change (BzTmplInv.StageID words S t c) in HR.
   unfold BzTmplInv.stages in Hold. cbn in Hold. injection Hold as Ha Hb Htok Hl2.
   destruct HR as [H141 [H139 [H140 [H138 Hdom]]]]. unfold BzTmplInv.rg in H141, H139, H140, H138.
   destruct (decode_at t c Hdom) as [i [Hdec Hleg]].
   set (w := BzTmplInv.iword words t) in *.
   (* forwarding over the two older stages *)
   assert (HWp : forall k t' c' y, (k < 2)%nat /\ BzTmplInv.stage_rel words events k t' c' -> J.checked_pc_effect t' c' = Some y ->
                forall r, V.isa_view y r = Is.upd (Co.Wpay S (norm 32 (read_signal D 259%nat)) k) r (V.isa_view c' r)).
   { intros k t' c' y [Hk2 HRk] HEf r. destruct k as [|[|k']]; [|  | lia].
     - unfold BzTmplInv.stage_rel in HRk. change (BzTmplInv.StageMEM words S t' c') in HRk.
       destruct HRk as [_ [_ [H283 [_ [_ [Hd' [i' [Hdec' Hm]]]]]]]].
       destruct Hd' as [HAt' Ht']. pose proof (legal_at t' c' i' (conj HAt' Ht') Hdec') as Hleg'.
       pose proof (Is.isa_eff words HC t' c' y i' HAt' Ht' HEf Hdec' r) as Heff.
       cbn [Co.Wpay]. rewrite (W0_eq S c' t' i' Hleg' Hm H283 Hdec'). exact Heff.
     - unfold BzTmplInv.stage_rel in HRk. change (BzTmplInv.StageEX words S t' c') in HRk.
       destruct HRk as [_ [_ [_ [H244' [_ [_ [Hd' [i' [Hdec' Hex']]]]]]]]].
       destruct Hd' as [HAt' Ht']. pose proof (legal_at t' c' i' (conj HAt' Ht') Hdec') as Hleg'.
       pose proof (Is.isa_eff words HC t' c' y i' HAt' Ht' HEf Hdec' r) as Heff.
       cbn [Co.Wpay]. rewrite (W1_eq S c' t' i' Hleg' Hex' H244' Hdec' (norm 32 (read_signal D 259%nat)) (fun Hd' => Cl.exval_all seedD D S c' i' Hleg' Hd' HD' HDS Hex')). exact Heff. }
   assert (HSR' : Pst.StagesRel J.checked_pc_effect (fun k t' c' => (k < 2)%nat /\ BzTmplInv.stage_rel words events k t' c') 0 retired [a; b] c).
   { refine (Pst.relabel J.checked_pc_effect (BzTmplInv.stage_rel words events) _ 0 [a; b] 0 retired c HSR _).
     intros k t' c' _ Hk2 HRk. cbn [length] in Hk2. cbv beta. rewrite Nat.sub_0_r. split; [lia|exact HRk]. }
   pose proof (Pst.forwarding_correct J.checked_pc_effect V.isa_view Z.eqb _ (Co.Wpay S (norm 32 (read_signal D 259%nat))) 0 retired [a; b] c HSR' HWp) as Hfw.
   subst a b.
   assert (Hfw2 : forall r, uw (formal_register_word c r) = Is.upd (Co.W1 S (norm 32 (read_signal D 259%nat))) r (Is.upd (Co.W0 S) r (V.isa_view retired r))).
   { intro r. rewrite (V.view_formal c r), (Hfw r). apply Co.fwd_two. exact HSfull. }
   destruct Hdom as [HAt Ht]. pose proof (conj HAt Ht) as Hdom'.
   (* controller input facts at the driven state *)
   assert (H153 : norm 1 (read_signal D 153%nat) = 0).
   { rewrite (Ci.ctlin_153 seedD D HD'), (Co.d232 _ _ HDS). exact HS5a. }
   assert (H151 : norm 1 (read_signal D 151%nat) = 0).
   { rewrite (Ci.ctlin_151 seedD D HD'), (Co.d277 _ _ HDS). exact HS5b. }
   assert (H142 : norm 1 (read_signal D 142%nat) = 1).
   { rewrite (Ci.ctlin_142 seedD D HD'). change (norm 1 (read_signal (phase_driven_state P F.rise S) 1%nat) = 1). rewrite D1, H1. reflexivity. }
   assert (Hw : norm 32 (read_signal D 140%nat) = w).
   { rewrite (Co.d140 _ _ HDS). exact H140. }
   assert (HAf : norm 2 (read_signal D 160%nat) = Dp.ASEL D -> forall r, r = bitSlice w 15 20 -> norm 32 (read_signal D 204%nat) = uw (formal_register_word c r)).
   { intros Hsel r Hr.
     assert (Hr' : norm 5 (read_signal D 146%nat) = r).
     { rewrite (Lk.link_rs1 seedD D HD'), (Co.d140 _ _ HDS), H140, Hr, (V.bs_norm w 15 20 ltac:(lia) ltac:(lia)). reflexivity. }
     rewrite (Hfw2 r). exact (Co.opnd_A seedD D S retired r HD' HDS HRF' Hsel Hr'). }
   assert (HBf : norm 2 (read_signal D 161%nat) = Dp.BSEL D -> forall r, r = bitSlice w 20 25 -> norm 32 (read_signal D 210%nat) = uw (formal_register_word c r)).
   { intros Hsel r Hr.
     assert (Hr' : norm 5 (read_signal D 147%nat) = r).
     { rewrite (Lk.link_rs2 seedD D HD'), (Co.d140 _ _ HDS), H140, Hr, (V.bs_norm w 20 25 ltac:(lia) ltac:(lia)). reflexivity. }
     rewrite (Hfw2 r). exact (Co.opnd_B seedD D S retired r HD' HDS HRF' Hsel Hr'). }
   assert (HPC : norm 32 (read_signal S 139%nat) = uw (getPc c)). { rewrite H139. exact Ht. }
   assert (HLK : norm 32 (read_signal S 138%nat) = uw (word.add (getPc c) (word.of_Z 4 : word))).
   { rewrite H138, (V.uw_link (getPc c)), <- Ht. reflexivity. }
   destruct (Cl.tr_all seedD D S S1 c w i Hleg HD' H153 H151 H142 Hw Hdec HAf HBf HPC HLK HP) as [Hex [H163 H164]].
   unfold BzTmplInv.StageEX, BzTmplInv.rg. change (BzTmplInv.iword words t) with w.
   split; [rewrite (Co.p250 _ _ _ HP); exact H141|]. split; [rewrite (Co.p245 _ _ _ HP); exact H139|].
   split; [rewrite (Co.p249 _ _ _ HP); exact H138|].
   split; [rewrite (Co.p244 _ _ _ HP), H140, (V.bs_norm w 7 12 ltac:(lia) ltac:(lia)); reflexivity|].
   split; [rewrite (Co.p233 _ _ _ HP); exact H163|]. split; [rewrite (Co.p232 _ _ _ HP); exact H164|].
   split; [exact Hdom'|]. exists i. split; [exact Hdec|]. exact Hex.
Qed.
"""

END = r"""
End Main.
End BzTmplTrans.
"""


def build():
    return TEXT.replace('@AUTHOR@', AUTHOR) + MAIN + END + 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions BzTmplTrans.{e}.\n' for e in ('transport_core', 'exmem', 'W0_eq', 'W1_eq', 'decode_at'))


if __name__ == '__main__':
    Path(sys.argv[1]).write_text(build())
