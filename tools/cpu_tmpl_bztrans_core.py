#!/usr/bin/env python3
"""Bzeeno transport, RTL-side core (module BzTmplTrCore): the registers after one cycle in terms of the old registers and the driven rise state
(`Post`), driven = old registers (`DSame`), the forwarding payloads and the operand lemma (class independent).  Generated text + hand core.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
# (register after the cycle, width, source kind, source): S = old register, D = driven wire
FALL = [(286, 1, 'S', 250), (287, 32, 'S', 245), (283, 5, 'S', 244), (278, 1, 'S', 233), (277, 1, 'S', 232), (279, 1, 'S', 236), (284, 32, 'D', 259),
        (245, 32, 'S', 139), (249, 32, 'S', 138), (233, 1, 'D', 163), (232, 1, 'D', 164), (242, 6, 'D', 158), (237, 1, 'D', 169), (234, 1, 'D', 165),
        (235, 1, 'D', 173), (241, 1, 'D', 166), (236, 1, 'D', 162), (243, 1, 'D', 224), (246, 32, 'D', 204), (247, 32, 'D', 210), (248, 32, 'D', 30)]
# registers that the driven state keeps (sequential registers, comb-unwritten)
KEEP = [138, 139, 140, 141, 232, 233, 234, 235, 236, 237, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 277, 278, 279, 283, 284, 286, 287]
FR_ONLY = [319]

HEAD = r"""(** Bzeeno transport, RTL core (tools/cpu_tmpl_bztrans_core.py).  proof_author: @AUTHOR@; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVScalarHistory Lang.ExtendedSVBoundedCatalogPhase
 Lang.ExtendedSVSeqTree Lang.ExtendedSVBankOperand GeneratedClockCycleJoint.CycleJoint GeneratedRuntimeInput.ConfiguredAST
 GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment
 TmplBzEdge.BzTmplEdge TmplBzEnv.BzTmplEnv TmplBzPhase.BzTmplPhase TmplBzValid.BzTmplValid TmplBzXfer.BzTmplXfer TmplBzFrame.BzTmplFrame TmplBzInv.BzTmplInv
 TmplBzStage.BzTmplStage TmplBzShape.BzTmplShape TmplBzTrIsa.BzTmplTrIsa TmplBzFwdIn.BzTmplFwdIn TmplBzExGen.BzTmplExGen TmplBzRF.BzTmplRF TmplBzCtlIn.BzTmplCtlIn
 TmplBzLink.BzTmplLink TmplBzDisp2.BzTmplDisp2 Ex.External.CPUISARegView Ex.External.CPUPipelineStages
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility.
Import ListNotations ExtendedSV ExtendedSVBankAlignment ExtendedSVDependencyCatalog ExtendedSVScalarHistory ExtendedSVBoundedCatalogPhase ExtendedSVBankOperand.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program.
Module BzTmplTrCore.
Notation P := BzeenoLoadUseJalASTConfigured3122be4a95.bzeeno_load_use_jal_program (only parsing).
Module Ph := TmplBzPhase.BzTmplPhase.BzTmplPhase.
Module En := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Module Ed := TmplBzEdge.BzTmplEdge.BzTmplEdge.
Module Va := TmplBzValid.BzTmplValid.BzTmplValid.
Module Xf := TmplBzXfer.BzTmplXfer.BzTmplXfer.
Module Fr := TmplBzFrame.BzTmplFrame.BzTmplFrame.
Module St := TmplBzStage.BzTmplStage.BzTmplStage.
Module Sh := TmplBzShape.BzTmplShape.BzTmplShape.
Module Is := TmplBzTrIsa.BzTmplTrIsa.BzTmplTrIsa.
Module Fi := TmplBzFwdIn.BzTmplFwdIn.BzTmplFwdIn.
Module Gn := TmplBzExGen.BzTmplExGen.BzTmplExGen.
Module Rf := TmplBzRF.BzTmplRF.BzTmplRF.
Module Ci := TmplBzCtlIn.BzTmplCtlIn.BzTmplCtlIn.
Module Lk := TmplBzLink.BzTmplLink.BzTmplLink.
Module Dp := TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Module F := GeneratedSeedBoot.FrozenEnvironment.
Module V := Ex.External.CPUISARegView.CPUISARegView.
Notation Cat := GeneratedDependencyCatalog.Catalog.actual_catalog.
"""


def post_record():
    L = ['Record Post (S D S1 : State) : Prop := {']
    for r, w, k, s in FALL:
        src = f'read_signal S {s}%nat' if k == 'S' else f'read_signal D {s}%nat'
        L.append(f' p{r} : norm {w} (read_signal S1 {r}%nat) = norm {w} ({src});')
    L.append(' p250 : norm 1 (read_signal S1 250%nat) = norm 1 (read_signal S 141%nat);')
    L.append(' p244 : norm 5 (read_signal S1 244%nat) = norm 5 (Z.shiftr (norm 32 (read_signal S 140%nat)) 7) }.')
    return '\n'.join(L)


def post_proof():
    FR = lambda r: f'Fr.fall_frame_{r} F.fall (Ph.rise_state words events) seed2 Hc2 Hv2 H02 H12 HW2 HL2 HD2'
    L = []
    for r, w, k, s in FALL:
        L.append(f' assert (F{r} := {FR(r)}).')
    for r, w, k, s in FALL:
        if r == 286:
            L.append(' assert (X286 := Va.valid_286 F.rise (En.rs words events) seed (Sh.flushD words events) (Sh.stallD words events) Hc Hv H0 H1 HW HL HD eq_refl eq_refl).')
        else:
            L.append(f' assert (X{r} := Xf.xfer_{r} F.rise (En.rs words events) seed HH).')
    L.append(' assert (V250 := Va.valid_250 F.rise (En.rs words events) seed (Sh.flushD words events) (Sh.stallD words events) Hc Hv H0 H1 HW HL HD eq_refl eq_refl).')
    L.append(f' assert (F250 := {FR(250)}).')
    L.append(' assert (X244f := Xf.xfer_244_field F.rise (En.rs words events) seed HH).')
    L.append(f' assert (F244 := {FR(244)}).')
    L.append(' rewrite Hn in V250.')
    L.append(' rewrite <- Ph.rise_state_eq in *. rewrite Ph.fall_state_eq.')
    L.append(' constructor.')
    L.extend(f' - rewrite F{r}; exact X{r}.' for r, _, _, _ in FALL)
    L.append(' - rewrite F250. rewrite V250. apply Sh.bit1.')
    L.append(' - rewrite F244. exact X244f.')
    return '\n'.join(L)


def dsame():
    L = ['Record DSame (D S : State) : Prop := {']
    L.append(';\n'.join(f' d{r} : read_signal D {r}%nat = read_signal S {r}%nat' for r in KEEP + FR_ONLY) + ' }.')
    return '\n'.join(L)


def dsame_proof():
    L = ['Theorem dsame_holds words events : Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> DSame (Sh.drv words events) (En.rs words events).',
         'Proof. intros HE HB. destruct (En.env_rise_hyps words events HE HB) as [seed [Hc _]]. constructor.']
    for r in KEEP:
        L.append(f' - exact (ExtendedSVSeqTree.driven_unchanged P F.rise (En.rs words events) {r}%nat St.comb_unw_{r} ltac:(rewrite Hc; discriminate)).')
    for r in FR_ONLY:
        L.append(f' - exact (ExtendedSVSeqTree.driven_unchanged P F.rise (En.rs words events) {r}%nat Fr.comb_unw_{r} ltac:(rewrite Hc; discriminate)).')
    L.append('Qed.')
    return '\n'.join(L)


MID = r"""
Section Core.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.

(** The write payloads of the older stages as the RTL presents them (the guards are those of the forwarding selects ASEL/BSEL). *)
Definition W0 (S : State) : option (Z * Z) :=
 if (Z.eqb (norm 1 (read_signal S 279%nat)) 1) && negb (Z.eqb (norm 5 0) (norm 5 (read_signal S 283%nat))) then Some (norm 5 (read_signal S 283%nat), norm 32 (read_signal S 284%nat)) else None.
Definition W1 (S : State) (vex : Z) : option (Z * Z) :=
 if (Z.eqb (norm 1 (read_signal S 236%nat)) 1) && negb (Z.eqb (norm 5 0) (norm 5 (read_signal S 244%nat))) then Some (norm 5 (read_signal S 244%nat), vex) else None.
Definition Wpay (S : State) (vex : Z) (k : nat) : option (Z * Z) := match k with 0%nat => W0 S | 1%nat => W1 S vex | _ => None end.
Local Notation fwd := (CPUPipelineStages.CPUPipelineStages.forward_from (Token:=Z) Z.eqb).

Lemma n50 : norm 5 0 = 0. Proof. reflexivity. Qed.
Lemma W0_none S : BzTmplInv.Struct S -> norm 1 (read_signal S 286%nat) = 0 -> W0 S = None.
Proof. intros [_ [_ [H286 _]]] H. destruct (H286 H) as [H283 _]. unfold BzTmplInv.rg in H283. unfold W0. rewrite H283. rewrite n50. cbn [Z.eqb negb]. rewrite andb_false_r. reflexivity. Qed.
Lemma W1_none S vex : BzTmplInv.Struct S -> norm 1 (read_signal S 250%nat) = 0 -> W1 S vex = None.
Proof. intros [_ [H250 _]] H. destruct (H250 H) as [H244 _]. unfold BzTmplInv.rg in H244. unfold W1. rewrite H244. rewrite n50. cbn [Z.eqb negb]. rewrite andb_false_r. reflexivity. Qed.
Lemma W0_none' S : BzTmplInv.Struct S -> norm 1 (read_signal S 286%nat) = 0 -> W0 S = None.
Proof. exact (W0_none S). Qed.

Lemma fwd_two S vex r base : BzTmplInv.Struct S ->
 fwd (Wpay S vex) 0 [BzTmplInv.tok S 286 287; BzTmplInv.tok S 250 245] r base = Is.upd (W1 S vex) r (Is.upd (W0 S) r base).
Proof. intro HS. unfold BzTmplInv.tok, BzTmplInv.rg.
 destruct (Z.eqb (norm 1 (read_signal S 286%nat)) 0) eqn:E286; destruct (Z.eqb (norm 1 (read_signal S 250%nat)) 0) eqn:E250.
 - apply Z.eqb_eq in E286, E250. rewrite (W0_none S HS E286), (W1_none S vex HS E250). reflexivity.
 - apply Z.eqb_eq in E286. rewrite (W0_none S HS E286). reflexivity.
 - apply Z.eqb_eq in E250. rewrite (W1_none S vex HS E250). reflexivity.
 - reflexivity.
Qed.

Lemma bit_cases (x : Z) : norm 1 x = 0 \/ norm 1 x = 1.
Proof. pose proof (norm_bounds 1 x) as H. cbn in H. lia. Qed.

Ltac opnd_close m0 m1 m2 o317 i312 Hr :=
 first [ rewrite (m1 ltac:(assumption)); reflexivity | rewrite (m2 ltac:(assumption)); reflexivity
       | (rewrite (m0 ltac:(assumption)), o317, i312, Hr; reflexivity) ].
"""

OPND = r"""
Lemma opnd_@X@ seed1 (D S : State) (retired : FormalSpec.State) (r : Z) :
 CombLFP P seed1 D -> DSame D S -> RFRel (read_signal S 319%nat) (V.isa_view retired) ->
 norm 2 (read_signal D @SEL@%nat) = Dp.@SELF@ D -> norm 5 (read_signal D @RS@%nat) = r ->
 norm 32 (read_signal D @MUX@%nat) = Is.upd (W1 S (norm 32 (read_signal D 259%nat))) r (Is.upd (W0 S) r (V.isa_view retired r)).
Proof. intros HL HS HR Hsel Hr.
 pose proof (Ci.ctlin_152 seed1 D HL) as c152. pose proof (Ci.ctlin_150 seed1 D HL) as c150.
 pose proof (Ci.ctlin_154 seed1 D HL) as c154. pose proof (Ci.ctlin_155 seed1 D HL) as c155.
 pose proof (Gn.fwd@XL@_sel0 seed1 D HL) as m0. pose proof (Gn.fwd@XL@_sel1 seed1 D HL) as m1. pose proof (Gn.fwd@XL@_sel2 seed1 D HL) as m2.
 assert (HR' : RFRel (read_signal D 319%nat) (V.isa_view retired)) by (rewrite (d319 _ _ HS); exact HR).
 pose proof (Rf.operand_@IDX@ seed1 D (V.isa_view retired) HL HR') as o317.
 pose proof (Fi.rsidx_@IDXN@ seed1 D HL) as i312.
 unfold Dp.@SELF@ in Hsel. rewrite c152, c150, c154, c155, Hr in Hsel.
 rewrite (d236 _ _ HS), (d279 _ _ HS), (d283 _ _ HS), (d244 _ _ HS) in Hsel.
 rewrite (d284 _ _ HS) in m2.
 unfold W1, W0, Is.upd, CPUPipelineStages.CPUPipelineStages.upd. revert Hsel.
 destruct (Z.eqb (norm 1 (read_signal S 236%nat)) 1) eqn:Ea1; destruct (Z.eqb (norm 5 0) (norm 5 (read_signal S 244%nat))) eqn:Ez1;
 destruct (Z.eqb (norm 5 (read_signal S 244%nat)) r) eqn:Ee1;
 destruct (Z.eqb (norm 1 (read_signal S 279%nat)) 1) eqn:Ea2; destruct (Z.eqb (norm 5 0) (norm 5 (read_signal S 283%nat))) eqn:Ez2;
 destruct (Z.eqb (norm 5 (read_signal S 283%nat)) r) eqn:Ee2; cbn; try rewrite Ee1; try rewrite Ee2; cbn; intro Hsel;
 opnd_close m0 m1 m2 o317 i312 Hr.
Qed.
"""

def opnd():
    A = dict(X='A', SEL='160', SELF='ASEL', RS='146', MUX='204', XL='a', IDX='317', IDXN='312')
    B = dict(X='B', SEL='161', SELF='BSEL', RS='147', MUX='210', XL='b', IDX='318', IDXN='313')
    out = ''
    for d in (A, B):
        t = OPND
        for k, v in d.items():
            t = t.replace(f'@{k}@', v)
        out += t
    return out


def build():
    L = [HEAD.replace('@AUTHOR@', AUTHOR), post_record(), dsame(), dsame_proof()]
    L.append(r"""Theorem post_holds words events :
 Forall (CatalogEvent P Cat) events -> ClockBoundary (En.rs words events) -> Sh.stallD words events = 1 ->
 Post (En.rs words events) (Sh.drv words events) (Ph.fall_state words events).
Proof.
 intros HE HB Hn. destruct (Ph.cycle_hyps words events HE HB) as [[seed [Hc [Hv [H0 [H1 [HW [HL HD]]]]]]] [[seed2 [Hc2 [Hv2 [H02 [H12 [HW2 [HL2 HD2]]]]]]] _]].
 pose proof (conj Hc (conj Hv (conj H0 (conj H1 (conj HW (conj HL HD)))))) as HH.""")
    L.append(post_proof())
    L.append('Qed.')
    L.append(MID)
    L.append(opnd())
    L.append('End Core.\nEnd BzTmplTrCore.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L.extend(f'Print Assumptions BzTmplTrCore.{e}.' for e in ('post_holds', 'dsame_holds', 'fwd_two', 'opnd_A', 'opnd_B'))
    return '\n'.join(L) + '\n'


if __name__ == '__main__':
    Path(sys.argv[1]).write_text(build())
