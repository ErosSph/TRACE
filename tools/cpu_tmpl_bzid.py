#!/usr/bin/env python3
"""ID-stage facts of the Bzeeno template route per instruction class (module BzTmplId), generated from the class table.
  IC d i        : the controller outputs the front relation needs: no store/load (163, 164 = 0) and the class's flush/pcsrc/jalr select
                  (branches: compare unit selects 174/175 and the flow outputs per compare bit);
  ic_<C>        : the decoded word at the IF/ID register is class C -> IC (class slices via the link lemmas, BzTmplDisp2.<C>_o and BzTmplFlow.<C>_f);
  ic_all        : any legal decoded word;
  br_<C>        : branches: given the operands 204/210 as ISA register values, flush = pcsrc = boolz (isa_branch_guard ...) (BzTmplExIface.<C>_isa).
Untrusted generator; Coq checks everything. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path
import cpu_tmpl_factcheck as FC
import cpu_isa_classes as isa
import cpu_tmpl_bzdisp as DP
import cpu_tmpl_bzflow as FL
import cpu_tmpl_bznone as NO

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
import cpu_tmpl_bztrans as _TB
C168 = {cl: v[168][1] for cl, v in _TB.ctl_outs().items()}
HEAD = r"""(** Bzeeno: ID-stage controller facts per instruction class (tools/cpu_tmpl_bzid.py). proof_author: """ + AUTHOR + r"""; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Lang.ExtendedSVSymExec GeneratedRuntimeInput.ConfiguredAST
 Ex.External.CPUClassTableInverse Ex.External.CPUDatapathFacts Ex.External.CPUISARegView Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUImmediateShapes
 Ex.External.CV32E40PBranchISACondition
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Spec.Decode
 TmplBzLink.BzTmplLink TmplBzCtlIn.BzTmplCtlIn TmplBzDisp.BzTmplDisp TmplBzDisp2.BzTmplDisp2 TmplBzFlow.BzTmplFlow TmplBzExCmp.BzTmplExCmp TmplBzExIface.BzTmplExIface.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUDatapathFacts CPUISARegView BzTmplLink BzTmplCtlIn CV32E40PBranchISACondition BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Module BzTmplId.
Notation P := bzeeno_load_use_jal_program (only parsing).
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Module Dp := TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Module Fw := TmplBzFlow.BzTmplFlow.BzTmplFlow.
Module Dq := TmplBzDisp.BzTmplDisp.BzTmplDisp.
Module Ex := TmplBzExIface.BzTmplExIface.BzTmplExIface.
Module Cm := TmplBzExCmp.BzTmplExCmp.BzTmplExCmp.
Ltac slice_goal w :=
  first [ (rewrite (slice_val w 0 7 ltac:(lia)); cbn; assumption)
        | (rewrite (slice_val w 12 3 ltac:(lia)); cbn; assumption)
        | (rewrite (slice_val w 25 7 ltac:(lia)); cbn; assumption)
        | (rewrite (bs7_shift w ltac:(assumption)); match goal with H : bitSlice w 26 32 = _ |- _ => rewrite H end; reflexivity) ].
"""

ARGS = NO.ARGS
CMPW = {'Beq': 149, 'Bne': 149, 'Blt': 148, 'Bge': 148, 'Bltu': 148, 'Bgeu': 148}


def build():
    sets, gp, metas = FL.TB.meta()
    outs = FL.outs_table()
    L = [HEAD]
    # the IC definition
    L.append('Definition IC (d : State) (i : Decode.InstructionI) : Prop :=')
    L.append(' norm 1 (read_signal d 163%nat) = 0 /\\ norm 1 (read_signal d 164%nat) = 0 /\\ norm 1 (read_signal d 168%nat) = (match i with')
    for c in isa.classes():
        L.append(f'   | Decode.{c["name"]} {" ".join(["_"] * ARGS[c["group"]])} => {C168[c["name"]]}')
    L.append('   | _ => 0 end) /\\')
    L.append(' match i with')
    info = {}
    for c in isa.classes():
        cl = c['name']
        us = ' '.join(['_'] * ARGS[c['group']])
        if cl in CMPW:
            o0, o1 = outs[(cl, '0')], outs[(cl, '1')]
            cw = CMPW[cl]
            body = (f'norm 1 (read_signal d 174%nat) = {{s}} /\\ norm 1 (read_signal d 175%nat) = 0 /\\ ((norm 1 (read_signal d {cw}%nat) = 0 -> Fw.Fl d {o0[157]} {o0[159]} {o0[167]}) /\\ '
                    f'(norm 1 (read_signal d {cw}%nat) = 1 -> Fw.Fl d {o1[157]} {o1[159]} {o1[167]}))')
        else:
            o = outs[(cl, '')]
            body = f'Fw.Fl d {o[157]} {o[159]} {o[167]}'
        info[cl] = body
        L.append(f' | Decode.{cl} {us} => {body}')
    L.append(' | _ => False end.')
    # signed flags of the branches come from the Cout constants of the controller facts
    t = DP.CTL.read_text()
    names = ['IC']
    for c in isa.classes():
        cl = c['name']
        mine = {k: v for k, v in sets.items() if re.match(f'facts_{cl}_f', k)}
        common, scen = metas[cl]
        prem = [f[0][2] for f in common if f[0][0] == 'EVar']
        cmpid = sorted({e[2] for k, fl in mine.items() for e, v in fl if e[0] == 'EVar' and (e, v) not in common})
        k = ARGS[c['group']]
        av = ' '.join(f'a{i}' for i in range(k))
        args = []
        for pid in prem:
            if pid == '142':
                args.append('H142')
            else:
                lk = {'143': 'link_opcode', '144': 'link_funct3', '145': 'link_funct7'}[pid]
                args.append(f'(ltac:(rewrite ({lk} seed d HL), Hw; slice_goal w))')
        astr = ' '.join(args)
        cmp = f' (Dq.bit_cases (read_signal d {cmpid[0]}%nat))' if cmpid else ''
        L.append(f'Lemma ic_{cl} seed d w {av} : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->')
        L.append(f' Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.{cl} {av}) -> IC d (Decode.{cl} {av}).')
        L.append(f'Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_{cl} w {av} Hdec) as [_ Hs]. repeat match goal with H : _ /\\ _ |- _ => destruct H end.')
        L.append(f' pose proof (Dp.{cl}_o seed d HL H153 H151 {astr}{cmp}) as HO.')
        L.append(f' pose proof (Fw.{cl}_f seed d HL H153 H151 {astr}) as HF.')
        L.append(' destruct HO as [_ [_ [_ [_ [_ [H163 [H164 [_ [_ [H168 [_ [_ [H174 H175]]]]]]]]]]]]].')
        if cl in CMPW:
            L.append(' unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. split; [exact H174|]. split; [exact H175|]. exact HF.')
            info[cl] = info[cl]
        else:
            L.append(' unfold IC. split; [exact H163|]. split; [exact H164|]. split; [exact H168|]. exact HF.')
        L.append('Qed.')
    # fix the signed flag placeholder with the constants of the controller (174)
    # dispatcher
    L.append('Theorem ic_all seed d w i : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->')
    L.append(' Decode.decode Decode.RV32I w = Decode.IInstruction i -> CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> IC d i.')
    L.append('Proof. intros HL Hw H153 H151 H142 Hdec Hleg. destruct i; try (vm_compute in Hleg; discriminate Hleg).')
    L.append(' all: first [ ' + ' | '.join((f'exact (ic_{c["name"]} seed d w _ _ _ HL Hw H153 H151 H142 Hdec)' if ARGS[c["group"]] == 3 else f'exact (ic_{c["name"]} seed d w _ _ HL Hw H153 H151 H142 Hdec)') for c in isa.classes()) + ' ].')
    L.append('Qed.')
    names.append('ic_all')
    # flush = 0 implies pcsrc = 0
    for c in isa.classes():
        cl = c['name']
        us = ' '.join(['_'] * ARGS[c['group']])
        L.append(f'Lemma icfp_{cl} d {" ".join("a%d" % j for j in range(ARGS[c["group"]]))} : IC d (Decode.{cl} {" ".join("a%d" % j for j in range(ARGS[c["group"]]))}) -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.')
        if cl in CMPW:
            o0, o1 = outs[(cl, '0')], outs[(cl, '1')]
            def one(o, hn):
                return ('exact B' if o[157] == 0 else 'rewrite A in H157; discriminate H157')
            L.append(f'Proof. intros [_ [_ [_ [_ [_ [H0 H1]]]]]] H157. destruct (Dq.bit_cases (read_signal d {CMPW[cl]}%nat)) as [Hb|Hb].')
            L.append(f' - destruct (H0 Hb) as [A [B C]]. {one(o0, 0)}.')
            L.append(f' - destruct (H1 Hb) as [A [B C]]. {one(o1, 1)}.')
        else:
            o = outs[(cl, '')]
            L.append('Proof. intros [_ [_ [_ [A [B C]]]]] H157. ' + ('exact B' if o[157] == 0 else 'rewrite A in H157; discriminate H157') + '.')
        L.append('Qed.')
    L.append('Theorem ic_fp d i : CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> IC d i -> norm 1 (read_signal d 157%nat) = 0 -> norm 2 (read_signal d 159%nat) = 0.')
    L.append('Proof. intros Hleg HI H157. destruct i; try (vm_compute in Hleg; discriminate Hleg).')
    L.append(' all: first [ ' + ' | '.join(f'exact (icfp_{c["name"]} _ ' + ' '.join(['_'] * ARGS[c["group"]]) + ' HI H157)' for c in isa.classes()) + ' ].')
    L.append('Qed.')
    names.append('ic_fp')
    # branches: flush = pcsrc = guard
    L.append('Section Br.\nContext {word : Interface.word 32} {BW : Bitwidth 32} {word_ok : word.ok word}.')
    for c in isa.classes():
        cl = c['name']
        if cl not in CMPW:
            continue
        cw = CMPW[cl]
        L.append(f'Theorem br_{cl} seed d (x y : word) rs1 rs2 imm : CombLFP P seed d -> IC d (Decode.{cl} rs1 rs2 imm) -> norm 32 (read_signal d 204%nat) = word.unsigned x -> norm 32 (read_signal d 210%nat) = word.unsigned y ->')
        L.append(f' Fw.Fl d (boolz (isa_branch_guard (Decode.{cl} rs1 rs2 imm) x y)) (boolz (isa_branch_guard (Decode.{cl} rs1 rs2 imm) x y)) 0.')
        L.append(f'Proof. intros HL HI ha hb. unfold IC in HI. cbn [IC] in HI. destruct HI as [_ [_ [_ [h174 [h175 [HF0 HF1]]]]]].')
        L.append(f' pose proof (Ex.{cl}_isa seed d x y rs1 rs2 imm HL h174 h175 ha hb) as [Hp _].')
        L.append(f' destruct (Dq.bit_cases (read_signal d {cw}%nat)) as [Hb|Hb].')
        v0, v1 = outs[(cl, '0')][159], outs[(cl, '1')][159]
        L.append(f' - pose proof (HF0 Hb) as HF. rewrite Hb in Hp. assert (E0 : Cm.{cl}_pcsrc 0 = {v0}) by reflexivity. rewrite E0 in Hp. rewrite <- Hp. exact HF.')
        L.append(f' - pose proof (HF1 Hb) as HF. rewrite Hb in Hp. assert (E1 : Cm.{cl}_pcsrc 1 = {v1}) by reflexivity. rewrite E1 in Hp. rewrite <- Hp. exact HF.')
        L.append('Qed.')
        names.append(f'br_{cl}')
    L.append('End Br.')
    L.append('End BzTmplId.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L.extend(f'Print Assumptions BzTmplId.{n}.' for n in names)
    return '\n'.join(L) + '\n', names


def signed_flag(cl):
    return {'Beq': 1, 'Bne': 1, 'Blt': 1, 'Bge': 1, 'Bltu': 0, 'Bgeu': 0}[cl]


def build_sel():
    """Module BzTmplSel: the forwarding selects 160/161 of the controller equal ASEL/BSEL for any legal instruction word (from BzTmplDisp2.<C>_o)."""
    sets, gp, metas = FL.TB.meta()
    L = [HEAD.replace('Module BzTmplId.', 'Module BzTmplSel.').replace('ID-stage controller facts per instruction class (tools/cpu_tmpl_bzid.py)',
                      'forwarding selects per instruction class (tools/cpu_tmpl_bzid.py --sel)')]
    for c in isa.classes():
        cl = c['name']
        mine = {k: v for k, v in sets.items() if re.match(f'facts_{cl}_f', k)}
        common, scen = metas[cl]
        prem = [f[0][2] for f in common if f[0][0] == 'EVar']
        cmpid = sorted({e[2] for k, fl in mine.items() for e, v in fl if e[0] == 'EVar' and (e, v) not in common})
        k = ARGS[c['group']]
        av = ' '.join(f'a{i}' for i in range(k))
        args = []
        for pid in prem:
            if pid == '142':
                args.append('H142')
            else:
                lk = {'143': 'link_opcode', '144': 'link_funct3', '145': 'link_funct7'}[pid]
                args.append(f'(ltac:(rewrite ({lk} seed d HL), Hw; slice_goal w))')
        astr = ' '.join(args)
        cmp = f' (Dq.bit_cases (read_signal d {cmpid[0]}%nat))' if cmpid else ''
        L.append(f'Lemma sel_{cl} seed d w {av} : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->')
        L.append(f' Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.{cl} {av}) -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.')
        L.append(f'Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_{cl} w {av} Hdec) as [_ Hs]. repeat match goal with H : _ /\\ _ |- _ => destruct H end.')
        L.append(f' exact (Dp.Cout_sel _ _ _ _ _ _ _ _ _ _ (Dp.{cl}_o seed d HL H153 H151 {astr}{cmp})).')
        L.append('Qed.')
    L.append('Theorem sel_all seed d w i : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->')
    L.append(' Decode.decode Decode.RV32I w = Decode.IInstruction i -> CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> norm 2 (read_signal d 160%nat) = Dp.ASEL d /\\ norm 2 (read_signal d 161%nat) = Dp.BSEL d.')
    L.append('Proof. intros HL Hw H153 H151 H142 Hdec Hleg. destruct i; try (vm_compute in Hleg; discriminate Hleg).')
    L.append(' all: first [ ' + ' | '.join((f'exact (sel_{c["name"]} seed d w _ _ _ HL Hw H153 H151 H142 Hdec)' if ARGS[c["group"]] == 3 else f'exact (sel_{c["name"]} seed d w _ _ HL Hw H153 H151 H142 Hdec)') for c in isa.classes()) + ' ].')
    L.append('Qed.')
    L.append('End BzTmplSel.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\nPrint Assumptions BzTmplSel.sel_all.')
    return '\n'.join(L) + '\n'


if __name__ == '__main__':
    if len(sys.argv) > 2 and sys.argv[2] == '--sel':
        Path(sys.argv[1]).write_text(build_sel())
        sys.exit(0)
    t, ex = build()
    for cl in CMPW:
        t = t.replace('| Decode.%s _ _ _ => norm 1 (read_signal d 174%%nat) = {s}' % cl, '| Decode.%s _ _ _ => norm 1 (read_signal d 174%%nat) = %d' % (cl, signed_flag(cl)))
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()), len(ex))
