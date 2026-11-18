#!/usr/bin/env python3
"""o_not_stall = 1 from the decoded instruction word (Bzeeno template route): per class `nw_<C>` (decode of the IF/ID word is class C ->
class slices of the controller wires via the link lemmas and the decode inverse -> BzTmplDisp.<C>_n) and `n_one_word` (any legal instruction).
Premises: comb fixed point, wire 140 = word, load flags (153, 151) = 0, resetn register (wire 1) = 1.
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path
import cpu_tmpl_factcheck as FC
import cpu_isa_classes as isa

CTL = Path('results/r-tmpl-bz-ctl-20261103-a4/BzTmplCtl3.v')
ARGS = {'OP': 3, 'OPIMM': 3, 'LUI': 2, 'AUIPC': 2, 'JAL': 2, 'JALR': 3, 'BRANCH': 3}
HEAD = r"""(** Bzeeno: o_not_stall = 1 from the instruction word (tools/cpu_tmpl_bznone.py). proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment Lang.ExtendedSVSymExec GeneratedRuntimeInput.ConfiguredAST
 Ex.External.CPUClassTableInverse Ex.External.CPUDatapathFacts Ex.External.CPUISARegView Ex.External.CPUJumpFamilyProgramDomain
 coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Spec.Decode
 TmplBzLink.BzTmplLink TmplBzCtlIn.BzTmplCtlIn TmplBzDisp.BzTmplDisp.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUDatapathFacts CPUISARegView BzTmplLink BzTmplCtlIn BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Module BzTmplNOne.
Notation P := bzeeno_load_use_jal_program (only parsing).
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Ltac slice_goal w :=
  first [ (rewrite (slice_val w 0 7 ltac:(lia)); cbn; assumption)
        | (rewrite (slice_val w 12 3 ltac:(lia)); cbn; assumption)
        | (rewrite (slice_val w 25 7 ltac:(lia)); cbn; assumption)
        | (rewrite (bs7_shift w ltac:(assumption)); match goal with H : bitSlice w 26 32 = _ |- _ => rewrite H end; reflexivity) ].
"""


def build():
    sets = FC.scan(CTL.read_text())
    L = [HEAD]
    names = []
    for c in isa.classes():
        cl = c['name']
        mine = {k: v for k, v in sets.items() if re.match(f'facts_{cl}_f', k)}
        common = [f for f in next(iter(mine.values())) if all(f in o for o in mine.values())]
        prem = [f[0][2] for f in common if f[0][0] == 'EVar']
        cmpid = sorted({e[2] for k, fl in mine.items() for e, v in fl if e[0] == 'EVar' and (e, v) not in common})
        k = ARGS[c['group']]
        av = ' '.join(f'a{i}' for i in range(k))
        L.append(f'Lemma nw_{cl} seed d w {av} : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->')
        L.append(f' Decode.decode Decode.RV32I w = Decode.IInstruction (Decode.{cl} {av}) -> norm 1 (read_signal d 156%nat) = 1.')
        L.append(f'Proof. intros HL Hw H153 H151 H142 Hdec. destruct (Inv.inv_{cl} w {av} Hdec) as [_ Hs]. repeat match goal with H : _ /\ _ |- _ => destruct H end.')
        args = []
        for pid in prem:
            if pid == '142':
                args.append('H142')
            else:
                lk = {'143': 'link_opcode', '144': 'link_funct3', '145': 'link_funct7'}[pid]
                args.append(f'(ltac:(rewrite ({lk} seed d HL), Hw; slice_goal w))')
        cmp = f' (BzTmplDisp.bit_cases (read_signal d {cmpid[0]}%nat))' if cmpid else ''
        L.append(f' exact (BzTmplDisp.{cl}_n seed d HL H153 H151 ' + ' '.join(args) + cmp + ').')
        L.append('Qed.')
        names.append(f'nw_{cl}')
    L.append('Theorem n_one_word seed d w i : CombLFP P seed d -> norm 32 (read_signal d 140%nat) = w -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> norm 1 (read_signal d 142%nat) = 1 ->')
    L.append(' Decode.decode Decode.RV32I w = Decode.IInstruction i -> CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> norm 1 (read_signal d 156%nat) = 1.')
    L.append('Proof. intros HL Hw H153 H151 H142 Hdec Hleg. destruct i; try (vm_compute in Hleg; discriminate Hleg).')
    L.append(' all: first [ ' + ' | '.join(f'exact (nw_{c["name"]} seed d w _ _ _ HL Hw H153 H151 H142 Hdec)' if ARGS[c["group"]] == 3 else f'exact (nw_{c["name"]} seed d w _ _ HL Hw H153 H151 H142 Hdec)' for c in isa.classes()) + ' ].')
    L.append('Qed.')
    names.append('n_one_word')
    L.append('End BzTmplNOne.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L.extend(f'Print Assumptions BzTmplNOne.{n}.' for n in names)
    return '\n'.join(L) + '\n'


if __name__ == '__main__':
    Path(sys.argv[1]).write_text(build())
