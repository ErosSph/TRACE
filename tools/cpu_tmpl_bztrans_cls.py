#!/usr/bin/env python3
"""Bzeeno transport, per-class lemmas (module BzTmplTrCls), generated from the class table and the accepted ex-iface / controller-output modules:
  tr_<C>    ID -> EX : the ExCl clause of class C at the registers after the cycle (Post), from the controller outputs (Cout), the forwarded operands, the
            immediate (<C>_imm) and the compare bit (<C>_cmp);
  exval_<C> the EX result wire 259 at the driven state equals the ISA value (<C>_ex_isa), from ExCl at the old registers;
  dispatchers over the instruction constructor (tr_all, exval_all) and rd_inv.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path
import cpu_isa_classes as isa
import cpu_tmpl_bztrans as TB
import cpu_tmpl_bztrans_isa as TI

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
FIELDS = {}
for n in ('Add', 'Sub', 'Sll', 'Slt', 'Sltu', 'Xor', 'Srl', 'Sra', 'Or', 'And'):
    FIELDS[n] = ['rd', 'rs1', 'rs2']
for n in ('Addi', 'Slti', 'Sltiu', 'Xori', 'Ori', 'Andi'):
    FIELDS[n] = ['rd', 'rs', 'imm']
for n in ('Slli', 'Srli', 'Srai'):
    FIELDS[n] = ['rd', 'rs', 'sh']
FIELDS['Lui'] = ['rd', 'imm']
FIELDS['Auipc'] = ['rd', 'imm']
FIELDS['Jal'] = ['rd', 'imm']
FIELDS['Jalr'] = ['rd', 'rs1', 'imm']
for n in ('Beq', 'Bne', 'Blt', 'Bge', 'Bltu', 'Bgeu'):
    FIELDS[n] = ['rs1', 'rs2', 'imm']

KIND = {}
for n in ('Add', 'Sub', 'Sll', 'Xor', 'Srl', 'Sra', 'Or', 'And'):
    KIND[n] = 'R'
KIND['Slt'] = KIND['Sltu'] = 'Rslt'
for n in ('Addi', 'Xori', 'Ori', 'Andi'):
    KIND[n] = 'I'
KIND['Slti'] = KIND['Sltiu'] = 'Islt'
for n in ('Slli', 'Srli', 'Srai'):
    KIND[n] = 'Ish'
KIND['Lui'] = 'Lui'
KIND['Auipc'] = 'Auipc'
KIND['Jal'] = 'Jal'
KIND['Jalr'] = 'Jalr'
for n in ('Beq', 'Bne', 'Blt', 'Bge', 'Bltu', 'Bgeu'):
    KIND[n] = 'B'
IMMFN = {'Lui': 'isa_imm_U', 'Auipc': 'isa_imm_U'}
# register rewrite list for the Post equalities
PREG = [242, 237, 234, 235, 241, 236, 243, 246, 247, 248, 245, 249]
DREG = [242, 237, 234, 235, 241, 243, 245, 246, 247, 248, 249]
SLICE = {143: 'link_opcode', 144: 'link_funct3', 145: 'link_funct7'}

HEAD = r"""(** Bzeeno transport, per-class lemmas (tools/cpu_tmpl_bztrans_cls.py).  proof_author: @AUTHOR@; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment GeneratedRuntimeInput.ConfiguredAST
 Ex.External.CPUClassTableInverse Ex.External.CPUDatapathFacts Ex.External.CPUISARegView Ex.External.CPUImmediateShapes Ex.External.CPUJumpFamilyProgramDomain
 Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte riscv.Utility.Utility riscv.Spec.Decode
 TmplBzInv.BzTmplInv TmplBzExIface.BzTmplExIface TmplBzExImm.BzTmplExImm TmplBzExCmp.BzTmplExCmp TmplBzLink.BzTmplLink TmplBzNOne.BzTmplNOne
 TmplBzDisp2.BzTmplDisp2 TmplBzTrIsa.BzTmplTrIsa TmplBzTrCore.BzTmplTrCore.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment CPUDatapathFacts CPUISARegView CPUImmediateShapes CV32E40PReq40StateRel CV32E40PDataOpExecution
 BzeenoLoadUseJalASTConfigured3122be4a95 TmplBzNOne.BzTmplNOne.BzTmplNOne.
Local Open Scope Z_scope.
Module BzTmplTrCls.
Notation P := bzeeno_load_use_jal_program (only parsing).
Module EI := TmplBzExIface.BzTmplExIface.BzTmplExIface.
Module BzI := TmplBzExImm.BzTmplExImm.BzTmplExImm.
Module BzC := TmplBzExCmp.BzTmplExCmp.BzTmplExCmp.
Module Lk := TmplBzLink.BzTmplLink.BzTmplLink.
Module Dp := TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Module Is := TmplBzTrIsa.BzTmplTrIsa.BzTmplTrIsa.
Module Co := TmplBzTrCore.BzTmplTrCore.BzTmplTrCore.
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Module PD := Ex.External.CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.
Section Cls.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Local Notation uw := word.unsigned.
Local Notation reg := formal_register_word.

Lemma shamt_facts w : bitSlice w 25 26 = 0 -> 0 <= bitSlice w 20 26 /\ bitSlice w 20 26 < 32 /\ norm 5 (bitSlice w 20 26) = bitSlice w 20 26.
Proof. intro H. rewrite <- (shamt5 w H). pose proof (norm_bounds 5 (Z.shiftr w 20)) as [B0 B1]. change (2 ^ Z.of_nat 5) with 32 in B1.
 split; [exact B0|]. split; [exact B1|]. apply norm_idempotent. Qed.
"""


def pattern(n, vars_=None):
    f = FIELDS[n]
    return 'Decode.' + n + ''.join(' ' + (vars_ or {}).get(x, x) for x in f)


def prem_args(meta_cl, w='w'):
    common, scen = meta_cl
    prem = [(f[0], f[1]) for f in common if f[0][0] == 'EVar']
    args = []
    for e, v in prem:
        wire = int(e[2])
        if wire == 142:
            args.append('H142')
        else:
            args.append(f'(ltac:(rewrite (Lk.{SLICE[wire]} seed D HL), Hw; slice_goal {w}))')
    return args


def cmpid(sets, cl):
    import cpu_tmpl_factcheck as FC
    ids = sorted({e[2] for k, fl in sets.items() if re.match(f'facts_{cl}_f', k) for e, v in fl if e[0] == 'EVar' and (e, v) not in sets[f'facts_{cl}_f00_c11' if False else k] and False})
    return ids


def build():
    sets, gp, metas = TB.meta()
    cls = [c['name'] for c in isa.classes()]
    L = [HEAD.replace('@AUTHOR@', AUTHOR)]
    # which classes have a compare-bit premise in <C>_o (second return of meta: scen keys with non-empty cmpbit)
    hasx = {cl: any(k[1] != '' for k in metas[cl][1]) for cl in cls}
    gen_prem = ('CombLFP P seed D -> norm 1 (read_signal D 153%nat) = 0 -> norm 1 (read_signal D 151%nat) = 0 -> norm 1 (read_signal D 142%nat) = 1 ->\n'
                ' norm 32 (read_signal D 140%nat) = w -> Decode.decode Decode.RV32I w = Decode.IInstruction (@PAT@) ->\n'
                ' (norm 2 (read_signal D 160%nat) = Dp.ASEL D -> forall r, r = bitSlice w 15 20 -> norm 32 (read_signal D 204%nat) = uw (reg c r)) ->\n'
                ' (norm 2 (read_signal D 161%nat) = Dp.BSEL D -> forall r, r = bitSlice w 20 25 -> norm 32 (read_signal D 210%nat) = uw (reg c r)) ->\n'
                ' norm 32 (read_signal S 139%nat) = uw (getPc c) -> norm 32 (read_signal S 138%nat) = uw (word.add (getPc c) (word.of_Z 4 : word)) ->\n'
                ' Co.Post S D S1 -> BzTmplInv.ExCl S1 c (@PAT@) /\\ norm 1 (read_signal D 163%nat) = 0 /\\ norm 1 (read_signal D 164%nat) = 0.')
    for n in cls:
        f = FIELDS[n]
        k = KIND[n]
        pat = pattern(n)
        fl = ' '.join(f)
        L.append(f'Theorem tr_{n} seed (D S S1 : State) (c : FormalSpec.State) (w {fl} : Z) :')
        L.append(' ' + gen_prem.replace('@PAT@', pat))
        pr = prem_args(metas[n])
        hx = ' (bit_cases _)' if hasx[n] else ''
        # note: the cmp-bit premise of <C>_o is a disjunction on the compare wire
        inv_args = fl
        L.append(' Proof. intros HL H153 H151 H142 Hw Hdec HA HB HPC HLK HP.')
        L.append(f' destruct (Inv.inv_{n} w {inv_args} Hdec) as [Hf Hs]. repeat match goal with H : _ /\\ _ |- _ => destruct H end.')
        L.append(f' pose proof (Dp.{n}_o seed D HL H153 H151 H142 ' + ' '.join(pr[1:]) + (' (Co.bit_cases _)' if hasx[n] else '') + ') as O.')
        L.append(' destruct O as [_ [Hsa [Hsb [c158 [c162 [c163 [c164 [c165 [c166 [c168 [c169 [c173 [c174 c175]]]]]]]]]]]]].')
        A = f[1] if k in ('R', 'Rslt', 'I', 'Islt', 'Ish') else None
        B = f[2] if k in ('R', 'Rslt') else None
        if A:
            L.append(f' assert (A1 : norm 32 (read_signal D 204%nat) = uw (reg c {A})) by (apply (HA Hsa); assumption).')
        if B:
            L.append(f' assert (B1 : norm 32 (read_signal D 210%nat) = uw (reg c {B})) by (apply (HB Hsb); assumption).')
        if k in ('I', 'Islt', 'Lui', 'Auipc'):
            imm = f[2] if k in ('I', 'Islt') else f[1]
            fn = IMMFN.get(n, 'isa_imm_I')
            L.append(f' pose proof (BzI.{n}_imm seed D w) as Hi0. repeat (specialize (Hi0 ltac:(assumption))).')
            L.append(f' assert (HI : norm 32 (read_signal D 30%nat) = norm 32 {imm}) by (rewrite Hi0; unfold {fn}; match goal with H : {imm} = _ |- _ => rewrite H end; reflexivity).')
        if k == 'Ish':
            sh = f[2]
            L.append(f' pose proof (BzI.{n}_imm seed D w) as Hi0. repeat (specialize (Hi0 ltac:(assumption))).')
            L.append(f' destruct (shamt_facts w ltac:(assumption)) as [HS1 [HS2 HS3]].')
            L.append(f' assert (HSH1 : 0 <= {sh}) by (match goal with H : {sh} = _ |- _ => rewrite H end; exact HS1).')
            L.append(f' assert (HSH2 : {sh} < 32) by (match goal with H : {sh} = _ |- _ => rewrite H end; exact HS2).')
            L.append(f' assert (HSH3 : norm 5 (norm 32 (read_signal D 30%nat)) = {sh}) by (rewrite Hi0; match goal with H : {sh} = _ |- _ => rewrite H end; exact HS3).')
        if k == 'Rslt':
            L.append(f' pose proof (BzC.{n}_cmp seed D (uw (reg c {A})) (uw (reg c {B}))) as Hc0. repeat (specialize (Hc0 ltac:(assumption))). destruct Hc0 as [_ [_ HCMP]].')
        if k == 'Islt':
            L.append(f' pose proof (BzC.{n}_cmp seed D (uw (reg c {A})) (norm 32 {f[2]})) as Hc0. repeat (specialize (Hc0 ltac:(assumption))). destruct Hc0 as [_ [_ HCMP]].')
        L.append(' refine (conj _ (conj c163 c164)).')
        L.append(' cbn [BzTmplInv.ExCl]. ' + f'unfold EI.ExPrem_{n}.' if k != 'B' else ' cbn [BzTmplInv.ExCl].')
        if k == 'Ish':
            L.append(' exists (norm 32 (read_signal D 30%nat)).')
        L.append(' ' + ' '.join(f'try rewrite (Co.p{r} _ _ _ HP);' for r in PREG))
        L.append(' repeat split; first [ assumption | reflexivity ].')
        L.append('Qed.')
    # exval
    for n in cls:
        k = KIND[n]
        if k == 'B':
            continue
        f = FIELDS[n]
        fl = ' '.join(f)
        pat = pattern(n)
        res = 'uw (word.add (getPc c) (word.of_Z 4 : word))' if k in ('Jal', 'Jalr') else f'uw (result_word c ({pat}))'
        L.append(f'Theorem exval_{n} seed (D S : State) (c : FormalSpec.State) ({fl} : Z) : CombLFP P seed D -> Co.DSame D S -> BzTmplInv.ExCl S c ({pat}) ->')
        L.append(f' norm 32 (read_signal D 259%nat) = {res}.')
        L.append(' Proof. intros HL HS Hex. cbn [BzTmplInv.ExCl] in Hex. repeat match goal with H : _ /\\ _ |- _ => destruct H | H : exists _, _ |- _ => let b := fresh "b" in destruct H as [b H] end.')
        L.append(f' unfold EI.ExPrem_{n} in *. repeat match goal with H : _ /\\ _ |- _ => destruct H end.')
        L.append(' ' + ' '.join(f'try rewrite <- (Co.d{r} _ _ HS) in *;' for r in DREG))
        L.append(f' assert (HPD : EI.ExPrem_{n} D) by (unfold EI.ExPrem_{n}; repeat split; assumption).')
        ex = ' b' if k == 'Ish' else ''
        arg = {'Jal': '', 'Jalr': ''}.get(k, f' {fl}')
        L.append(f' eapply (EI.{n}_ex_isa seed D c{arg}{ex} HL); first [ assumption | (split; assumption) ].')
        L.append(' Qed.')
    # dispatchers
    all_args = lambda n: ' '.join('_' for _ in FIELDS[n])
    alts = ' | '.join(f'exact (tr_{n} seed D S S1 c w {all_args(n)} HL H153 H151 H142 Hw Hdec HA HB HPC HLK HP)' for n in cls)
    L.append('Theorem tr_all seed (D S S1 : State) (c : FormalSpec.State) (w : Z) (i : Decode.InstructionI) :')
    L.append(' PD.legal_instruction i = true -> ' + gen_prem.replace('@PAT@', 'i') .replace('Decode.IInstruction (i)', 'Decode.IInstruction i').replace('c (i)', 'c i'))
    L.append(' Proof. intros Hleg HL H153 H151 H142 Hw Hdec HA HB HPC HLK HP. destruct i; try (vm_compute in Hleg; discriminate Hleg).')
    L.append(' all: first [ ' + alts + ' ].')
    L.append('Qed.')
    alts = ' | '.join(f'exact (exval_{n} seed D S c {all_args(n)} HL HS Hex)' for n in cls if KIND[n] != 'B')
    L.append('Theorem exval_all seed (D S : State) (c : FormalSpec.State) (i : Decode.InstructionI) : PD.legal_instruction i = true -> Is.dwr i = true -> CombLFP P seed D -> Co.DSame D S -> BzTmplInv.ExCl S c i ->')
    L.append(' norm 32 (read_signal D 259%nat) = uw (Is.dval c i).')
    L.append(' Proof. intros Hleg Hd HL HS Hex. destruct i; try (vm_compute in Hleg; discriminate Hleg); try discriminate Hd.')
    L.append(' all: first [ ' + alts + ' ].')
    L.append('Qed.')
    # rd_inv
    dest = TI.dest_classes()
    ralts = ' | '.join(f'(destruct (Inv.inv_{n} w {" ".join("_" for _ in FIELDS[n])} Hdec) as [[H _] _]; exact H)' for n in dest)
    L.append('Lemma rd_inv w (i : Decode.InstructionI) : Decode.decode Decode.RV32I w = Decode.IInstruction i -> Is.dwr i = true -> Is.drd i = bitSlice w 7 12.')
    L.append(' Proof. intros Hdec Hd. destruct i; try discriminate Hd.')
    L.append(' all: first [ ' + ralts + ' ].')
    L.append('Qed.')
    L.append('End Cls.\nEnd BzTmplTrCls.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    names = ['tr_all', 'exval_all', 'rd_inv', 'shamt_facts']   # the per-class lemmas are in the closure of the dispatchers
    L.extend(f'Print Assumptions BzTmplTrCls.{e}.' for e in names)
    return '\n'.join(L) + '\n'


if __name__ == '__main__':
    Path(sys.argv[1]).write_text(build())
