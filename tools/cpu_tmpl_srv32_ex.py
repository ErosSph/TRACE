#!/usr/bin/env python3
"""srv32 EX-stage facts per ISA class (29 classes), on the planner/session/emitter of tools/cpu_tmpl_bzex.py (design independent
parts reused unchanged; the srv32 specs below are new).  For a comb fixed point d and the ex_* registers holding the values the
instruction decode gives for class C (the determined flags of the class, found by sampling the capture decode), the EX wires
ex_result (323), next_pc (324), branch_taken (325) have the class values on the operand wires alu_op1/alu_op2 (247/248).
Untrusted generator; Coq checks every equation.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse
import json
import random
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_bzex as B
import cpu_isa_classes as isa
import srv32_inv_sim as SIM

R_ = dict(memwr=257, jal=266, jalr=267, lui=264, auipc=265, csr=262, mul=288, alu=261, alu_op=255, subtype=256, branch=268,
          system=269, imm_sel=251)
A, Bo, PC, IMM, FL, FE, SUB = 247, 248, 241, 250, 272, 239, 321
B.PREAMBLE = B.PREAMBLE.replace('Ex.External.CPUDatapathFacts @AST@.', 'Ex.External.CPUDatapathFacts Ex.External.CPUSubSign33 Lang.ExtendedSVBankAlignment @AST@.')
RANGES = ('assert (Ra : 0 <= a < 2 ^ 32) by (rewrite <- Hn0; rewrite ExtendedSVBankAlignment.norm_mod; apply Z.mod_pos_bound; cbn; lia). '
          'assert (Rb : 0 <= b < 2 ^ 32) by (rewrite <- Hn1; rewrite ExtendedSVBankAlignment.norm_mod; apply Z.mod_pos_bound; cbn; lia). ')
CLOSE_SLT = ('cnorm. ' + RANGES + 'change (Z.lor (Z.shiftl (norm 1 (Z.shiftr a 31)) (Z.of_nat 32)) a) with (CPUSubSign33.sx a). '
             'change (Z.lor (Z.shiftl (norm 1 (Z.shiftr b 31)) (Z.of_nat 32)) b) with (CPUSubSign33.sx b). '
             'rewrite (CPUSubSign33.slt_signbit a b Ra Rb). destruct (signed_value 32 a <? signed_value 32 b); reflexivity.')
CLOSE_SLTU = ('cnorm. ' + RANGES + 'rewrite (CPUSubSign33.sltu_signbit a b Ra Rb). destruct (a <? b); reflexivity.')
CLOSE_LINK = 'cnorm. repeat first [rewrite Hn0 | rewrite Hm0 | rewrite norm_lo by lia | rewrite norm_wide by lia]. rewrite (Z.add_comm 4 pc). reflexivity.'
CLOSE_NEXT = ('try rewrite hc9. cnorm. repeat (apply conj).\n 1: (repeat rewrite norm_self; rewrite rtl_clear0; reflexivity).\n all: (cnorm; repeat first [{HN} | reflexivity]).')
CLOSE_NEXT0 = 'cnorm. repeat (apply conj).\n all: (cnorm; repeat first [{HN} | reflexivity]).'
CLOSERS = dict(Slt=CLOSE_SLT, Slti=CLOSE_SLT, Sltu=CLOSE_SLTU, Sltiu=CLOSE_SLTU, Jal=CLOSE_LINK, Jalr=CLOSE_LINK)


def flag_values(c):
    """flag -> value for the flags the class determines (constant over random words of the class), + csr/mul (0 by decode)"""
    rng = random.Random(7)
    seen = {}
    for _ in range(300):
        w = rng.getrandbits(32)
        w = (w & ~0x7f) | c['opcode']
        if c['funct3'] is not None:
            w = (w & ~(7 << 12)) | (c['funct3'] << 12)
        if c['funct7'] is not None:
            w = (w & ~(0x7f << 25)) | (c['funct7'] << 25)
        elif c['name'] in ('Slli', 'Srli', 'Srai'):
            w = (w & ~(0x7f << 25)) | ((32 if c['name'] == 'Srai' else 0) << 25)
        m = SIM.mirror_decode(w)
        op = w & 127
        m['csr'] = int(op == 0x73 and ((w >> 12) & 7) != 0)
        m['mul'] = 0
        for k in R_:
            key = {'alu_op': 'alu_op'}.get(k, k)
            if key in m:
                seen.setdefault(k, set()).add(m[key])
    return {k: next(iter(v)) for k, v in seen.items() if len(v) == 1}


def wire_specs():
    SX = 'CPUSubSign33.sx'
    return [B.Spec('Sub_wire', [], [(A, 'a'), (Bo, 'b')], [(321, f'norm 33 (norm 33 (norm 33 ({SX} a) - norm 33 ({SX} b)))')], kind='gen',
                   closer='cnorm. unfold CPUSubSign33.sx. repeat first [{HN}]. reflexivity.'),
            B.Spec('Subu_wire', [], [(A, 'a'), (Bo, 'b')], [(322, 'norm 33 (norm 33 (norm 33 a - norm 33 b))')], kind='gen')]


def arm_exprs(f3):
    """(ECond condition, SIf guard) of the f3 arm of the branch process (process 80), read from the AST"""
    a = T.Ast('experiments/framework/generated/srv32/Srv32AST.v', 'experiments/framework/generated/srv32/report.json')
    seq = a.procs[80]['body'][1][0][1]
    case = [x for x in seq if x[0] == 'SCase'][0]
    inner = [b for key, b in case[2] if key == ('EVar', 1, 268)][0][1][0]
    for k2, b2 in inner[2]:
        if k2 == ('EConst', 3, f3):
            cond = [x for x in b2[1] if x[0] == 'SAssign'][0][2][2]
            guard = [x for x in b2[1] if x[0] == 'SIf'][0][1]
            return cond, guard
    raise KeyError(f3)


def evb(e, wire, s):
    """value of a 1-bit condition over the wire (id) holding the 33-bit value s"""
    k = e[0]
    if k == 'EBinary':
        l, r = evb(e[3], wire, s), evb(e[4], wire, s)
        return int(l == r) if e[2] == 'BEq' else int(l != r)
    if k == 'EConst':
        return e[2]
    if k == 'EVar':
        return s
    if k == 'ESel':
        return (s >> 32) & 1
    if k == 'EUnary':
        return 1 - evb(e[3], wire, s)
    if k == 'ECond':
        # guarded expression (tmpl-econd-casesplit): the guard is opaque, the fact is stated with the `no` branch's value and
        # the generated assertion is proved by case-splitting on the guard, so it must hold in BOTH branches (Coq rejects it
        # otherwise; this mirror only proposes the value)
        return evb(e[4], wire, s)
    raise ValueError(k)


def guard_roots(e, acc=None):
    """roots read by the guards of the ECond nodes of e (in order, no duplicates)"""
    acc = [] if acc is None else acc
    if e[0] == 'ECond':
        for _, r in B.X.inputs(e[2]):
            if r not in acc:
                acc.append(r)
    for c in e[1:]:
        if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
            guard_roots(c, acc)
    return acc


def branch_specs(c):
    n, f3, cond = c['name'], c['funct3'], c['cond']
    ce, ge = arm_exprs(f3)
    unsigned = n in ('Bltu', 'Bgeu')
    wire = 322 if unsigned else 321
    eqtype = n in ('Beq', 'Bne')
    base = 'Z.eqb a b' if eqtype else ('Z.ltb a b' if unsigned else 'Z.ltb (signed_value 32 a) (signed_value 32 b)')
    out = []
    for taken in (True, False):
        # sample wire value realising the scenario: s = 0 / 1 (eq), bit32 = 0 / 1 (sign)
        pv = {'Beq': True, 'Bne': False, 'Blt': True, 'Bge': False, 'Bltu': True, 'Bgeu': False}[n] == taken
        sample = (0 if pv else 1) if eqtype else ((1 << 32) if pv else 0)
        facts = [(ce, evb(ce, wire, sample)), (ge, evb(ge, wire, sample))]
        wname = 'Subu_wire' if unsigned else 'Sub_wire'
        pre = [f'pose proof ({wname} seed d a b HL hd0 hd1) as W.', RANGES.replace('Hn0', 'hd0').replace('Hn1', 'hd1'),
               f'assert (Hp : {base} = {"true" if pv else "false"}) by (destruct ({base}) eqn:E; cbn in hx0; first [discriminate | reflexivity]).']
        for j, (e, v) in enumerate(facts):
            if eqtype:
                body = 'rewrite (CPUSubSign33.sub33_zero a b Ra Rb), Hp; reflexivity'
            elif unsigned:
                body = 'rewrite (CPUSubSign33.sltu_signbit a b Ra Rb), Hp; reflexivity'
            else:
                body = 'rewrite (CPUSubSign33.slt_signbit a b Ra Rb), Hp; reflexivity'
            gr = guard_roots(e) if B.OPAQUE_GUARDS else []
            if gr:   # opaque ECond guard in the arm condition: case-split, the fact must hold in both branches
                pre.append(f'assert (Hg{j} : eval_expr d {T.coq(e)} = {v}) by (cbn [eval_expr]; try change (norm 33 0) with 0; try change (norm 6 32) with 32; '
                           f'{B.opaque_split(gr)}; try rewrite W; {body}).')
                continue
            pre.append(f'assert (Hg{j} : eval_expr d {T.coq(e)} = {v}) by (cbn [eval_expr]; try change (norm 33 0) with 0; try change (norm 6 32) with 32; rewrite W; {body}).')
        tg = [(324, 'norm 32 (Z.add pc imm)' if taken else 'norm 32 (Z.add 4 fe)'), (325, '1' if taken else '0')]
        consts = [(R_['jal'], 0), (R_['jalr'], 0), (R_['branch'], 1), (R_['alu_op'], f3), (FL, 0)]
        out.append(B.Spec(f'{n}_ex_branch_{"t" if taken else "n"}', consts, [(A, 'a'), (Bo, 'b'), (PC, 'pc'), (IMM, 'imm'), (FE, 'fe')], tg,
                          extra_hyps=[f'({cond}) = {"true" if taken else "false"}'], derived=facts, pre=pre, kind='branch',
                          closer='try rewrite hc4. cnorm. repeat (apply conj).\n all: (cnorm; repeat first [{HN} | reflexivity]).'))
    return out


def wires_specs():
    z = [B.Spec('if_stall_zero', [(232, 0)], [], [(236, '0')], kind='wires'),
         B.Spec('ex_stall_zero', [(232, 0), (258, 0)], [], [(237, '0')], kind='wires'),
         B.Spec('wb_stall_zero', [(232, 0)], [(292, 'wm'), (293, 'wr')], [(238, '0')], kind='wires'),
         B.Spec('ex_flush_or', [], [(295, 'b0'), (296, 'b1')], [(272, 'norm 1 (Z.lor b0 b1)')], kind='wires'),
         B.Spec('wb_flush_or', [], [(298, 'n'), (299, 'm')], [(305, 'norm 1 (Z.lor n m)')], kind='wires'),
         B.Spec('alu_op1_copy', [], [(245, 'r')], [(247, 'norm 32 r')], kind='wires'),
         B.Spec('alu_op2_imm', [(251, 1)], [(250, 'imm')], [(248, 'norm 32 imm')], kind='wires'),
         B.Spec('alu_op2_reg', [(251, 0)], [(246, 'r2')], [(248, 'norm 32 r2')], kind='wires'),
         B.Spec('ex_trap_valid', [(272, 0), (279, 0), (280, 0), (258, 0), (257, 0), (269, 0), (270, 0), (23, 0), (24, 0), (25, 0), (262, 0)],
                [(324, 'np'), (255, 'aop'), (259, 'ma'), (310, 'ms'), (313, 'me')], [(274, '0'), (275, '0')], extra_hyps=['norm 2 np = 0'], kind='wires')]
    for sp in z:
        sp.closer = 'cnorm. ' + ''.join(f'try rewrite hc{i}. ' for i in range(len(sp.consts))) + 'try change (norm 1 (Z.lnot 1)) with 0. try change (norm 1 (Z.lnot 0)) with 1. repeat (progress (rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r; cnorm)). try rewrite Z.shiftr_0_r; try rewrite hx0; repeat (progress (rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r; cnorm)). repeat (apply conj).\n all: (cnorm; repeat first [{HN} | reflexivity]).'
    return z


def specs(P, kinds=('gen', 'alu', 'branch', 'next', 'wires', 'op')):
    out = wire_specs() + wires_specs() + operand_specs()
    for c in isa.classes():
        n, k = c['name'], c['kind']
        fv = flag_values(c)
        consts = [(R_[x], v) for x, v in fv.items() if x in ('memwr', 'jal', 'jalr', 'lui', 'auipc', 'csr', 'mul', 'alu', 'alu_op', 'subtype', 'branch')]
        if k == 'branch':
            out += branch_specs(c)
            continue
        fl0 = consts + [(FL, 0)]
        if k in ('jal', 'jalr'):
            base, bn = ((PC, 'pc'), 'pc') if k == 'jal' else ((A, 'a'), 'a')
            out.append(B.Spec(f'{n}_ex_next', fl0, [base, (IMM, 'imm')],
                              [(324, f'norm 32 (Z.shiftl (Z.shiftr (norm 32 (Z.add {bn} imm)) 1) 1)'), (325, '1'), (280, '0')], kind='next',
                              closer=CLOSE_NEXT.replace('hc9', f'hc{len(fl0) - 1}')))
        else:
            out.append(B.Spec(f'{n}_ex_next', fl0, [(FE, 'fe')], [(324, 'norm 32 (Z.add 4 fe)'), (325, '0'), (280, '0')], kind='next', closer=CLOSE_NEXT0))
        if k in ('jal', 'jalr'):
            out.append(B.Spec(f'{n}_ex_result', consts, [(PC, 'pc')], [(323, 'norm 32 (Z.add pc 4)')], kind='alu', closer=CLOSERS[n]))
        elif n == 'Lui':
            out.append(B.Spec(f'{n}_ex_result', consts, [(IMM, 'b')], [(323, 'norm 32 b')], kind='alu'))
        elif n == 'Auipc':
            out.append(B.Spec(f'{n}_ex_result', consts, [(PC, 'pc'), (IMM, 'b')], [(323, 'norm 32 (Z.add pc b)')], kind='alu'))
        else:
            out.append(B.Spec(f'{n}_ex_result', consts, [(A, 'a'), (Bo, 'b')], [(323, f'norm 32 ({c["value"]})')], kind='alu', closer=CLOSERS.get(n, '')))
    return [x for x in out if x.kind in kinds]


IDX12 = '''Lemma idx12 x : norm 12 (norm 5 x * 32) = 32 * norm 5 x.
Proof. rewrite !ExtendedSVBankAlignment.norm_mod. change (Z.of_nat 5) with 5. change (Z.of_nat 12) with 12.
 assert (E5 : 2 ^ 5 = 32) by reflexivity. assert (E12 : 2 ^ 12 = 4096) by reflexivity. rewrite E5, E12.
 pose proof (Z.mod_pos_bound x 32 ltac:(lia)). rewrite Z.mod_small by lia. lia. Qed.'''


def run(names, module, kinds=('gen', 'alu', 'branch', 'next', 'wires', 'op')):
    P = B.Planner('srv32')
    sp = specs(P, kinds)
    if names != 'all':
        sp = [s for s in sp if s.kind in ('gen', 'wires', 'op') or s.name.split('_')[0] in names.split(',')]
    return B.module_text(P, sp, module, extra_defs=OPDEFS + '\n' + IDX12)


# ---------------------------------------------------------------------------------------------------------------------------
# operand ports (reg_rdata1/2 = 245/246): x0 guard, WB forwarding, bank lane; three scenarios per port (conditions decided by facts)
OPDEFS = '''Lemma bit_cases f : norm 1 f = f -> f = 0 \\/ f = 1.
Proof. intro H. rewrite ExtendedSVBankAlignment.norm_mod in H. pose proof (Z.mod_pos_bound f (2 ^ Z.of_nat 1) ltac:(cbn; lia)). cbn in *. lia. Qed.'''


def operand_specs():
    out = []
    for nm, sel, port in (('rdata1', 252, 245), ('rdata2', 253, 246)):
        c1t = ('EBinary', 1, 'BEq', ('EConst', 5, 0), ('EVar', 5, sel))
        c2t = ('EBinary', 1, 'BAnd', ('EBinary', 1, 'BAnd', ('EUnary', 1, 'UNot', ('EVar', 1, 305)), ('EVar', 1, 289)), ('EBinary', 1, 'BEq', ('EVar', 5, 294), ('EVar', 5, sel)))
        C1, C2 = T.coq(c1t), T.coq(c2t)
        datas = [(sel, 's'), (305, 'f'), (289, 'wa'), (294, 'wd'), (293, 'wm'), (304, 'wr'), (290, 'wres'), (244, 'bank')]
        head = 'cbn [eval_expr]; rewrite ?hd0, ?hd1, ?hd2, ?hd3; try change (norm 5 0) with 0; '
        nb = ('assert (Nf : norm 1 f = f) by (rewrite <- hd1; apply norm_idempotent). assert (Na : norm 1 wa = wa) by (rewrite <- hd2; apply norm_idempotent). ')
        # A: s = 0
        out.append(B.Spec(f'{nm}_zero', [], datas, [(port, '0')], extra_hyps=['s = 0'], derived=[(c1t, 1)],
                          pre=[f'assert (Hg0 : eval_expr d {C1} = 1) by ({head}rewrite hx0; vm_compute; reflexivity).'], kind='op',
                          closer='cnorm. repeat first [{HN} | reflexivity].'))
        # B: forwarded
        out.append(B.Spec(f'{nm}_fwd', [], datas, [(port, 'norm 32 (if wm =? 0 then wres else wr)')],
                          extra_hyps=['s <> 0', 'f = 0', 'wa = 1', 'wd = s'], derived=[(c1t, 0), (c2t, 1)],
                          pre=[f'assert (Hg0 : eval_expr d {C1} = 0) by ({head}assert (Hs : (0 =? s) = false) by (apply Z.eqb_neq; lia); rewrite Hs; reflexivity).',
                               f'assert (Hg1 : eval_expr d {C2} = 1) by ({head}rewrite hx1, hx2, hx3, Z.eqb_refl; vm_compute; reflexivity).'],
                          kind='op', closer='cnorm. repeat first [{HN} | reflexivity].'))
        # C: bank lane
        out.append(B.Spec(f'{nm}_bank', [], datas, [(port, 'norm 32 (Z.shiftr bank (32 * norm 5 (s - 1)))')],
                          extra_hyps=['s <> 0', '~ (f = 0 /\\ wa = 1 /\\ wd = s)'], derived=[(c1t, 0), (c2t, 0)],
                          pre=[f'assert (Hg0 : eval_expr d {C1} = 0) by ({head}assert (Hs : (0 =? s) = false) by (apply Z.eqb_neq; lia); rewrite Hs; reflexivity).',
                               nb + f'assert (Hg1 : eval_expr d {C2} = 0) by ({head}destruct (bit_cases f Nf) as [-> | ->]; destruct (bit_cases wa Na) as [-> | ->]; '
                               'destruct (Z.eqb wd s) eqn:Eq; vm_compute; try reflexivity; exfalso; apply hx1; repeat split; try reflexivity; apply Z.eqb_eq; assumption).'],
                          kind='op', closer='cnorm. rewrite idx12. repeat first [{HN} | reflexivity].'))
    return out


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--classes', default='all')
    ap.add_argument('--module', default='Srv32ExAlu')
    ap.add_argument('--out', required=True)
    a = ap.parse_args()
    text, exports, info = run(a.classes, a.module)
    Path(a.out).write_text(text)
    print(a.out, len(text.splitlines()), json.dumps(info)[:300])


