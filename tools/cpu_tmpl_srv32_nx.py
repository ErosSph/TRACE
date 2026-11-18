#!/usr/bin/env python3
"""srv32 template route: next-value lemmas of one clock cycle (rise tree on the driven state + fall frame) for the registers of the invariant,
stated under the wire/register facts they read.  Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_srv32_step as S

BASE = 'TmplSrv32Base.Srv32Base.Srv32Base'
HEAD = '''From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqTree Lang.ExtendedSVBankAlignment Lang.ExtendedSVBitSlice Lang.ExtendedSVRegisterBank
 Ex.External.CPUDatapathFacts Srv32.Srv32AST TmplSrv32Base.Srv32Base TmplSrv32Rf.Srv32Rf.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVSeqTree CPUDatapathFacts Srv32AST Srv32Base.Srv32Base.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module @MOD@.
Ltac fin2 := try change (norm 1 (Z.lnot 1)) with 0; try change (norm 1 (Z.lnot 0)) with 1; rewrite ?Z.land_0_r, ?Z.land_0_l, ?Z.lor_0_l, ?Z.lor_0_r; fin.
'''
# (register, width, process) of the rise trees
ROWS = {r: (w, k) for r, w, k in S.stage_rows()}


def dw(k, w, v):
    return f'norm {w} (read_signal (D s) {k}%nat) = {v}'


def rs(k, w, v):
    return f'norm {w} (read_signal s {k}%nat) = {v}'


class Nx:
    def __init__(self, name, reg, vars_, hyps, concl, norms=(), fin='fin.'):
        self.name, self.reg, self.vars_, self.hyps, self.concl, self.norms, self.fin = name, reg, vars_, hyps, concl, list(norms), fin


def lemmas():
    L = []
    A = L.append
    # 1-bit/word copies and constants (valid and flushed tokens alike)
    A(Nx('nx_232', 232, [], [dw(20, 1, 0)], '0'))
    A(Nx('nx_234', 234, ['a'], [rs(232, 1, 'a')], 'a', norms=[('a', 1)]))
    A(Nx('nx_240', 240, ['f'], [dw(238, 1, 0), rs(239, 32, 'f')], 'f', norms=[('f', 32)]))
    A(Nx('nx_241', 241, ['f'], [dw(236, 1, 0), rs(240, 32, 'f')], 'f', norms=[('f', 32)]))
    A(Nx('nx_250', 250, ['im'], [dw(236, 1, 0), dw(320, 32, 'im')], 'im', norms=[('im', 32)]))
    A(Nx('nx_239_fl', 239, ['f'], [dw(237, 1, 0), dw(272, 1, 1), rs(239, 32, 'f')], 'norm 32 (Z.add 4 f)', norms=[('f', 32)]))
    A(Nx('nx_239_nf', 239, ['np'], [dw(237, 1, 0), dw(272, 1, 0), dw(274, 1, 0), dw(324, 32, 'np')], 'norm 32 (Z.shiftl (Z.shiftr np 1) 1)', norms=[('np', 32)], fin='simp_if; repeat rewrite ?norm_idempotent; rewrite rtl_clear0; reflexivity.'))
    A(Nx('nx_290', 290, ['r'], [dw(237, 1, 0), dw(323, 32, 'r')], 'r', norms=[('r', 32)]))
    A(Nx('nx_294', 294, ['d'], [dw(237, 1, 0), rs(254, 5, 'd')], 'd', norms=[('d', 5)]))
    A(Nx('nx_293', 293, ['m'], [dw(237, 1, 0), rs(258, 1, 'm')], 'm', norms=[('m', 1)]))
    A(Nx('nx_295', 295, ['b', 't'], [dw(237, 1, 0), dw(325, 1, 'b'), dw(274, 1, 't')], 'norm 1 (Z.lor b t)', norms=[('b', 1), ('t', 1)]))
    A(Nx('nx_296', 296, ['b'], [dw(237, 1, 0), rs(295, 1, 'b')], 'b', norms=[('b', 1)]))
    g11 = [dw(237, 1, 0), rs(292, 1, 0), dw(32, 1, 1)]
    A(Nx('nx_298', 298, ['b'], g11 + [rs(295, 1, 'b')], 'b', norms=[('b', 1)]))
    A(Nx('nx_299', 299, ['n'], g11 + [rs(298, 1, 'n')], 'n', norms=[('n', 1)]))
    A(Nx('nx_297', 297, ['t'], g11 + [dw(275, 1, 't')], 't', norms=[('t', 1)]))
    A(Nx('nx_292_m0', 292, [], [rs(257, 1, 0), rs(292, 1, 0), dw(32, 1, 1)], '0'))
    A(Nx('nx_292_fl', 292, [], [dw(272, 1, 1), rs(292, 1, 0), dw(32, 1, 1)], '0'))
    for nm, flags in (('alu', (1, 0, 0, 0, 0)), ('lui', (0, 1, 0, 0, 0)), ('auipc', (0, 0, 1, 0, 0)), ('jal', (0, 0, 0, 1, 0)), ('jalr', (0, 0, 0, 0, 1)), ('none', (0, 0, 0, 0, 0))):
        a, l, u, j, jr = flags
        A(Nx(f'nx_289_{nm}', 289, [], [dw(237, 1, 0), rs(261, 1, a), rs(264, 1, l), rs(265, 1, u), rs(266, 1, j), rs(267, 1, jr), rs(262, 1, 0), rs(288, 1, 0),
                                         rs(258, 1, 0), dw(281, 1, 0)], '1' if any(flags) else '0', fin='fin; vm_compute; reflexivity.'))
    return L


import re


def to_d(h):
    """the same hypothesis about the driven state D s (register values are unchanged by the rising edge, drv_R)"""
    return re.sub(r'read_signal s (\d+)%nat', r'read_signal (D s) \1%nat', h)


def text(module='Srv32Nx', lems=None, head=None):
    """optimisation (the one allowed): the proof works on hypotheses about D s only, so no rewriting with drv_R inside the big evaluated tree
    (drv_all cost 10-40 s per lemma); the statement with hypotheses about s is derived from the D-form lemma by small rewrites"""
    L = [(head or HEAD).replace('@MOD@', module)]
    ex = []
    for n in (lems if lems is not None else lemmas()):
        w, k = ROWS[n.reg]
        vs = ' '.join(f'({v}:Z)' for v in n.vars_)
        hyD = ''.join(f' -> {to_d(h)}' for h in n.hyps)
        hy = ''.join(f' -> {h}' for h in n.hyps)
        L.append(f'Theorem {n.name}_D s {vs} : Lo s{hyD} -> norm {w} (read_signal (cycle s) {n.reg}%nat) = {n.concl}.')
        names = ' '.join(f'H{i}' for i in range(len(n.hyps)))
        pf = [f'Proof. intros H {names}.']
        for v, wd in n.norms:
            src = [i for i, h in enumerate(n.hyps) if h.endswith(f'= {v}')][0]
            pf.append(f' assert (N_{v} : norm {wd} {v} = {v}) by (rewrite <- H{src}; apply norm_idempotent).')
        pf.append(f' pose proof (resetb_D s H) as R1.')
        pf.append(f' rewrite (cyc_{n.reg} s H).')
        pf.append(f' let e := eval vm_compute in (texpr {w}%nat {n.reg}%nat (St.tree_of process_{k})) in change (texpr {w}%nat {n.reg}%nat (St.tree_of process_{k})) with e.')
        pf.append(f' cbn [eval_expr].')
        pf.append(' rewrite ?R1' + ''.join(f', ?H{i}' for i in range(len(n.hyps))) + '.')
        if n.norms:
            pf.append(' rewrite ?' + ', ?'.join(f'N_{v}' for v, _ in n.norms) + '.')
        nrw = ('all: try (rewrite ?' + ', ?'.join(f'N_{v}' for v, _ in n.norms) + '; try reflexivity). ') if n.norms else ''
        pf.append(f' {n.fin.replace("fin", "fin2", 1) if n.fin.startswith("fin") else n.fin} {nrw}Qed.')
        L += pf
        L.append(f'Theorem {n.name} s {vs} : Lo s{hy} -> norm {w} (read_signal (cycle s) {n.reg}%nat) = {n.concl}.')
        conv = []
        for i, h in enumerate(n.hyps):
            m = re.match(r'norm \d+ \(read_signal s (\d+)%nat\) = ', h)
            if m:
                conv.append(f' rewrite <- (drv_{m.group(1)} s) in H{i}.')
        L.append(f'Proof. intros H {names}.' + ''.join(conv) + f' exact ({n.name}_D s{"".join(" "+v for v in n.vars_)} H{"".join(" H"+str(i) for i in range(len(n.hyps)))}). Qed.')
        ex.append(f'{module}.{n.name}')
    L.append(f'End {module}.')
    L.append('Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L += [f'Print Assumptions {e}.' for e in ex]
    return '\n'.join(L) + '\n', ex


if __name__ == '__main__':
    t, ex = text()
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()))
