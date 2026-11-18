#!/usr/bin/env python3
"""srv32 template route: comb-wire facts of the driven/settled state used by the one-cycle layer (stall wires, inst, ROM word, immediates,
junk-token wires).  Planner of tools/cpu_tmpl_bzex.py (design independent), srv32 specs new.  Untrusted; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_bzex as B
import cpu_tmpl_srv32_ex as X
B.PREAMBLE = B.PREAMBLE.replace('Lang.ExtendedSVBankAlignment @AST@.', 'Lang.ExtendedSVBankAlignment Lang.ExtendedSVExpressionFold Lang.ExtendedSVCheckedAssignmentBinding @AST@.').replace('Import ListNotations ExtendedSV ', 'Import ListNotations ExtendedSV ExtendedSVCheckedAssignmentBinding ')


def wclose(nconsts):
    return ('cnorm. ' + ''.join(f'try rewrite hc{i}. ' for i in range(nconsts))
            + 'try change (norm 1 (Z.lnot 1)) with 0. try change (norm 1 (Z.lnot 0)) with 1. '
            'repeat (progress (rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r; cnorm)). try rewrite Z.shiftr_0_r; try rewrite hx0; '
            'repeat (progress (rewrite ?Z.land_0_l, ?Z.land_0_r, ?Z.lor_0_l, ?Z.lor_0_r; cnorm)). repeat (apply conj).\n'
            ' all: (cnorm; repeat first [{HN} | reflexivity]).')


IDX7 = '''Lemma idx7 x : norm 12 (Z.shiftl (norm 7 x) (Z.of_nat 5)) = 32 * norm 7 x.
Proof. rewrite !ExtendedSVBankAlignment.norm_mod. change (Z.of_nat 7) with 7. change (Z.of_nat 12) with 12. change (Z.of_nat 5) with 5.
 assert (E7 : 2 ^ 7 = 128) by reflexivity. assert (E12 : 2 ^ 12 = 4096) by reflexivity. rewrite E7, E12.
 pose proof (Z.mod_pos_bound x 128 ltac:(lia)). rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
 rewrite (Z.mod_small (x mod 128 * 32) 4096) by lia. lia. Qed.'''


def specs(P):
    out = []

    def W(name, consts, datas, targets, **kw):
        sp = B.Spec(name, consts, datas, targets, kind='wires', **kw)
        sp.closer = kw.get('closer') or wclose(len(consts))
        out.append(sp)
    W('stall_wires', [(232, 0)], [(258, 'm2r'), (292, 'wm'), (293, 'wr')], [(236, '0'), (237, '0'), (238, '0'), (26, '1'), (5, '1')])
    W('inst_noflush', [(234, 0)], [(12, 'r')], [(233, 'norm 32 r')])
    W('imem_addr_copy', [], [(239, 'fe')], [(4, 'norm 32 fe')])
    W('const_wires', [], [], [(20, '0'), (23, '0'), (24, '0'), (25, '0'), (27, '1'), (29, '1'), (32, '1'), (37, '1'), (39, '1')])
    W('rom_word_val', [], [(2, 'rm'), (4, 'a')], [(13, 'norm 32 (Z.shiftr rm (32 * norm 7 (Z.shiftr a 2)))')],
      closer='cnorm. rewrite Z.lor_0_r, idx7. rewrite norm_idempotent. reflexivity.')
    return out


JUNK_CL = 'cnorm. repeat (apply conj).\n all: (cnorm; repeat first [{HN} | reflexivity]).'


def eqw(P, root):
    """binding lemma of a single-assignment combinational wire: the wire equals its right-hand side evaluated on the fixed point"""
    c = P.ast.comb[root]
    return [f'Definition orig_w{root} : Expr := {T.coq(c["rhs"])}.',
            f'Theorem eq_w{root} seed d : CombLFP P seed d -> norm {c["width"]} (read_signal d {root}%nat) = norm {c["width"]} (eval_expr d orig_w{root}).',
            f'Proof. intro HL. refine (checked_assignment_binding P _ {c["k"]}%nat process_{c["proc"]} false orig_w{root} {c["width"]}%nat {root}%nat seed d eq_refl _ _ _ _ HL).',
            ' all: first [vm_compute; reflexivity | (vm_compute; lia)]. Qed.']


ZCLOSE = 'cbn [eval_expr]. rewrite ?H. change (norm 1 (Z.lnot 1)) with 0. change (norm 1 (Z.lnot 0)) with 1. cnorm. rewrite ?Z.land_0_r, ?Z.land_0_l, ?Z.lor_0_l, ?Z.lor_0_r. cnorm. try reflexivity.'


def guarded_zero(P):
    """wires gated by a factor that is 0 in the situation (flushed token: ex_flush = 1; no load: ex_mem2reg = 0; no store: ex_memwr = 0)"""
    L = []
    for r in (274, 275, 281, 282):
        L += eqw(P, r)
    def th(name, hyp, hv, tgts):
        L.append(f'Theorem {name} seed d : CombLFP P seed d -> norm 1 (read_signal d {hyp}%nat) = {hv} -> ' + ' /\\ '.join(f'norm 1 (read_signal d {r}%nat) = 0' for r in tgts) + '.')
        L.append(f'Proof. intros HL H. repeat apply conj.')
        for r in tgts:
            L.append(f' - rewrite (eq_w{r} seed d HL). unfold orig_w{r}. {ZCLOSE}')
        L.append('Qed.')
    th('flush_zero', 272, 1, [274, 275, 281, 282])
    th('ld_m2r0', 258, 0, [281])
    th('st_mw0', 257, 0, [282])
    return L


def junk_specs(P):
    """branch_taken (325) is 0 in every flushed token (ex_flush = 1) whatever the decoded flags are: scenario theorems over the case of process 80
    (jal / jalr / branch with funct3 / none), the guards of the conditional `branch_taken = 0` assignments given as exact 0/1 hypotheses"""
    out = []
    FL, JAL, JALR, BR, OP = 272, 266, 267, 268, 255
    mk = lambda name, consts, hyps, derived: out.append(B.Spec(name, consts, [], [(325, '0')], extra_hyps=hyps, derived=derived, kind='junk', closer=wclose(len(consts))))
    mk('junk_jal', [(FL, 1), (JAL, 1)], [], [])
    mk('junk_jalr', [(FL, 1), (JAL, 0), (JALR, 1)], [], [])
    mk('junk_none', [(FL, 1), (JAL, 0), (JALR, 0), (BR, 0)], [], [])
    for f3 in range(8):
        base = [(FL, 1), (JAL, 0), (JALR, 0), (BR, 1), (OP, f3)]
        if f3 in (2, 3):
            mk(f'junk_br{f3}', base, [], [])
            continue
        ce, ge = X.arm_exprs(f3)
        for g in (0, 1):
            mk(f'junk_br{f3}_g{g}', base, [f'eval_expr d {T.coq(ge)} = {g}'], [(ge, g)])
    return out


def junk_combine():
    """the combining theorem: case split on the flags and on the 0/1 value of each guard"""
    L = ['Lemma nb1 x : norm 1 x = 0 \\/ norm 1 x = 1.', 'Proof. pose proof (ExtendedSVBankAlignment.norm_bounds 1 x) as H. change (0 <= norm 1 x < 2) in H. lia. Qed.',
         'Lemma nb3 x : norm 3 x = 0 \\/ norm 3 x = 1 \\/ norm 3 x = 2 \\/ norm 3 x = 3 \\/ norm 3 x = 4 \\/ norm 3 x = 5 \\/ norm 3 x = 6 \\/ norm 3 x = 7.',
         'Proof. pose proof (ExtendedSVBankAlignment.norm_bounds 3 x) as H. change (0 <= norm 3 x < 8) in H. lia. Qed.',
         'Lemma ev01 d e : expr_width e = 1%nat -> eval_expr d e = 0 \\/ eval_expr d e = 1.',
         'Proof. intro H. pose proof (ExtendedSVExpressionFold.eval_normalized d e) as E. rewrite H in E. destruct (nb1 (eval_expr d e)) as [A|A]; rewrite E in A; auto. Qed.',
         'Theorem junk_bt0 seed d : CombLFP P seed d -> norm 1 (read_signal d 272%nat) = 1 -> norm 1 (read_signal d 325%nat) = 0.',
         'Proof. intros HL Hf.',
         ' destruct (nb1 (read_signal d 266%nat)) as [Hj|Hj]; [|exact (junk_jal seed d HL Hf Hj)].',
         ' destruct (nb1 (read_signal d 267%nat)) as [Hr|Hr]; [|exact (junk_jalr seed d HL Hf Hj Hr)].',
         ' destruct (nb1 (read_signal d 268%nat)) as [Hb|Hb]; [exact (junk_none seed d HL Hf Hj Hr Hb)|].',
         ' destruct (nb3 (read_signal d 255%nat)) as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]].']
    for f3 in range(8):
        if f3 in (2, 3):
            L.append(f'   + exact (junk_br{f3} seed d HL Hf Hj Hr Hb H0).')
            continue
        ce, ge = X.arm_exprs(f3)
        L.append(f'   + destruct (ev01 d {T.coq(ge)} eq_refl) as [G|G]; [exact (junk_br{f3}_g0 seed d HL Hf Hj Hr Hb H0 G)|exact (junk_br{f3}_g1 seed d HL Hf Hj Hr Hb H0 G)].')
    L.append('Qed.')
    return L

def run(module):
    P = B.Planner('srv32')
    sp = specs(P) + junk_specs(P)
    jc = junk_combine()
    k = [i for i, l in enumerate(jc) if l.startswith('Theorem junk_bt0')][0]
    text, ex, info = B.module_text(P, sp, module, extra_defs=X.OPDEFS + '\n' + X.IDX12 + '\n' + IDX7 + '\n' + '\n'.join(jc[:k]) + '\n' + '\n'.join(guarded_zero(P)), extra_exports=[f'{module}.{n}' for n in ('junk_bt0','flush_zero','ld_m2r0','st_mw0')])
    text = text.replace(f'\nEnd {module}.\n', '\n' + '\n'.join(jc[k:]) + f'\nEnd {module}.\n', 1)
    return text, ex, info


if __name__ == '__main__':
    text, ex, info = run('Srv32Wire')
    Path(sys.argv[1]).write_text(text)
    print(sys.argv[1], len(text.splitlines()))
