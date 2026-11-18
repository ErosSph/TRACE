#!/usr/bin/env python3
"""srv32 closure: the immediate wire 320 (process 53, a case on the opcode of `inst`) per instruction format, via the planner
of tools/cpu_tmpl_bzex.py (design independent; facts = the opcode / funct3 slices of inst).  Each theorem states
norm 32 (read d 320) = eval_expr d FORM, FORM = the accepted RTL immediate shapes (CPUImmediateShapes.imm_U,
CPUImmediateRtlShapes.rimm_J / rimm_I, the srv32 B shape rimm_B2, the shift-amount zero extension).
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0."""
import re, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_tmpl_ast as T, cpu_tmpl_bzex as B, cpu_tmpl_srv32_ex as X

OPC = ('ESel', 7, ('EVar', 32, 233), ('EConst', 5, 0))
F3 = ('ESel', 3, ('EVar', 32, 233), ('EConst', 5, 12))
FORM = {'U': '(CPUImmediateShapes.imm_U (EVar 32 233%nat))', 'J': '(CPUImmediateRtlShapes.rimm_J (EVar 32 233%nat))',
        'I': '(CPUImmediateRtlShapes.rimm_I (EVar 32 233%nat))', 'B': '(rimm_B2 (EVar 32 233%nat))',
        'S': '(EExtend 32 false (ESel 5 (EVar 32 233%nat) (EConst 5 20)))'}
RB2 = ('Definition rimm_B2 (W:Expr) : Expr := EConcat 32 (EReplicate 20 20 (ESel 1 W (EConst 5 31))) (EConcat 12 (ESel 1 W (EConst 5 7)) '
       '(EConcat 11 (ESel 6 W (EConst 5 25)) (EConcat 5 (ESel 4 W (EConst 5 8)) (EConst 1 0)))).')


def run(module):
    P = B.Planner('srv32')
    sp = []

    def mk(name, facts, form):
        hyps = [f'eval_expr d {T.coq(e)} = {v}' for e, v in facts]
        s = B.Spec(name, [], [(233, 'w')], [(320, f'eval_expr d {FORM[form]}')], extra_hyps=hyps, derived=facts, kind='wires')
        s.closer = 'exact (ExtendedSVExpressionFold.eval_normalized d _).'
        sp.append(s)
    for op in (23, 55):
        mk(f'imm_u{op}', [(OPC, op)], 'U')
    mk('imm_j', [(OPC, 111)], 'J')
    mk('imm_jalr', [(OPC, 103)], 'I')
    mk('imm_b', [(OPC, 99)], 'B')
    for f3 in range(8):
        mk(f'imm_a{f3}', [(OPC, 19), (F3, f3)], 'S' if f3 in (1, 5) else 'I')
    # ex_ill_branch (280) is 0 for a valid branch (funct3 in 0,1,4..7), any comparison result
    comb = []
    for f3 in (0, 1, 4, 5, 6, 7):
        ce, ge = X.arm_exprs(f3)
        for g in (0, 1):
            s = B.Spec(f'br_ill{f3}_g{g}', [(272, 0), (266, 0), (267, 0), (268, 1), (255, f3)], [], [(280, '0')],
                       extra_hyps=[f'eval_expr d {T.coq(ge)} = {g}'], derived=[(ge, g)], kind='wires')
            s.closer = 'cnorm. reflexivity.'
            sp.append(s)
        comb += [f'Theorem br_ill{f3} seed d : CombLFP P seed d -> norm 1 (read_signal d 272%nat) = 0 -> norm 1 (read_signal d 266%nat) = 0 -> norm 1 (read_signal d 267%nat) = 0 ->',
                 f' norm 1 (read_signal d 268%nat) = 1 -> norm 3 (read_signal d 255%nat) = {f3} -> norm 1 (read_signal d 280%nat) = 0.',
                 f'Proof. intros HL H0 H1 H2 H3 H4. destruct (ev01 d {T.coq(ge)} eq_refl) as [G|G];',
                 f' [exact (br_ill{f3}_g0 seed d HL H0 H1 H2 H3 H4 G)|exact (br_ill{f3}_g1 seed d HL H0 H1 H2 H3 H4 G)]. Qed.']
    text, ex, info = B.module_text(P, sp, module, extra_defs=X.OPDEFS + '\n' + X.IDX12 + '\n' + RB2, author='LLM-generated: Claude Code (claude-opus-5-5)')
    # keep the binding equation unevaluated: the RHS is the accepted shape up to delta (no symbolic cbn, cheap kernel check)
    text = text.replace('as E320; cbn [eval_expr expr_width] in E320.', 'as E320.')
    text = re.sub(r'\n assert \(Hn0 : norm 32 w = w\)[^\n]*\n assert \(Hm0[^\n]*\n rewrite E320, hd0\.', '\n rewrite E320.', text)
    text = text.replace('(** Srv32.Srv32AST: EX/ID datapath facts (tools/cpu_tmpl_bzex.py).', '(** Srv32.Srv32AST: immediate wire 320 per format (tools/cpu_tmpl_srv32_imm.py over the planner of tools/cpu_tmpl_bzex.py).', 1)
    EV = ['Lemma nb1 x : norm 1 x = 0 \\/ norm 1 x = 1.', 'Proof. pose proof (ExtendedSVBankAlignment.norm_bounds 1 x) as H. change (0 <= norm 1 x < 2) in H. lia. Qed.',
          'Lemma ev01 d e : expr_width e = 1%nat -> eval_expr d e = 0 \\/ eval_expr d e = 1.',
          'Proof. intro H. pose proof (ExtendedSVExpressionFold.eval_normalized d e) as E. rewrite H in E. destruct (nb1 (eval_expr d e)) as [A|A]; rewrite E in A; auto. Qed.']
    text = text.replace(f'\nEnd {module}.\n', '\n' + '\n'.join(EV + comb) + f'\nEnd {module}.\n', 1)
    text = text.replace(' Srv32.Srv32AST.\n', ' Lang.ExtendedSVExpressionFold Srv32.Srv32AST.\n', 1)
    return text, ex


if __name__ == '__main__':
    text, ex = run('Srv32TmplImm')
    Path(sys.argv[1]).write_text(text)
    print(sys.argv[1], len(text.splitlines()), len(ex))
