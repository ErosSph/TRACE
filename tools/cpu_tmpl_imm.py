#!/usr/bin/env python3
"""Dark immediate instantiation: for every immediate-carrying opcode of the class table, the decoded immediate register
(XSIMM, mined from the capture process) equals the riscv-coq decoder immediate of the slot word, using the design
independent shape lemmas of CPUImmediateShapes. The arm selection is by computation on the mined expression."""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_inv as inv
import cpu_isa_classes as isa

HDR = """From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Ex.External.CPUImmediateShapes @AST@ TmplDarkInv.DarkTmplInv.
Import ListNotations ExtendedSV ExtendedSVWordInvariant CPUImmediateShapes @ASTNS@.
Local Open Scope Z_scope.
Ltac norm_lits:=repeat match goal with
 |_:_|-context[norm ?w ?v]=>
  lazymatch v with context[read_signal _ _]=>fail|_=>idtac end;
  let r:=eval vm_compute in(norm w v)in change(norm w v)with r end.
"""
KIND = {'OPIMM': 'I', 'JALR': 'I', 'BRANCH': 'B', 'JAL': 'J', 'LUI': 'U', 'AUIPC': 'U'}


def text(design, module):
    ast, pr, tr = roles.load_all(design)
    fields, inword = inv.captured_fields(ast, pr)
    word = pr['fetch_slot']['word']['id']
    simm = pr['controller']['imm_signed']['id']
    # the register loaded into SIMM's source: XSIMM is the captured register feeding the SIMM wire
    xs = ast.comb[simm]['rhs']
    assert xs[0] == 'EVar', 'SIMM must be an alias of the captured register'
    reg = xs[2]
    g = [gx for R, w, gx in fields if R == reg][0]
    out = [f'Definition simm_expr : Expr := {T.coq(g)}.',
           f'Definition W : Expr := (EVar 32 {word}%nat).']
    seen = {}
    for c in isa.classes():
        k = KIND.get(c['group'])
        if k is None or c['group'] in seen:
            continue
        seen[c['group']] = k
        G = c['group']
        out += [f'Theorem simm_{G} s : norm 7 (norm 32 (read_signal s {word}%nat)) = {c["opcode"]} ->',
                f' eval_expr s simm_expr = eval_expr s (imm_{k} W).',
                f'Proof. intro Hop. unfold simm_expr, W. cbn [eval_expr]. change (norm 5 0) with 0. rewrite ?Z.shiftr_0_r.',
                ' rewrite Hop. norm_lits. cbn [Z.eqb Pos.eqb]. unfold imm_' + k + ', sign_fill, sel. cbn [eval_expr expr_width]. rewrite ?norm_idempotent. reflexivity. Qed.',
                f'Theorem isa_simm_{G} s : norm 7 (norm 32 (read_signal s {word}%nat)) = {c["opcode"]} ->',
                f' norm 32 (eval_expr s simm_expr) = norm 32 (isa_imm_{k} (norm 32 (read_signal s {word}%nat))).',
                f'Proof. intro Hop. rewrite (simm_{G} s Hop), (eval_imm_{k} s W). unfold W. cbn [eval_expr]. rewrite ?norm_idempotent. reflexivity. Qed.']
    exps = [f'isa_simm_{G}' for G in seen]
    return HDR.replace('@AST@', pr['ast']['module']).replace('@ASTNS@', pr['ast']['module'].split('.')[-1]) + f'Module {module}.\n' + '\n'.join(out) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {module}.{e}.\n' for e in exps), [f'{module}.{e}' for e in exps]


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='darkriscv')
    ap.add_argument('--module', default='DarkTmplImm')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    body, exports = text(a.design, a.module)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out)
        sys.exit(0)
    ast, pr, tr = roles.load_all(a.design)
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    lp = [(d['directory'], d['namespace']) for d in json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())['coq_load_paths']
          if d['namespace'] == 'Dark38']
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov, extra=dict(generator='tools/cpu_tmpl_imm.py', design=a.design))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
