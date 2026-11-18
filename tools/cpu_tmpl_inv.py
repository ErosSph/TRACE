#!/usr/bin/env python3
"""Milestone 2 generator: R/INV from role-parameterised templates.

Templates (all design independent, instantiated from the AST + roles):
  CoherentFields  "synchronized fields": every register R that the capture process loads with
                  `stall ? R : g(input_word)` equals g evaluated on the held slot word.
  Inv             arch part (the pinned target's arch relation: committed RF, PC cursor, ROM, RAM)
                  /\\ CoherentFields at the RTL state.
  inv_init        Inv holds at the real reset state (arch part from the target's own initial theorem,
                  CoherentFields by computation on the actual reset state).
  inv_prem_<C>    (a)->(b) bridge: CoherentFields + commit-cycle base + the ISA decode fields of the slot
                  word give the controller premise prem_<C> of the milestone-1 facts.
Untrusted generator; Coq checks everything.
"""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_isa_classes as isa
import cpu_tmpl_controls as ctl


def subst(e, old, new):
    if e[0] == 'EVar':
        return ('EVar', e[1], new) if e[2] == old else e
    if e[0] == 'EConst':
        return e
    return tuple(subst(c, old, new) if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E') else c
                 for c in e)


def captured_fields(ast, pr):
    """[(reg, width, g_on_slot_word)] for registers loaded as `stall ? R : g(input)` in the capture process."""
    stall = pr['fetch_slot']['stall']['id']
    cap = int(pr['fetch_slot']['capture_process'].split('_')[1])
    word = pr['fetch_slot']['word']['id']
    out, inword = [], None
    for s in roles.flat(ast.procs[cap]['body']):
        if s[0] != 'SAssign' or s[3][0] != 'LVar':
            continue
        R, w = s[3][2], s[3][1]
        r = s[2]
        if r[0] == 'ECond' and r[2] == ('EVar', 1, stall) and r[3] == ('EVar', w, R):
            out.append((R, w, r[4]))
    # the input word is the variable of the slot-word register's own g
    g = [x for x in out if x[0] == word][0][2]
    assert g[0] == 'EVar', 'slot word must be a plain copy of the input'
    inword = g[2]
    return [(R, w, subst(g_, inword, word)) for R, w, g_ in out], inword


def build(design, module):
    g = ctl.Gen(design, module)
    ast, pr, tr = g.ast, g.pr, g.tr
    tb = tr['target_binding']
    fields, inword = captured_fields(ast, pr)
    word = pr['fetch_slot']['word']['id']
    c = pr['controller']
    f3, f7 = c['funct3']['id'], c['funct7']['id']
    for r in (f3, f7):
        g.wire_eq(r)
    B = tb['binders']
    AND = ' /\\ '
    lines = []
    clauses = [f'norm {w}(read_signal f {R}%nat)=norm {w}(eval_expr f {T.coq(gx)})' for R, w, gx in fields]
    lines.append('Definition CoherentFields(f:State):Prop:=' + AND.join(clauses) + '.')
    lines.append(f'Definition Inv {B} s isa:Prop:={tb["arch_relation"]} s isa' + AND + f'CoherentFields({tb["runtime_rtl"]} s).')
    lines.append(f'Theorem inv_init {B}:Inv {B} {tb["reset_state"]}({tb["isa_initial"]}).')
    lines.append(f'Proof. split;[exact(target_initial_architecture {B})|].')
    lines.append(f' unfold CoherentFields;unfold {tb["reset_state"]};cbn[{tb["runtime_rtl"]}];repeat split;vm_compute;reflexivity. Qed.')
    flagmap = {f['reg']['id']: f['opcode'] for f in tr['class_flags']['flags']}
    ids = [R for R, _, _ in fields]
    cpat = f'C{ids[-1]}'
    for R in reversed(ids[:-1]):
        cpat = f'[C{R} {cpat}]'
    def alt(x):
        if x == g.id['xres']:
            return 'exact Hx'
        if x == g.id['halt']:
            return 'exact Hh'
        if x == g.id['flush']:
            return 'exact Hf'
        if x in flagmap:
            return f'rewrite C{x}. DBG cbn[eval_expr]. DBG norm_lits. DBG rewrite ?Z.shiftr_0_r. DBG rewrite Hop. DBG vm_compute. DBG reflexivity'
        if x == f3:
            return f'rewrite(eq_w{x} seed fixed HL). DBG unfold orig_w{x}. DBG cbn[eval_expr]. DBG change(norm 5 {g.ast.comb[x]["rhs"][3][2]})with {g.ast.comb[x]["rhs"][3][2]}. DBG rewrite H3. DBG reflexivity'
        if x == f7:
            return f'rewrite(eq_w{x} seed fixed HL). DBG unfold orig_w{x}. DBG cbn[eval_expr]. DBG change(norm 5 {g.ast.comb[x]["rhs"][3][2]})with {g.ast.comb[x]["rhs"][3][2]}. DBG rewrite H7. DBG reflexivity'
        raise ValueError(x)
    exports = []
    for cl in isa.classes():
        name = cl['name']
        hyps = [f'norm 7(norm 32(read_signal fixed {word}%nat))={cl["opcode"]}']
        hn = ['Hop']
        if cl['funct3'] is not None:
            hyps.append(f'norm 3(Z.shiftr(norm 32(read_signal fixed {word}%nat))12)={cl["funct3"]}')
            hn.append('H3')
        if cl['funct7'] is not None:
            hyps.append(f'norm 7(Z.shiftr(norm 32(read_signal fixed {word}%nat))25)={cl["funct7"]}')
            hn.append('H7')
        base = (f'norm 1(read_signal fixed {g.id["xres"]}%nat)=0' + AND + f'norm 1(read_signal fixed {g.id["halt"]}%nat)=0'
                + AND + f'norm 2(read_signal fixed {g.id["flush"]}%nat)=0')
        lines.append(f'Theorem inv_prem_{name} seed fixed:CombLFP P seed fixed->({base})->CoherentFields fixed->'
                     + '->'.join(hyps) + f'->TmplDarkControls.DarkTmplControls.DarkTmplControls.prem_{name} fixed.')
        lines.append(f'Proof. intros HL[Hx[Hh Hf]]HC {" ".join(hn)}. destruct HC as {cpat}.')
        prem = g.premises(cl)
        steps = []
        for k, (w, x, v) in enumerate(prem):
            steps.append(alt(x) + '.' if k == len(prem) - 1 else 'split. { ' + alt(x) + '. }')
        lines.append(f' unfold TmplDarkControls.DarkTmplControls.DarkTmplControls.prem_{name}. ' + ' '.join(steps).replace('DBG ', DBG) + ' Qed.')
        exports.append(f'inv_prem_{name}')
    exports = ['inv_init'] + exports
    return g, lines, exports


DBG = ''
PRE = r"""From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVBankAlignment Lang.ExtendedSVStallFlush @AST@ @IMPORTS@ TmplDarkControls.DarkTmplControls.
Import ListNotations ExtendedSV ExtendedSVCheckedAssignmentBinding ExtendedSVWordInvariant @ASTNS@ @OPENS@.
Local Open Scope Z_scope.
"""


def text(design, module):
    g, lines, exports = build(design, module)
    tb = g.tr['target_binding']
    pre = (PRE.replace('@AST@', g.ast_module).replace('@ASTNS@', g.ast_module.split('.')[-1])
           .replace('@IMPORTS@', ' '.join(tb['imports'])).replace('@OPENS@', ' '.join(tb['open_modules'])))
    hdr = (f'(** {design}: R/INV templates (coherent fields, Inv, initialization at the real reset, a->b bridge). Generated by\n'
           f'    tools/cpu_tmpl_inv.py. proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. Do not edit. *)\n')
    body = hdr + pre + f'Module {module}.\n' + '\n'.join(g.head) + '\n' + '\n'.join(lines) + f'\nEnd {module}.\n'
    body += ''.join(f'Print Assumptions {module}.{e}.\n' for e in exports)
    return body, [f'{module}.{e}' for e in exports], g


def run_accept(design, module, namespace, out, providers):
    import cpu_tmpl_accept as acc
    body, exports, g = text(design, module)
    tb = g.tr['target_binding']
    lp = [(d['directory'], d['namespace']) for d in json.loads(Path(f'framework/auto-contract-profiles/{design}.json').read_text())['coq_load_paths']
          if d['namespace'] == 'Dark38'] + [tuple(x) for x in tb['extra_loadpaths']]
    return acc.accept(out, namespace, module, body, exports, lp, providers=providers,
                      extra=dict(generator='tools/cpu_tmpl_inv.py', design=design, ast_sha256=acc.sha(g.ast.file)))


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='darkriscv')
    ap.add_argument('--module', default='DarkTmplInv')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[], help='NAMESPACE=results/dir')
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    if a.accept:
        r = run_accept(a.design, a.module, a.namespace, a.out, prov)
        print(json.dumps(r, indent=1))
        sys.exit(0 if r['accepted'] else 1)
    body, exports, g = text(a.design, a.module)
    Path(a.out).write_text(body)
    print(a.out, len(body.splitlines()))
