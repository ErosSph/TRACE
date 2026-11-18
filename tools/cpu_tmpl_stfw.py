#!/usr/bin/env python3
"""Fetch-wire layer (instruction word as a mux of the registered read data) from the manifest `route.fetchwire`:
  roots: [instruction word id, copy wire id, field wires..], conds: {flush, valid, hold1, hold2} wire ids with required values, mem: read-data signal id.
Every wire value comes from the checked assignment binding of its combinational process (ExtendedSVCheckedAssignmentBinding, one theorem
`w_<R>` per root); `fetch_wire` then evaluates the mux under the operating-state conditions.  Facts about the AST are checked by Coq (vm_compute).
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse, json
from pathlib import Path
import cpu_tmpl_ast as T
ROOT = Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('--design', default='steel'); ap.add_argument('--module', required=True); ap.add_argument('--out', required=True)
a = ap.parse_args()
man = json.loads((ROOT / f'framework/auto-contract-profiles/{a.design}.json').read_text())
fw = man['route']['fetchwire']
ast_m = man['pipeline_roles']['ast']
ast = T.Ast(ROOT / ast_m['file'], ROOT / ast_m['signal_table'])
mod, astmod = a.module, ast_m['module'].split('.')[0]
astname = ast_m['module'].split('.')[1] if '.' in ast_m['module'] else ast_m['module']
prog = ast_m['program'].split('.')[-1]
L = [f'(** Fetch wires of {a.design} (tools/cpu_tmpl_stfw.py, manifest route.fetchwire).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)',
     'From Coq Require Import ZArith List Bool Lia.',
     f'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection Lang.ExtendedSVCheckedAssignmentBinding {ast_m["module"]}.',
     f'Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVCheckedAssignmentBinding {astname}.', 'Local Open Scope Z_scope.',
     'Ltac cclose := repeat match goal with |- context [(norm ?w ?x =? 0)] => let v := eval vm_compute in (norm w x =? 0) in match v with true => change (norm w x =? 0) with true | false => change (norm w x =? 0) with false end end; cbv iota.', f'Module {mod}.', f'Notation P := {prog} (only parsing).']
ex = []
for r in fw['roots']:
    c = ast.comb[r]
    k, nm, w, e = c['k'], c['name'], c['width'], T.coq(c['rhs'])
    L += [f'Lemma at_{r} : nth_error (filter is_comb (processes P)) {k}%nat = Some {nm}. Proof. vm_compute; reflexivity. Qed.',
          f'Lemma body_{r} : process_body {nm} = SAssign false {e} (LVar {w} {r}%nat). Proof. vm_compute. reflexivity. Qed.',
          f'Lemma bind_{r} : assignment_bindingb (filter is_comb (processes P)) {k}%nat = true. Proof. vm_compute; reflexivity. Qed.',
          f'Theorem w_{r} seed d : CombLFP P seed d -> norm {w} (read_signal d {r}%nat) = norm {w} (eval_expr d {e}).',
          f'Proof. intro HL. exact (checked_assignment_binding P (filter is_comb (processes P)) {k}%nat {nm} false {e} {w}%nat {r}%nat seed d eq_refl at_{r} body_{r} bind_{r} ltac:(vm_compute; lia) HL). Qed.']
    ex.append(f'w_{r}')
iw, mem = fw['word'], fw['mem']
cs = fw['conds']      # list of [wire, width, value]
hyps = ' -> '.join(f'norm {w} (read_signal d {i}%nat) = {v}' for i, w, v in cs)
rws = ', '.join(f'h{n}' for n in range(len(cs)))
ints = ' '.join(f'h{n}' for n in range(len(cs)))
L += [f'Theorem fetch_wire seed d : CombLFP P seed d -> {hyps} -> norm 32 (read_signal d {iw}%nat) = norm 32 (read_signal d {mem}%nat).',
      f'Proof. intros HL {ints}. rewrite (w_{iw} seed d HL). cbn [eval_expr expr_width]. rewrite {rws}. rewrite (w_{fw["copy"]} seed d HL). cbn [eval_expr expr_width]. cclose. cbn [Z.eqb]. cbv iota. repeat rewrite norm_idempotent. reflexivity. Qed.']
ex.append('fetch_wire')
L += [f'End {mod}.'] + [f'Print Assumptions {mod}.{n}.' for n in ex]
Path(a.out).write_text('\n'.join(L) + '\n')
