#!/usr/bin/env python3
"""Forwarded zero-muxed read-port operand lemmas in register-relation shape (rebased bank), from manifest route.operands:
  {bank, ports:[{dst, rs}]}.  The port wire has the shape  ECond (0 == rs) 0 (ECond FWD X (bank[(rs-1)*32 +: 32]))  (checked by Coq);
  operand_<dst>: CombLFP, RFRelR bank view, FWD = 0  ->  norm 32 dst = view (norm 5 rs).  (The forwarded scenario FWD <> 0 is the X arm: Srv32Ex.)
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse, json
from pathlib import Path
import cpu_tmpl_ast as T
ROOT = Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('--design', default='srv32'); ap.add_argument('--module', required=True); ap.add_argument('--out', required=True)
a = ap.parse_args()
man = json.loads((ROOT / f'framework/auto-contract-profiles/{a.design}.json').read_text())
op = man['route']['operands']
am = man['pipeline_roles']['ast']
ast = T.Ast(ROOT / am['file'], ROOT / am['signal_table'])
astname = am['module'].split('.')[-1]; prog = am['program'].split('.')[-1]; bank = op['bank']
L = [f'(** {a.design}: forwarded read-port operands in register-relation shape (tools/cpu_tmpl_srv32_op.py).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)',
 'From Coq Require Import ZArith List Bool Lia.',
 f'Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVRootProjection Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVBankIndex Lang.ExtendedSVBankRead Lang.ExtendedSVBankOperand Lang.ExtendedSVBankRebase Lang.ExtendedSVCheckedAssignmentBinding {am["module"]}.',
 f'Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVRegisterBank ExtendedSVBankAlignment ExtendedSVBankIndex ExtendedSVBankRead ExtendedSVBankOperand ExtendedSVBankRebase ExtendedSVCheckedAssignmentBinding {astname}.',
 'Local Open Scope Z_scope.', f'Module {a.module}.', f'Notation P := {prog} (only parsing).',
 f'''Lemma port_gen s rs (F X : Expr) view : RFRelR (read_signal s {bank}%nat) view -> eval_expr s F = 0 ->
 norm 32 (eval_expr s (ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 rs)) (EConst 32 0) (ECond 32 F X (ESel 32 (EVar 1024%nat {bank}%nat) (rebased_index rs))))) = view (norm 5 (read_signal s rs)).
Proof.
 intros [HR H0] HF. rewrite eval_cond_unfold, eval_zero_guard.
 destruct (Z.eqb (norm 5 (read_signal s rs)) 0) eqn:E.
 - apply Z.eqb_eq in E. rewrite E. cbn. rewrite H0. reflexivity.
 - apply Z.eqb_neq in E.
   assert (Hz : Z.eqb 0 (norm 5 (read_signal s rs)) = false) by (apply Z.eqb_neq; lia).
   rewrite Hz. cbn [boolz]. change (norm 1 0 =? 0) with true. cbn iota.
   rewrite eval_cond_unfold, HF. cbn iota. change (0 =? 0) with true. cbn iota.
   rewrite (eval_packed_lane {bank}%nat 1024%nat (rebased_index rs) (le_n _) (rebased_bounded rs) s). repeat rewrite lane_read_norm.
   rewrite (rebase_eval s rs E).
   pose proof (norm_bounds 5 (read_signal s rs)) as HB5. change (0 <= norm 5 (read_signal s rs) < 32) in HB5.
   replace (32 * (norm 5 (read_signal s rs) - 1) / 32) with (norm 5 (read_signal s rs) - 1) by (rewrite Z.mul_comm; rewrite Z.div_mul; lia).
   rewrite HR by lia. f_equal. lia.
Qed.''']
ex = []
for p in op['ports']:
    d, rs = p['dst'], p['rs']; c = ast.comb[d]
    rhs = c['rhs']; assert rhs[0] == 'ECond' and rhs[4][0] == 'ECond', rhs[:1]
    F, X = T.coq(rhs[4][2]), T.coq(rhs[4][3])
    e = T.coq(rhs); k, nm = c['k'], c['name']
    L += [f'Lemma at_{d} : nth_error (filter is_comb (processes P)) {k}%nat = Some {nm}. Proof. vm_compute; reflexivity. Qed.',
          f'Lemma body_{d} : process_body {nm} = SAssign false {e} (LVar 32 {d}%nat). Proof. vm_compute. reflexivity. Qed.',
          f'Lemma bind_{d} : assignment_bindingb (filter is_comb (processes P)) {k}%nat = true. Proof. vm_compute; reflexivity. Qed.',
          f'Theorem operand_{d} seed d view : CombLFP P seed d -> RFRelR (read_signal d {bank}%nat) view -> eval_expr d {F} = 0 -> norm 32 (read_signal d {d}%nat) = view (norm 5 (read_signal d {rs}%nat)).',
          f'Proof. intros HL HR HF. rewrite (checked_assignment_binding P (filter is_comb (processes P)) {k}%nat {nm} false {e} 32%nat {d}%nat seed d eq_refl at_{d} body_{d} bind_{d} ltac:(vm_compute; lia) HL).',
          f' exact (port_gen d {rs}%nat {F} {X} view HR HF). Qed.']
    ex.append(f'operand_{d}')
L += [f'End {a.module}.'] + [f'Print Assumptions {a.module}.{n}.' for n in ex]
Path(a.out).write_text('\n'.join(L) + '\n')
