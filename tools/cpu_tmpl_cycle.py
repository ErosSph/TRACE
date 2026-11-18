#!/usr/bin/env python3
"""Milestone 3 cycle layer for an N=0 design: register steps at the clock edge, reset handling, environment
invariant, observer and rank facts; plus (generated from the AST) the capture-register steps and the
preservation of the template coherent fields.

The design-specific core (clock-cycle shape, reset sequencing, XRES/FLUSH facts, observer, rank) is the hand-written
source framework/template-sources/DarkTmplCycleCore.v.in (provenance llm_written); the capture-register part is generated.
"""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_params as PR
import cpu_tmpl_controls as ctl
import cpu_tmpl_inv as inv

HDR = r"""From Coq Require Import ZArith List Bool Lia.
Require Import Ex.External.CV32E40PTwoCommitITreeInterface Lang.ExtendedSVBankAlignment Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVStallFlush Lang.ExtendedSV Lang.ExtendedSVRootProjection
 Lang.ExtendedSVProcessSlice Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVConstantRoot Lang.ExtendedSVSeqStep
 Ex.External.DarkRISCV38DerivedCycle Ex.External.DarkRISCV38DerivedTarget Ex.External.DarkRISCV38DerivedLFP
 Dark38.DarkRISCV38DerivedAST TmplDarkInv.DarkTmplInv.
Import ListNotations CV32E40PTwoCommitITreeInterface ExtendedSVWordInvariant ExtendedSVCheckedAssignmentBinding
 ExtendedSVStallFlush ExtendedSV ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVEmptyPipeline
 ExtendedSVConstantRoot ExtendedSVSeqStep DarkRISCV38DerivedCycle DarkRISCV38DerivedLFP
 DarkRISCV38DerivedTarget.DarkRISCV38DerivedTarget DarkRISCV38DerivedAST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
"""


def capture_part(design):
    ast, pr, tr = roles.load_all(design)
    cap = int(pr['fetch_slot']['capture_process'].split('_')[1])
    stall = pr['fetch_slot']['stall']['id']
    word = pr['fetch_slot']['word']['id']
    clk = pr['events']['clock']['id']
    fields, inword = inv.captured_fields(ast, pr)
    sts = roles.flat(ast.procs[cap]['body'])
    out = ['Local Opaque actual_cycle clock_cycle.']
    pnames = ast.names
    for R, w, gprime in fields:
        k = [i for i, s in enumerate(sts) if s[0] == 'SAssign' and s[3][0] == 'LVar' and s[3][2] == R][0]
        rhs = sts[k][2]
        writers = [pnames[i] for i, p in enumerate(ast.procs) if any(
            s[0] == 'SAssign' and (s[3][2] if s[3][0] == 'LVar' else s[3][2][2]) == R for s in roles.flat(p['body']))]
        sel = ''
        for wname in writers:
            if wname == pnames[cap]:
                sel += f' rewrite (matches_rise {wname} pre _ {clk}%nat eq_refl eq_refl H0 (rise_clk pre)); cbn [filter].'
            else:
                sel += f' assert (Hm{wname}: process_matches_states pre (phase_driven_state P rise pre) {wname} = false) by reflexivity; rewrite Hm{wname}; cbn [filter].'
        out += [
            f'Lemma comb_unw_c{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma writers_c{R} : filter (writes_rootb {R}%nat) (processes P) = [{"; ".join(writers)}]. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma rise_selc{R} pre : read_signal pre {clk}%nat = 0 ->',
            f' filter (process_matches_states pre (phase_driven_state P rise pre)) (filter (writes_rootb {R}%nat) (processes P)) = [{pnames[cap]}].',
            f'Proof. intro H0. rewrite writers_c{R}. cbn [filter].{sel} reflexivity. Qed.',
            f'Lemma rise_c{R} pre : read_signal pre {clk}%nat = 0 ->',
            f' norm {w} (read_signal (PhaseSemantics P rise pre) {R}%nat) = norm {w} (eval_expr (phase_driven_state P rise pre) {T.coq(rhs)}).',
            f'Proof. intro H0. refine (seq_root_step P rise pre {R}%nat {pnames[cap]} _ {k}%nat _ {w} comb_unw_c{R} _ eq_refl _ _ (rise_selc{R} pre H0) eq_refl _ _).',
            ' all: try (vm_compute; reflexivity). all: cbn; try lia. Qed.',
            f'Lemma cyc_c{R} image s : env_ok s -> norm {w} (read_signal (rtl (actual_cycle image s)) {R}%nat) =',
            f' norm {w} (eval_expr (phase_driven_state P rise (rtl s)) {T.coq(rhs)}).',
            f'Proof. intros [H0 _]. rewrite (act_reg image s {R}%nat comb_unw_c{R} ltac:(discriminate)).',
            f' rewrite (frame3 image s {R}%nat comb_unw_c{R} ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)). apply rise_c{R}. exact H0. Qed.']
    # word register: next value is the held-or-new input word; with HLT=0 it is the input word
    inw = inword
    out += [
        f'Lemma next_word image s : env_ok s -> norm 32 (read_signal (rtl (actual_cycle image s)) {word}%nat) =',
        f' norm 32 (read_signal (phase_driven_state P rise (rtl s)) {inw}%nat).',
        f'Proof. intro HE. rewrite (cyc_c{word} image s HE). cbn [eval_expr]. rewrite (driven_halt s HE). cbn.',
        ' rewrite ?norm_idempotent. reflexivity. Qed.']
    names = []
    for R, w, gp in fields:
        k = [i for i, s in enumerate(sts) if s[0] == 'SAssign' and s[3][0] == 'LVar' and s[3][2] == R][0]
        g = sts[k][2][4]   # (ECond w stall hold g)
        out += [
            f'Lemma coh_aux_c{R} (n d : State) : norm 32 (read_signal n {word}%nat) = norm 32 (read_signal d {inw}%nat) ->',
            f' norm 1 (read_signal d {stall}%nat) = 0 -> norm {w} (read_signal n {R}%nat) = norm {w} (eval_expr d {T.coq(sts[k][2])}) ->',
            f' norm {w} (read_signal n {R}%nat) = norm {w} (eval_expr n {T.coq(gp)}).',
            'Proof. intros Hw Hh Hr. rewrite Hr. cbn [eval_expr]. rewrite Hh, Hw. cbn. rewrite ?norm_idempotent. reflexivity. Qed.',
            f'Lemma coh_c{R} image s : env_ok s -> norm {w} (read_signal (rtl (actual_cycle image s)) {R}%nat) =',
            f' norm {w} (eval_expr (rtl (actual_cycle image s)) {T.coq(gp)}).',
            f'Proof. intro HE. exact (coh_aux_c{R} _ _ (next_word image s HE) (driven_halt s HE) (cyc_c{R} image s HE)). Qed.']
        names.append(R)
    ids = names
    conj = f'(coh_c{ids[-1]} image s HE)'
    for R in reversed(ids[:-1]):
        conj = f'(conj (coh_c{R} image s HE) {conj})'
    out += [
        'Theorem coherent_step image s : env_ok s -> TmplDarkInv.DarkTmplInv.DarkTmplInv.CoherentFields (rtl (actual_cycle image s)).',
        f'Proof. intro HE. unfold TmplDarkInv.DarkTmplInv.DarkTmplInv.CoherentFields. exact {conj}. Qed.',
        'Print Assumptions coherent_step.']
    return '\n'.join(out) + '\n', ast


def text(design, module):
    core = PR.Params(design).core('TmplCycleCore.v.in')
    cap, ast = capture_part(design)
    # the core ends with Print Assumptions lines; keep them
    strip = lambda t: '\n'.join(l for l in t.split('\n') if not l.startswith('Print Assumptions'))
    body = HDR + f'Module {module}.\n' + strip(core) + '\n' + strip(cap) + f'End {module}.\n'
    exports = ['env_ok_reset', 'env_step', 'observe_eq', 'rank_dec', 'coherent_step']
    body += ''.join(f'Print Assumptions {module}.{e}.\n' for e in exports)
    return body, [f'{module}.{e}' for e in exports]


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='darkriscv')
    ap.add_argument('--module', default='DarkTmplCycle')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    body, exports = text(a.design, a.module)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out, len(body.splitlines()))
        sys.exit(0)
    ast, pr, tr = roles.load_all(a.design)
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    lp = [(d['directory'], d['namespace']) for d in json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())['coq_load_paths']
          if d['namespace'] == 'Dark38'] + [tuple(x) for x in tr['target_binding']['extra_loadpaths']]
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov,
                   extra=dict(generator='tools/cpu_tmpl_cycle.py', design=a.design, core='framework/template-sources/DarkTmplCycleCore.v.in (llm_written)',
                              reused_low_level_facts=['DarkRISCV38DerivedLFP.actual_driven_is_LFP (same AST, sha 4b701bf8...)']))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
