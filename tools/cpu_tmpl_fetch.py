#!/usr/bin/env python3
"""Dark fetch-pipeline layer: PC-chain register steps (generated from the AST: IFPC, IDPC, PC in process_7),
wire equations for the bus/mux wires (generated), and the hand-written fetch core
(framework/template-sources/DarkTmplFetchCore.v.in): fetch_inv (IDATA = rom(IDPC)), HLT2 = 0, comb consistency of IADDR,
slot_inv (FLUSH in {0,1} -> slot word = rom(PC)), all preserved by actual_cycle (env2_step, slot_step)."""
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_params as PR
import cpu_tmpl_controls as ctl
import cpu_tmpl_cycle as cyc

HDR = cyc.HDR.replace('Dark38.DarkRISCV38DerivedAST TmplDarkInv.DarkTmplInv.',
                      'Dark38.DarkRISCV38DerivedAST TmplDarkInv.DarkTmplInv TmplDarkCycle.DarkTmplCycle Lang.ExtendedSVSeqStepIf.').replace(
    'ExtendedSVConstantRoot ExtendedSVSeqStep DarkRISCV38DerivedCycle', 'ExtendedSVConstantRoot ExtendedSVSeqStep ExtendedSVSeqStepIf DarkRISCV38DerivedCycle').replace(
    'DarkRISCV38DerivedTarget.DarkRISCV38DerivedTarget DarkRISCV38DerivedAST.',
    'DarkRISCV38DerivedTarget.DarkRISCV38DerivedTarget DarkRISCV38DerivedAST TmplDarkCycle.DarkTmplCycle.DarkTmplCycle.')


def pc_chain(design, regs):
    ast, pr, tr = roles.load_all(design)
    clk = pr['events']['clock']['id']
    pcp = int(pr['pc']['process'].split('_')[1])
    pnames = ast.names
    sts = roles.flat(ast.procs[pcp]['body'])
    out = []
    for R in regs:
        k = [i for i, s in enumerate(sts) if s[0] == 'SAssign' and s[3][0] == 'LVar' and s[3][2] == R][0]
        w = sts[k][3][1]
        rhs = sts[k][2]
        writers = [pnames[i] for i, p in enumerate(ast.procs) if any(
            s[0] == 'SAssign' and (s[3][2] if s[3][0] == 'LVar' else s[3][2][2]) == R for s in roles.flat(p['body']))]
        sel = ''
        for wname in writers:
            if wname == pnames[pcp]:
                sel += f' rewrite (matches_rise {wname} pre _ {clk}%nat eq_refl eq_refl H0 (rise_clk pre)); cbn [filter].'
            else:
                sel += f' assert (Hm{wname}: process_matches_states pre (phase_driven_state P rise pre) {wname} = false) by reflexivity; rewrite Hm{wname}; cbn [filter].'
        out += [
            f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma writers_p{R} : filter (writes_rootb {R}%nat) (processes P) = [{"; ".join(writers)}]. Proof. vm_compute; reflexivity. Qed.',
            f'Lemma rise_selp{R} pre : read_signal pre {clk}%nat = 0 ->',
            f' filter (process_matches_states pre (phase_driven_state P rise pre)) (filter (writes_rootb {R}%nat) (processes P)) = [{pnames[pcp]}].',
            f'Proof. intro H0. rewrite writers_p{R}. cbn [filter].{sel} reflexivity. Qed.',
            f'Lemma rise_c{R} pre : read_signal pre {clk}%nat = 0 ->',
            f' norm {w} (read_signal (PhaseSemantics P rise pre) {R}%nat) = norm {w} (eval_expr (phase_driven_state P rise pre) {T.coq(rhs)}).',
            f'Proof. intro H0. refine (seq_root_step P rise pre {R}%nat {pnames[pcp]} _ {k}%nat _ {w} comb_unw_{R} _ eq_refl _ _ (rise_selp{R} pre H0) eq_refl _ _).',
            ' all: try (vm_compute; reflexivity). all: cbn; try lia. Qed.']
    return '\n'.join(out) + '\n'


def text(design, module):
    g = ctl.Gen(design, module)
    for r in (4, 25, 28):
        g.wire_eq(r)
    core = PR.Params(design).core('TmplFetchCore.v.in')
    core = core.replace('@WIRES@', pc_chain(design, [24, 64, 65]) + '\n'.join(g.head))
    strip = lambda t: '\n'.join(l for l in t.split('\n') if not l.startswith('Print Assumptions'))
    body = HDR + f'Module {module}.\n' + strip(core) + f'End {module}.\n'
    exports = ['env2_reset', 'env2_step', 'slot_step']
    body += ''.join(f'Print Assumptions {module}.{e}.\n' for e in exports)
    return body, [f'{module}.{e}' for e in exports]


if __name__ == '__main__':
    import argparse
    import cpu_tmpl_accept as acc
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='darkriscv')
    ap.add_argument('--module', default='DarkTmplFetch')
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
                   extra=dict(generator='tools/cpu_tmpl_fetch.py', design=a.design, core='framework/template-sources/DarkTmplFetchCore.v.in (llm_written)',
                              reused_low_level_facts=['DarkRISCV38DerivedLFP.actual_driven_is_LFP', 'DarkRISCV38DerivedLFP.actual_original_phase (same AST sha 4b701bf8...)']))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
