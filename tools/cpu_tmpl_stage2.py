#!/usr/bin/env python3
"""Stage-register steps at the rising edge for sequential processes whose body is a decision tree with SEQUENCES of independent trees at its leaves
(angelo5fix processes 4, 8, 9, 10: `if (rst) { if (ce) {captures}; if (..) ce-chain; ...} else {resets}`); generalisation of cpu_tmpl_stage.py (additive) using
Lang/ExtendedSVSeqTree2 (conv2 / Rel2 / seq_tree2_value).  Per register R of a full-width register written by such a process:
  rise_<R>: (rise hypotheses of the edge layer) -> norm w (read (PhaseSemantics P ev pre) R) = norm w (eval driven (texpr2 w R tree(Q)))
Registers written through part selects are listed under skipped_part_select (handled elsewhere). Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json, sys, argparse
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import cpu_tmpl_roles as roles
import cpu_tmpl_ast as T
import cpu_tmpl_edge as E
import cpu_tmpl_stage as S


def only_bits(ast, i, R):
    ok, seen = True, False
    def go(n):
        nonlocal ok, seen
        if isinstance(n, (list, tuple)):
            if n and n[0] == 'SAssign':
                lv = n[3]
                root = lv
                while root[0] == 'LSel': root = root[2]
                if root[2] == R:
                    seen = True
                    if not (lv[0] == 'LSel' and lv[1] == 1 and lv[2][0] == 'LVar' and lv[3][0] == 'EConst'):
                        ok = False
            for c in n: go(c)
    go(ast.procs[i]['body'])
    return ok and seen


def build(design, module, edge_mod, procs_only=None, slice_mode=False):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    rise = E.expected(procs, clk0, rst0, 0, 1, E.RST_IDLE)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVSeqTree2 Lang.ExtendedSVSeqTree2Slice Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice ' + edge_mod.rsplit('.', 1)[0]).replace(
        '@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVSeqTree2 ExtendedSVSeqTree2Slice ExtendedSVRootProjection ExtendedSVProcessSlice')
    hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = 1 -> read_signal pre {clk0}%nat = 0 ->'
            f' read_signal pre {rst0}%nat = {E.RST_IDLE} -> {edge_mod}.NetWords pre -> CombLFP P seed pre ->'
            f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
    args = 'Hc Hv H0 H1 HW HL HD'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).',
         'Definition inner_of (q : Process) : Stmt := match process_body q with SSeq [SSeq [t]] => t | _ => SSkip end.',
         'Definition conv_of (q : Process) := conv2 64%nat (inner_of q).',
         'Definition need_of (q : Process) : nat := match conv_of q with Some (d, _) => d | None => 0%nat end.',
         'Definition tree_of (q : Process) : Tree2 := match conv_of q with Some (_, T) => T | None => T2Cat [] end.']
    names, skipped = [], []
    for i in rise:
        bd = ast.procs[i]['body']
        if procs_only and i not in procs_only:
            continue
        if not (bd[0] == 'SSeq' and len(bd[1]) == 1 and bd[1][0][0] == 'SSeq' and len(bd[1][0][1]) == 1):
            skipped.append((i, ['body_shape'])); continue
        regs = S.full_width_regs(ast, i, None)
        S1 = {R: only_bits(ast, i, R) for R, w in regs.items() if w is None}
        if any(w is None for w in regs.values()):
            skipped.append((i, [r for r, w in regs.items() if w is None]))
        L += [f'Lemma body_{i} : process_body process_{i} = SSeq [SSeq [inner_of process_{i}]]. Proof. reflexivity. Qed.',
              f'Lemma conv_{i} : conv2 64%nat (inner_of process_{i}) = Some (need_of process_{i}, tree_of process_{i}).',
              f'Proof. unfold need_of, tree_of, conv_of. destruct (conv2 64%nat (inner_of process_{i})) as [[d T]|] eqn:E; [reflexivity|]. vm_compute in E. discriminate. Qed.',
              f'Lemma rel_{i} : Rel2 (need_of process_{i}) (inner_of process_{i}) (tree_of process_{i}). Proof. exact (conv2_sound _ _ _ _ conv_{i}). Qed.',
              f'Lemma depth_{i} : (need_of process_{i} + 2 <= statement_fuel P)%nat. Proof. vm_compute; lia. Qed.']
        for R, w in sorted(regs.items()):
            if slice_mode and w is not None:
                continue
            if w is None:
                if not slice_mode:
                    continue
                L += [f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.',
                      f'Lemma writers_{R} : filter (writes_rootb {R}%nat) (processes P) = [process_{i}]. Proof. vm_compute; reflexivity. Qed.',
                      f'Theorem rises_{R} ev pre seed :{hyps}',
                      f' read_signal(PhaseSemantics P ev pre){R}%nat = lastws(phase_driven_state P ev pre){R}%nat(tleaf2(phase_driven_state P ev pre)(tree_of process_{i}))(read_signal(phase_driven_state P ev pre){R}%nat).',
                      f'Proof. intros {args}.',
                      f' refine(seq_tree2s_value P ev pre {R}%nat process_{i} (inner_of process_{i}) (tree_of process_{i}) (need_of process_{i}) comb_unw_{R}'
                      f' (fun H => let Hn : {clk0}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) body_{i} rel_{i} depth_{i} _).',
                      f' rewrite writers_{R}. cbn[filter]. rewrite({edge_mod}.sel_rise_match_{i} ev pre seed {args}). reflexivity. Qed.']
                names.append(f'rises_{R}')
                if S1.get(R):
                    L += [f'Lemma s1_{R} : forall s, slice1_all {R}%nat (tleaf2 s (tree_of process_{i})).',
                          f'Proof. intro s. refine(slice1_tree2 {R}%nat _ _ s). vm_compute. reflexivity. Qed.',
                          f'Theorem bit_{R} ev pre seed j :{hyps}',
                          f' 0 <= j -> Z.testbit (read_signal(PhaseSemantics P ev pre){R}%nat) j = lastbit(phase_driven_state P ev pre){R}%nat j(tleaf2(phase_driven_state P ev pre)(tree_of process_{i}))(Z.testbit(read_signal(phase_driven_state P ev pre){R}%nat) j).',
                          f'Proof. intros {args} Hj. rewrite(rises_{R} ev pre seed {args}). exact(lastbit_correct _ _ j _ _ Hj (s1_{R} _)). Qed.']
                    names.append(f'bit_{R}')
                continue
            L += [f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.',
                  f'Lemma writers_{R} : filter (writes_rootb {R}%nat) (processes P) = [process_{i}]. Proof. vm_compute; reflexivity. Qed.',
                  f'Lemma wf_{R} : twf2m {w}%nat {R}%nat (tree_of process_{i}) = true. Proof. vm_compute; reflexivity. Qed.',
                  f'Theorem rise_{R} ev pre seed :{hyps}',
                  f' norm {w}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {w}(eval_expr(phase_driven_state P ev pre)(texpr2m {w}%nat {R}%nat (tree_of process_{i}))).',
                  f'Proof. intros {args}.',
                  f' refine(seq_tree2m_value P ev pre {R}%nat process_{i} (inner_of process_{i}) (tree_of process_{i}) (need_of process_{i}) {w}%nat comb_unw_{R}'
                  f' (fun H => let Hn : {clk0}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) body_{i} rel_{i} depth_{i} _ wf_{R}).',
                  f' rewrite writers_{R}. cbn[filter]. rewrite({edge_mod}.sel_rise_match_{i} ev pre seed {args}). reflexivity. Qed.']
            names.append(f'rise_{R}')
    body = (f'(** {design}: stage-register steps at the primary rising edge, two-level trees (tools/cpu_tmpl_stage2.py).\n'
            f'    proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + hdr +
            f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, [f'{module}.{n}' for n in names], dict(registers=len(names), skipped=skipped)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='angelo5fix'); ap.add_argument('--module', default='A5TmplStage2'); ap.add_argument('--namespace', default='TmplA5Stage2')
    ap.add_argument('--edge', default='TmplA5Edge.A5TmplEdge.A5TmplEdge'); ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[]); ap.add_argument('--accept', action='store_true')
    ap.add_argument('--procs', default=''); ap.add_argument('--slices', action='store_true')
    a = ap.parse_args()
    po = {int(x) for x in a.procs.split(',') if x} or None
    body, exports, info = build(a.design, a.module, a.edge, po, a.slices)
    if not a.accept:
        Path(a.out).write_text(body); print(a.out, info); sys.exit(0)
    import cpu_tmpl_accept as acc
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov, timeout=7200, extra=dict(generator='tools/cpu_tmpl_stage2.py', design=a.design, info=info))
    print(json.dumps(r, indent=1)[:1500]); sys.exit(0 if r['accepted'] else 1)
