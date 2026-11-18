#!/usr/bin/env python3
"""Stage-register steps at the rising edge for sequential processes whose body is [SSeq [SSeq l]] with SEVERAL items in l
(no reset test: angelo5fix wrapper memory read port process 0, wrapper memory write process 1, register file process 2).
Additive companion of tools/cpu_tmpl_stage2.py using Lang/ExtendedSVSeqTree2One (the converted statement is the inner sequence).
Per register R written by such a process:
  full-width R:      rise_<R>:  (rise hypotheses) -> norm w (read (PhaseSemantics P ev pre) R) = norm w (eval driven (texpr2m w R tree(Q)))
  part-select R:     rises_<R>: (rise hypotheses) -> read (PhaseSemantics P ev pre) R = lastws driven R (tleaf2 driven tree(Q)) (read driven R)
Untrusted generator; Coq checks everything.  proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0."""
import json, sys, argparse
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import cpu_tmpl_roles as roles
import cpu_tmpl_ast as T
import cpu_tmpl_edge as E
import cpu_tmpl_stage as S

AUTHOR = 'LLM-generated: Claude Code (claude-opus-5-5)'


def build(design, module, edge_mod, procs_only):
    ast, pr, tr = roles.load_all(design)
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    rise = E.expected(procs, clk0, rst0, 0, 1, E.RST_IDLE)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    hdr = E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVSeqTree2 Lang.ExtendedSVSeqTree2Slice Lang.ExtendedSVSeqTree2One Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice ' + edge_mod.rsplit('.', 1)[0]).replace(
        '@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVSeqTree2 ExtendedSVSeqTree2Slice ExtendedSVSeqTree2One ExtendedSVRootProjection ExtendedSVProcessSlice')
    hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = 1 -> read_signal pre {clk0}%nat = 0 ->'
            f' read_signal pre {rst0}%nat = {E.RST_IDLE} -> {edge_mod}.NetWords pre -> CombLFP P seed pre ->'
            f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
    args = 'Hc Hv H0 H1 HW HL HD'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).',
         'Definition inner1_of (q : Process) : Stmt := match process_body q with SSeq [t] => t | _ => SSkip end.',
         'Definition conv1_of (q : Process) := conv2 64%nat (inner1_of q).',
         'Definition need1_of (q : Process) : nat := match conv1_of q with Some (d, _) => d | None => 0%nat end.',
         'Definition tree1_of (q : Process) : Tree2 := match conv1_of q with Some (_, T) => T | None => T2Cat [] end.']
    names, skipped = [], []
    for i in rise:
        if i not in procs_only:
            continue
        bd = ast.procs[i]['body']
        if not (bd[0] == 'SSeq' and len(bd[1]) == 1 and bd[1][0][0] == 'SSeq'):
            skipped.append((i, ['body_shape'])); continue
        regs = S.full_width_regs(ast, i, None)
        L += [f'Lemma body1_{i} : process_body process_{i} = SSeq [inner1_of process_{i}]. Proof. reflexivity. Qed.',
              f'Lemma conv1_{i} : conv2 64%nat (inner1_of process_{i}) = Some (need1_of process_{i}, tree1_of process_{i}).',
              f'Proof. unfold need1_of, tree1_of, conv1_of. destruct (conv2 64%nat (inner1_of process_{i})) as [[d T]|] eqn:E; [reflexivity|]. vm_compute in E. discriminate. Qed.',
              f'Lemma rel1_{i} : Rel2 (need1_of process_{i}) (inner1_of process_{i}) (tree1_of process_{i}). Proof. exact (conv2_sound _ _ _ _ conv1_{i}). Qed.',
              f'Lemma depth1_{i} : (need1_of process_{i} + 1 <= statement_fuel P)%nat. Proof. vm_compute; lia. Qed.']
        for R, w in sorted(regs.items()):
            L += [f'Lemma comb_unw_{R} : comb_root_unwrittenb P {R}%nat = true. Proof. vm_compute; reflexivity. Qed.',
                  f'Lemma writers_{R} : filter (writes_rootb {R}%nat) (processes P) = [process_{i}]. Proof. vm_compute; reflexivity. Qed.']
            tail = (f' (fun H => let Hn : {clk0}%nat = {R}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) body1_{i} rel1_{i} depth1_{i} _')
            sel = f' rewrite writers_{R}. cbn[filter]. rewrite({edge_mod}.sel_rise_match_{i} ev pre seed {args}). reflexivity. Qed.'
            if w is None:
                L += [f'Theorem rises_{R} ev pre seed :{hyps}',
                      f' read_signal(PhaseSemantics P ev pre){R}%nat = lastws(phase_driven_state P ev pre){R}%nat(tleaf2(phase_driven_state P ev pre)(tree1_of process_{i}))(read_signal(phase_driven_state P ev pre){R}%nat).',
                      f'Proof. intros {args}.',
                      f' refine(seq_tree2s_value_one P ev pre {R}%nat process_{i} (inner1_of process_{i}) (tree1_of process_{i}) (need1_of process_{i}) comb_unw_{R}' + tail + ').', sel]
                names.append(f'rises_{R}')
            else:
                L += [f'Lemma wf_{R} : twf2m {w}%nat {R}%nat (tree1_of process_{i}) = true. Proof. vm_compute; reflexivity. Qed.',
                      f'Theorem rise_{R} ev pre seed :{hyps}',
                      f' norm {w}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {w}(eval_expr(phase_driven_state P ev pre)(texpr2m {w}%nat {R}%nat (tree1_of process_{i}))).',
                      f'Proof. intros {args}.',
                      f' refine(seq_tree2m_value_one P ev pre {R}%nat process_{i} (inner1_of process_{i}) (tree1_of process_{i}) (need1_of process_{i}) {w}%nat comb_unw_{R}' + tail + f' wf_{R}).', sel]
                names.append(f'rise_{R}')
    body = (f'(** {design}: stage-register steps at the primary rising edge for [SSeq [SSeq l]] process bodies (tools/cpu_tmpl_stage2one.py).\n'
            f'    proof_author: {AUTHOR}; external_llm_api_calls=0. *)\n' + hdr +
            f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n')
    body += ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, [f'{module}.{n}' for n in names], dict(registers=len(names), skipped=skipped)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='angelo5fix'); ap.add_argument('--module', default='A5TmplStage2One'); ap.add_argument('--namespace', default='TmplA5Stage2One')
    ap.add_argument('--edge', default='TmplA5Edge.A5TmplEdge.A5TmplEdge'); ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[]); ap.add_argument('--accept', action='store_true')
    ap.add_argument('--procs', default='0,1,2')
    a = ap.parse_args()
    po = {int(x) for x in a.procs.split(',') if x}
    body, exports, info = build(a.design, a.module, a.edge, po)
    if not a.accept:
        Path(a.out).write_text(body); print(a.out, info); sys.exit(0)
    import cpu_tmpl_accept as acc
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov, timeout=7200,
                   extra=dict(generator='tools/cpu_tmpl_stage2one.py', design=a.design, info=info, proof_author=AUTHOR))
    print(json.dumps({k: v for k, v in r.items() if k != 'loadpaths'}, indent=1)[:1500]); sys.exit(0 if r.get('coqc_accepted') or r.get('accepted') else 1)
