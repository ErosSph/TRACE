#!/usr/bin/env python3
"""Tag/valid transport of the Bzeeno pipeline at the rising edge (input of `shape_post`): next values of the four valid bits
(IF/ID 141, ID/EX 250, EX/MEM 286, MEM/WB 308) in terms of the previous valids and the controller outputs o_not_stall (156) and
o_flush (157) at the driven state.  Built on the stage layer (rise_<R>: decision-tree expression of the register), the edge layer
(reset nets) and the ctl scenarios (which give f and n per class).  Explicit tree expressions are produced here in Python from the AST
(texpr mirror); Coq checks `texpr = <expr>` by computation, so a wrong mirror is rejected.
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E


def texpr(st, R, w):
    if st[0] == 'SIf':
        return ('ECond', w, st[1], texpr(st[2], R, w), texpr(st[3], R, w))
    if st[0] == 'SSeq':
        if len(st[1]) == 1 and st[1][0][0] in ('SIf', 'SSeq'):
            return texpr(st[1][0], R, w)
        for s in st[1]:
            if s[0] == 'SAssign' and s[3][0] == 'LVar' and s[3][2] == R:
                return s[2]
        return ('EVar', w, R)
    if st[0] == 'SAssign':
        return st[2] if st[3][2] == R else ('EVar', w, R)
    return ('EVar', w, R)


def build(design, module, edge, stage):
    ast, pr, tr = roles.load_all(design)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    clk0, rst0, net, chain, procs = E.nets(ast, pr)
    vstages = [(s['valid']['id'], int(s['process'].split('_')[1])) for s in pr['stages']]
    ctl = pr['controller']
    nstall, flush = ctl['enable']['id'], ctl['flush']['id']
    hyps = (f' changed_signal ev = {clk0}%nat -> new_value ev = 1 -> read_signal pre {clk0}%nat = 0 ->'
            f' read_signal pre {rst0}%nat = 1 -> {edge}.NetWords pre -> CombLFP P seed pre ->'
            f' CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre) ->')
    args = 'Hc Hv H0 H1 HW HL HD'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).']
    done = set()

    def wire(s):
        if s in done:
            return
        done.add(s)
        cc = ast.comb[s]
        W = cc['width']
        L.extend([f'Definition orig_w{s}:Expr:={T.coq(cc["rhs"])}.',
                  f'Theorem eq_w{s} seed fixed:CombLFP P seed fixed->norm {W}(read_signal fixed {s}%nat)=norm {W}(eval_expr fixed orig_w{s}).',
                  f'Proof. intro HL. refine(checked_assignment_binding P _ {cc["k"]}%nat {cc["name"]} false orig_w{s} {W}%nat {s}%nat seed fixed eq_refl _ _ _ _ HL).',
                  ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.'])
    # cone wires of the valid trees: guards and leaf values, followed through comb copy / AND wires down to registers or ctl outputs
    sources = {v for v, _ in vstages} | {nstall, flush, rst0, clk0}
    cone = []

    def follow(i):
        if i in sources or i in cone or i not in ast.comb:
            return
        r = ast.comb[i]['rhs']
        for _, v in sorted(T.evars(r)):
            follow(v)
        cone.append(i)
    exprs = {}
    for R, i in vstages:
        ex = texpr(ast.procs[i]['body'], R, 1)
        exprs[R] = ex
        for _, v in sorted(T.evars(ex)):
            follow(v)
    for w in cone:
        wire(w)
    # norm-level wire lemmas
    for w in cone:
        r = ast.comb[w]['rhs']
        if r[0] == 'EVar':
            L += [f'Theorem n_{w} seed d : CombLFP P seed d -> norm 1(read_signal d {w}%nat)=norm 1(read_signal d {r[2]}%nat).',
                  f'Proof. intro HL. rewrite(eq_w{w} seed d HL). unfold orig_w{w}. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.']
        elif r[0] == 'EBinary' and r[2] == 'BAnd' and r[3][0] == 'EVar' and r[4][0] == 'EVar':
            a, b = r[3][2], r[4][2]
            L += [f'Theorem n_{w} seed d : CombLFP P seed d -> norm 1(read_signal d {w}%nat)=norm 1(Z.land(norm 1(read_signal d {a}%nat))(norm 1(read_signal d {b}%nat))).',
                  f'Proof. intro HL. rewrite(eq_w{w} seed d HL). unfold orig_w{w}. cbn[eval_expr]. rewrite ?norm_idempotent. reflexivity. Qed.']
        else:
            raise ValueError(f'unsupported cone wire {w}: {r}')
    # chain of a cone wire down to its source, as a rewriting script
    def down(i):
        """list of rewrite lemmas turning norm 1 (read d i) into an expression over sources"""
        return None
    names = []
    res = {R: None for R, _ in vstages}
    D = '(phase_driven_state P ev pre)'
    resets = [w for w in cone if w in net and net[w][0] == rst0]
    others = [w for w in cone if w not in resets and w != 14]
    # reset-net values (14 is the copy of the primary reset)
    pre_ = f'{hyps}'
    for w in resets:
        L += [f'Lemma rstv_{w} ev pre seed :{hyps}',
              f' norm 1(read_signal{D}{w}%nat)=1.',
              f'Proof. intros {args}. destruct({edge}.prim_driven ev pre Hc)as[_ D1]. rewrite(n_{w} _ {D} HD). rewrite(n_14 _ {D} HD).',
              ' rewrite D1, H1. reflexivity. Qed.']
    for R, i in vstages:
        ex = exprs[R]
        L += [f'Lemma texpr_{R} : ExtendedSVSeqTree.texpr 1%nat {R}%nat ({stage}.tree_of process_{i}) = {T.coq(ex)}. Proof. vm_compute; reflexivity. Qed.']
    regs = [v for v, _ in vstages]
    for R, i in vstages:
        used_resets = [w for w in resets if (1, w) in T.evars(exprs[R])]
        if R == 141:
            concl = f'norm 1(read_signal(PhaseSemantics P ev pre){R}%nat)=norm 1(if Z.eqb f 0 then (if Z.eqb n 0 then norm 1(read_signal pre {R}%nat) else 1) else 0)'
        elif R == 250:
            concl = f'norm 1(read_signal(PhaseSemantics P ev pre){R}%nat)=norm 1(Z.land(norm 1(read_signal pre 141%nat)) n)'
        else:
            prev = {286: 250, 308: 286}[R]
            concl = f'norm 1(read_signal(PhaseSemantics P ev pre){R}%nat)=norm 1(read_signal pre {prev}%nat)'
        rr = ', '.join(f'rstv_{w} ev pre seed {args}' for w in used_resets)
        L += [f'Theorem valid_{R} ev pre seed (f n:Z) :{hyps}',
              f' norm 1(read_signal{D}{flush}%nat)=f -> norm 1(read_signal{D}{nstall}%nat)=n ->',
              f' {concl}.',
              f'Proof. intros {args} Hf Hn. pose proof({stage}.rise_{R} ev pre seed {args}) as H. rewrite texpr_{R} in H. cbn[eval_expr] in H.']
        if rr:
            L.append(f' rewrite ?({rr}) in H.' if len(used_resets) == 1 else ' rewrite ' + ', '.join(f'?(rstv_{w} ev pre seed {args})' for w in used_resets) + ' in H.')
        L.append(' ' + ' '.join(f'rewrite ?(n_{w} _ {D} HD) in H.' for w in others) + ' ' + ' '.join(f'rewrite ?(n_{w} _ {D} HD) in H.' for w in others))
        L.append(' rewrite ?Hf, ?Hn in H.')
        L.append(' ' + ' '.join(f'rewrite ?(ExtendedSVSeqTree.driven_unchanged P ev pre {v}%nat {stage}.comb_unw_{v} ltac:(rewrite Hc; discriminate)) in H.' for v in regs))
        L.append(' rewrite H. cbn[Z.eqb]. destruct (Z.eqb f 0); destruct (Z.eqb n 0); rewrite ?norm_idempotent; reflexivity. Qed.' if R == 141 else ' rewrite H. cbn[Z.eqb]. rewrite ?norm_idempotent. reflexivity. Qed.')
        names.append(f'valid_{R}')
    hdr = (f'(** {design}: tag/valid transport (tools/cpu_tmpl_bzvalid.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' +
           E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection ' + edge.rsplit('.', 1)[0] + ' ' + stage.rsplit('.', 1)[0]).replace('@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVRootProjection'))
    body = hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, [f'{module}.{n}' for n in names], dict(valids=[v for v, _ in vstages])


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='bzeeno')
    ap.add_argument('--module', default='BzTmplValid')
    ap.add_argument('--namespace')
    ap.add_argument('--edge', default='TmplBzEdge.BzTmplEdge.BzTmplEdge')
    ap.add_argument('--stage', default='TmplBzStage.BzTmplStage.BzTmplStage')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    body, exports, info = build(a.design, a.module, a.edge, a.stage)
    if not a.accept:
        Path(a.out).write_text(body); print(a.out, len(body.splitlines())); sys.exit(0)
    import cpu_tmpl_accept as acc
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov, extra=dict(generator='tools/cpu_tmpl_bzvalid.py', design=a.design, info=info))
    print(json.dumps({k: r[k] for k in r if k in ('accepted', 'coqc_seconds', 'coqchk_seconds', 'assumptions')})); sys.exit(0 if r['accepted'] else 1)
