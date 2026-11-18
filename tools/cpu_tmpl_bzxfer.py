#!/usr/bin/env python3
"""Stage-register transport at the rising edge (Bzeeno template route), generated from the AST.

For every register R of the sequential processes 0..4 (PC, IF/ID, ID/EX, EX/MEM, MEM/WB; valids 141/250/286/308 are in BzTmplValid):
the next value (`PhaseSemantics P ev pre`, the state after the clock event) in terms of the previous registers and of the combinational
source wires at the driven state d.  Copy chains of the AST (`assign a = b`) are followed down to a stop wire (a register, a controller /
mux output, or a wire that the accepted EX/ID facts talk about).  Everything is derived from BzTmplStage.rise_<R> (decision tree of the
process) by rewriting with checked wire equations; Coq checks `texpr = <tree expr>` by computation, so a wrong Python mirror is rejected.
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E
import cpu_tmpl_bzvalid as V

EDGE = 'TmplBzEdge.BzTmplEdge.BzTmplEdge'
STAGE = 'TmplBzStage.BzTmplStage.BzTmplStage'
STOPS = {30, 204, 210, 224, 259, 130, 27, 137, 32, 263, 71, 156, 157}
REGS = {0: [119], 1: [138, 139, 140], 2: [232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249],
        3: [277, 278, 279, 280, 281, 282, 283, 284, 285, 287], 4: [303, 304, 305, 306, 307, 309]}
RESET = {0: 116, 1: 132, 2: 212, 3: 265, 4: 295}
WIDTH = {}


def build(design, module):
    ast, pr, tr = roles.load_all(design)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    sg = ast.sig
    hyps = f'RiseHyps ev pre seed'
    D = '(phase_driven_state P ev pre)'
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).',
         'Definition RiseHyps (ev:Event) (pre:State) (seed:State) : Prop := changed_signal ev = 0%nat /\\ new_value ev = 1 /\\ read_signal pre 0%nat = 0 /\\ read_signal pre 1%nat = 1 /\\',
         f' {EDGE}.NetWords pre /\\ CombLFP P seed pre /\\ CombLFP P(write_signal pre(changed_signal ev)(new_value ev))(phase_driven_state P ev pre).',
         'Ltac unh H := destruct H as [Hc [Hv [H0 [H1 [HW [HL HD]]]]]].']
    done = set()

    def wire(w):
        if w in done:
            return
        done.add(w)
        cc = ast.comb[w]
        W = cc['width']
        L.extend([f'Definition orig_w{w}:Expr:={T.coq(cc["rhs"])}.',
                  f'Theorem eq_w{w} seed fixed:CombLFP P seed fixed->norm {W}(read_signal fixed {w}%nat)=norm {W}(eval_expr fixed orig_w{w}).',
                  f'Proof. intro HL. refine(checked_assignment_binding P _ {cc["k"]}%nat {cc["name"]} false orig_w{w} {W}%nat {w}%nat seed fixed eq_refl _ _ _ _ HL).',
                  ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.'])
        r = cc['rhs']
        assert r[0] == 'EVar' and r[1] == W, (w, r)
        L.extend([f'Theorem n_{w} seed d : CombLFP P seed d -> norm {W}(read_signal d {w}%nat)=norm {W}(read_signal d {r[2]}%nat).',
                  f'Proof. intro HL. rewrite(eq_w{w} seed d HL). unfold orig_w{w}. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.'])

    def chain(w):
        """copy chain from w down to its end (inclusive); only wires before the end get lemmas"""
        out = [w]
        while w not in STOPS and w in ast.comb:
            r = ast.comb[w]['rhs']
            if not (r[0] == 'EVar' and r[1] == ast.comb[w]['width']):
                break
            w = r[2]
            out.append(w)
        return out

    def needs(ws):
        for w in ws[:-1]:
            wire(w)

    # reset values
    names = []
    for p, K in RESET.items():
        ch = chain(K)
        assert ch[-1] == 1, ch
        needs(ch)
    for p, K in RESET.items():
        L += [f'Lemma rstv_{K} ev pre seed : {hyps} -> norm 1(read_signal{D}{K}%nat)=1.',
              f'Proof. intro H. unh H. destruct({EDGE}.prim_driven ev pre Hc)as[_ D1]. ' +
              ' '.join(f'rewrite(n_{w} _ {D} HD).' for w in chain(K)[:-1]) + ' rewrite D1, H1. reflexivity. Qed.']
    uw = lambda x: f'{STAGE}.comb_unw_{x}'

    def drv(x):
        return f'ExtendedSVSeqTree.driven_unchanged P ev pre {x}%nat {uw(x)} ltac:(rewrite Hc; discriminate)'

    all_regs = {x for rs in REGS.values() for x in rs} | {141, 250, 286, 308}
    for p, regs in REGS.items():
        for R in regs:
            W = sg[R]['width']
            ex = V.texpr(ast.procs[p]['body'], R, W)
            L.append(f'Lemma texpr_{R} : ExtendedSVSeqTree.texpr {W}%nat {R}%nat ({STAGE}.tree_of process_{p}) = {T.coq(ex)}. Proof. vm_compute; reflexivity. Qed.')
            rk = RESET[p]
            if p == 0:
                n_c, i_c = chain(117), chain(118)
                needs(n_c); needs(i_c)
                assert n_c[-1] == 156 and i_c[-1] == 130, (n_c, i_c)
                L += [f'Theorem xfer_{R} ev pre seed (n:Z) : {hyps} -> norm 1(read_signal{D}156%nat)=n ->',
                      f' norm {W}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {W}(if Z.eqb n 0 then read_signal pre {R}%nat else read_signal{D}130%nat).',
                      f'Proof. intros HH Hn. pose proof HH as HH0. unh HH. pose proof({STAGE}.rise_{R} ev pre seed Hc Hv H0 H1 HW HL HD) as H. rewrite texpr_{R} in H. cbn[eval_expr] in H.',
                      f' rewrite ?(rstv_{rk} ev pre seed HH0) in H. ' + ' '.join(f'rewrite ?(n_{w} _ {D} HD) in H.' for w in n_c[:-1] + i_c[:-1] + n_c[:-1]),
                      ' rewrite ?Hn in H. rewrite ?(' + drv(R) + ') in H. rewrite H. cbn[Z.eqb]. destruct (Z.eqb n 0); rewrite ?norm_idempotent; reflexivity. Qed.']
                names.append(f'xfer_{R}')
            elif p == 1:
                f_c, n_c = chain(134), chain(133)
                assert f_c[-1] == 157 and n_c[-1] == 156
                leaf = {138: 135, 139: 136, 140: 137}[R]
                l_c = chain(leaf)
                needs(f_c); needs(n_c); needs(l_c)
                const = {138: 0, 139: 0, 140: 28691}[R]
                end = l_c[-1]
                endtxt = f'read_signal pre {end}%nat' if end in all_regs or end == 119 else f'read_signal{D}{end}%nat'
                L += [f'Theorem xfer_{R} ev pre seed (f n:Z) : {hyps} -> norm 1(read_signal{D}157%nat)=f -> norm 1(read_signal{D}156%nat)=n ->',
                      f' norm {W}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {W}(if Z.eqb f 0 then (if Z.eqb n 0 then read_signal pre {R}%nat else {endtxt}) else {const}).',
                      f'Proof. intros HH Hf Hn. pose proof HH as HH0. unh HH. pose proof({STAGE}.rise_{R} ev pre seed Hc Hv H0 H1 HW HL HD) as H. rewrite texpr_{R} in H. cbn[eval_expr] in H.',
                      f' rewrite ?(rstv_{rk} ev pre seed HH0) in H. ' + ' '.join(f'rewrite ?(n_{w} _ {D} HD) in H.' for w in f_c[:-1] + n_c[:-1] + l_c[:-1] + f_c[:-1] + n_c[:-1] + l_c[:-1]),
                      ' rewrite ?Hf, ?Hn in H. rewrite ?(' + drv(R) + ') in H.' + (f' rewrite ?({drv(end)}) in H.' if end in all_regs or end == 119 else ''),
                      ' rewrite H. cbn[Z.eqb]. destruct (Z.eqb f 0); destruct (Z.eqb n 0); rewrite ?norm_idempotent; reflexivity. Qed.']
                names.append(f'xfer_{R}')
            else:
                tail = ex
                while tail[0] == 'ECond':
                    tail = tail[3]
                assert tail[0] == 'EVar', (R, ex)
                l_c = chain(tail[2])
                needs(l_c)
                end = l_c[-1]
                isreg = end in all_regs
                endtxt = f'read_signal pre {end}%nat' if isreg else f'read_signal{D}{end}%nat'
                L += [f'Theorem xfer_{R} ev pre seed : {hyps} ->',
                      f' norm {W}(read_signal(PhaseSemantics P ev pre){R}%nat)=norm {W}({endtxt}).',
                      f'Proof. intro HH. pose proof HH as HH0. unh HH. pose proof({STAGE}.rise_{R} ev pre seed Hc Hv H0 H1 HW HL HD) as H. rewrite texpr_{R} in H. cbn[eval_expr] in H.',
                      f' rewrite ?(rstv_{rk} ev pre seed HH0) in H. ' + ' '.join(f'rewrite ?(n_{w} _ {D} HD) in H.' for w in l_c[:-1] + l_c[:-1]) +
                      (f' rewrite ?({drv(end)}) in H.' if isreg else ''),
                      ' rewrite H. cbn[Z.eqb]. rewrite ?norm_idempotent. reflexivity. Qed.']
                names.append(f'xfer_{R}')
    # the instruction rd field (ID/EX rd input is a part select of the IF/ID instruction)
    wire(28)
    cc = ast.comb[32]
    L.extend([f'Definition orig_w32:Expr:={T.coq(cc["rhs"])}.',
              f'Theorem eq_w32 seed fixed:CombLFP P seed fixed->norm 5(read_signal fixed 32%nat)=norm 5(eval_expr fixed orig_w32).',
              f'Proof. intro HL. refine(checked_assignment_binding P _ {cc["k"]}%nat {cc["name"]} false orig_w32 5%nat 32%nat seed fixed eq_refl _ _ _ _ HL).',
              ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.'])
    L += ['Theorem rd_field seed d : CombLFP P seed d -> norm 5(read_signal d 32%nat)=norm 5(Z.shiftr(norm 32(read_signal d 140%nat))7).',
          'Proof. intro HL. rewrite(eq_w32 seed d HL). unfold orig_w32. cbn[eval_expr]. rewrite(n_28 seed d HL). rewrite ?norm_idempotent. reflexivity. Qed.']
    names.append('rd_field')
    # the rd select feeds xfer_244 (its chain stops at 32): restate through the field
    L += [f'Theorem xfer_244_field ev pre seed : {hyps} -> norm 5(read_signal(PhaseSemantics P ev pre)244%nat)=norm 5(Z.shiftr(norm 32(read_signal pre 140%nat))7).',
          f'Proof. intro HH. pose proof HH as HH0. unh HH. rewrite(xfer_244 ev pre seed HH0). rewrite(rd_field _ {D} HD). rewrite ?({drv(140)}). reflexivity. Qed.']
    names.append('xfer_244_field')
    hdr = (f'(** {design}: stage-register transport at the rising edge (tools/cpu_tmpl_bzxfer.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' +
           E.HDR.replace('@AST@', pr['ast']['module'] + ' Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection ' + EDGE.rsplit('.', 1)[0] + ' ' + STAGE.rsplit('.', 1)[0]).replace(
               '@OPEN@', pmod + ' ExtendedSVSeqTree ExtendedSVRootProjection'))
    body = hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return body, names


if __name__ == '__main__':
    body, names = build('bzeeno', 'BzTmplXfer')
    Path(sys.argv[1]).write_text(body)
    print(sys.argv[1], len(body.splitlines()), len(names))
