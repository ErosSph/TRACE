#!/usr/bin/env python3
"""Copy-chain lemmas of the Bzeeno AST at any comb fixed point (generalisation of cpu_tmpl_bzctlin.py).
`ctch_<t>`: norm W (read d t) = norm W (read d s) where s is the end of the copy chain of t (a register/input/process-assigned root);
a chain that ends in a non-copy wire w gives `eq_w<w>` (the checked assignment equation) and `ctch_<t>` stops at w.
Usage: cpu_tmpl_bzcopy.py OUT.v MODULE t1 t2 ...   Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E


def build(module, targets, design='bzeeno'):
    ast, pr, tr = roles.load_all(design)
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).']
    done = set()

    def wire(w, copy):
        if w in done:
            return
        done.add(w)
        cc = ast.comb[w]
        W = cc['width']
        r = cc['rhs']
        L.extend([f'Definition orig_w{w}:Expr:={T.coq(r)}.',
                  f'Theorem eq_w{w} seed fixed:CombLFP P seed fixed->norm {W}(read_signal fixed {w}%nat)=norm {W}(eval_expr fixed orig_w{w}).',
                  f'Proof. intro HL. refine(checked_assignment_binding P _ {cc["k"]}%nat {cc["name"]} false orig_w{w} {W}%nat {w}%nat seed fixed eq_refl _ _ _ _ HL).',
                  ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.'])
        if copy:
            L.extend([f'Theorem n_{w} seed d : CombLFP P seed d -> norm {W}(read_signal d {w}%nat)=norm {W}(read_signal d {r[2]}%nat).',
                      f'Proof. intro HL. rewrite(eq_w{w} seed d HL). unfold orig_w{w}. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.'])
    names = []
    for t in targets:
        ch = [t]
        w = t
        while w in ast.comb:
            r = ast.comb[w]['rhs']
            if r[0] != 'EVar':
                wire(w, False)
                break
            wire(w, True)
            w = r[2]
            ch.append(w)
        if len(ch) > 1:
            W = ast.sig[t]['width']
            L.extend([f'Theorem ctch_{t} seed d : CombLFP P seed d -> norm {W}(read_signal d {t}%nat)=norm {W}(read_signal d {ch[-1]}%nat).',
                      'Proof. intro HL. ' + ' '.join(f'rewrite(n_{x} seed d HL).' for x in ch[:-1]) + ' reflexivity. Qed.'])
            names.append(f'ctch_{t}')
        names.extend(f'eq_w{x}' for x in [ch[-1]] if x in done and not any(f'n_{x} ' in l for l in L))
    hdr = (f'(** {design}: copy chains of the AST as register reads (tools/cpu_tmpl_bzcopy.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' +
           E.HDR.replace('@AST@', pr['ast']['module']).replace('@OPEN@', pmod))
    return hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)


if __name__ == '__main__':
    # generalized_rule (angelo5fix, 2026-11-04): optional --design D as the first two arguments; default bzeeno (unchanged).
    av = sys.argv[1:]
    des = 'bzeeno'
    if av[:1] == ['--design']:
        des, av = av[1], av[2:]
    Path(av[0]).write_text(build(av[1], [int(x) for x in av[2:]], des))
