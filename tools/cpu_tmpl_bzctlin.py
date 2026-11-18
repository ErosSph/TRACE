#!/usr/bin/env python3
"""Controller input wires of the Bzeeno ID stage as register reads: resetn 142 <- 1, mem_wreg 150 <- 279, mem_mem2reg 151 <- 277,
exe_wreg 152 <- 236, exe_mem2reg 153 <- 232, mem_rd 154 <- 283, exe_rd 155 <- 244 (copy chains of the AST), at any comb fixed point.
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_edge as E

TARGETS = [142, 150, 151, 152, 153, 154, 155]


def build(module='BzTmplCtlIn'):
    ast, pr, tr = roles.load_all('bzeeno')
    prog = pr['ast']['program']
    pmod = prog.split('.')[0]
    L = [f'Notation P := {prog.split(".")[-1]} (only parsing).']
    done = set()

    def wire(w):
        if w in done:
            return
        done.add(w)
        cc = ast.comb[w]
        W = cc['width']
        r = cc['rhs']
        assert r[0] == 'EVar' and r[1] == W
        L.extend([f'Definition orig_w{w}:Expr:={T.coq(r)}.',
                  f'Theorem eq_w{w} seed fixed:CombLFP P seed fixed->norm {W}(read_signal fixed {w}%nat)=norm {W}(eval_expr fixed orig_w{w}).',
                  f'Proof. intro HL. refine(checked_assignment_binding P _ {cc["k"]}%nat {cc["name"]} false orig_w{w} {W}%nat {w}%nat seed fixed eq_refl _ _ _ _ HL).',
                  ' all: first[vm_compute;reflexivity|(vm_compute;lia)]. Qed.',
                  f'Theorem n_{w} seed d : CombLFP P seed d -> norm {W}(read_signal d {w}%nat)=norm {W}(read_signal d {r[2]}%nat).',
                  f'Proof. intro HL. rewrite(eq_w{w} seed d HL). unfold orig_w{w}. cbn[eval_expr]. rewrite norm_idempotent. reflexivity. Qed.'])
    names = []
    for t in TARGETS:
        ch = [t]
        w = t
        while w in ast.comb:
            wire(w)
            w = ast.comb[w]['rhs'][2]
            ch.append(w)
        W = ast.sig[t]['width']
        L.extend([f'Theorem ctlin_{t} seed d : CombLFP P seed d -> norm {W}(read_signal d {t}%nat)=norm {W}(read_signal d {ch[-1]}%nat).',
                  'Proof. intro HL. ' + ' '.join(f'rewrite(n_{w} seed d HL).' for w in ch[:-1]) + ' reflexivity. Qed.'])
        names.append(f'ctlin_{t}')
    hdr = (f'(** bzeeno: controller input wires as register reads (tools/cpu_tmpl_bzctlin.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' +
           E.HDR.replace('@AST@', pr['ast']['module']).replace('@OPEN@', pmod))
    return hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)


if __name__ == '__main__':
    Path(sys.argv[1]).write_text(build())
