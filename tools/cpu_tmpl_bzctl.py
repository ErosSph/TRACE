#!/usr/bin/env python3
"""Bzeeno ID-stage controller facts per ISA class (goal 3), on the CV32E40P agent's symbolic executor.

Controller = one blocking comb process whose opcode/funct3/funct7 are separate input wires (roles pipeline_roles.controller).
Scenario (explicit hypotheses of each theorem, never assumed elsewhere): resetn = 1 and the hazard inputs listed in
`--base` (default: EX/MEM write enables and load flags = 0, i.e. no producer in flight; no loads exist in the domain).
Theorem per class:  CombLFP P seed fixed -> FactsHold fixed facts_C -> DecOut fixed outs_C.
Untrusted generator; Coq checks everything (ExtendedSVSymExec.comb_process_outs).
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import argparse
import json
import sys
from pathlib import Path
import cpu_tmpl_ast as T
import cpu_tmpl_roles as roles
import cpu_tmpl_symexec as X
import cpu_tmpl_decoder as D
import cpu_isa_classes as isa
import cpu_class_table as ct
import cpu_tmpl_factcheck as FC


def run(design, names, module, fuel=512, base_roles=('ex_write', 'ex_load', 'mem_write', 'mem_load'), atoms=False, check='warn'):
    ast, pr, tr = roles.load_all(design)
    c = pr['controller']
    proc = int(c['controller_process'].split('_')[1])
    k = ast.comb_ids.index(proc)
    wire = lambda n: ('EVar', c[n]['width'], c[n]['id'])
    body0 = ast.procs[proc]['body']
    seq = body0[1][0][1]

    def guards(s, acc):
        if s[0] == 'SIf':
            acc.append(s[1]); guards(s[2], acc); guards(s[3], acc)
        elif s[0] == 'SSeq':
            for x in s[1]:
                guards(x, acc)
        return acc
    # hazard guards: every SIf guard of the leading forwarding ifs and of the load-use stall if (those that read stage tags)
    tagset = {c[n]['id'] for n in base_roles} | {c['ex_rd']['id'], c['mem_rd']['id']}
    hz = []
    for s in seq:
        if s[0] == 'SIf' and T.evars(s[1]) & {(w, i) for i in tagset for w in (1, 5)} and not any(
                i in {c['pcsrc']['id'], c['enable']['id']} for _, i in T.evars(s[1])):
            for g in guards(s, []):
                if g not in hz:
                    hz.append(g)
    # forwarding chains: the leading statements `if g1 (fwd=1) else if g2 (fwd=2) else if g3 (fwd=3)`; scenario k = the k-th guard fires first
    fchains = []
    for s in seq:
        if s[0] == 'SIf' and T.evars(s[1]) & {(w, i) for i in tagset for w in (1, 5)} and not any(
                i in {c['pcsrc']['id'], c['enable']['id']} for _, i in T.evars(s[1])):
            ch, cur = [], s
            while cur[0] == 'SIf':
                ch.append(cur[1]); cur = cur[3]
            fsel = {c['forward_a']['id'], c['forward_b']['id']}
            if s[2][0] == 'SAssign' and s[2][3][0] == 'LVar' and s[2][3][2] in fsel:
                fchains.append(ch)
    hz = [g for ch in fchains for g in ch]
    # remaining hazard guards (load-use stall etc.) stay 0: no loads in the domain
    rest = []
    for s in seq:
        if s[0] == 'SIf' and T.evars(s[1]) & {(w, i) for i in tagset for w in (1, 5)} and not any(
                i in {c['pcsrc']['id'], c['enable']['id']} for _, i in T.evars(s[1])):
            for g in guards(s, []):
                if g not in hz and g not in rest:
                    rest.append(g)
    import itertools

    def scen(choice):
        out = []
        for ch, k in zip(fchains, choice):
            for j, g in enumerate(ch):
                if j < k:
                    out.append((g, 0))
                elif j == k:
                    out.append((g, 1))
                    break
            else:
                pass
        return out
    scen_names = list(itertools.product(*[range(len(ch) + 1) for ch in fchains]))   # k = len(ch): no guard fires
    def scen_facts(choice):
        out = []
        for ch, k in zip(fchains, choice):
            for j, g in enumerate(ch):
                if j < k:
                    out.append((g, 0))
                elif j == k:
                    out.append((g, 1))
        return out
    base0 = [(wire('controller_resetn'), 1)] + [(g, 0) for g in rest]
    import cpu_tmpl_edge as E
    nsig = max(ast.sig) + 1
    wt = [[] for _ in range(nsig)]
    for kk, i in enumerate(ast.comb_ids):
        for r in E.assigned_roots(ast.procs[i]['body']):
            wt[r].append(kk)
    later = lambda r: all(j < k + 1 for j in wt[r])      # wr_lt T r (S k)
    cls = [x for x in isa.classes() if names == 'all' or x['name'] in names.split(',')]
    body = ['Definition wtab:list(list nat):=[' + '; '.join('[' + ';'.join(f'{x}%nat' for x in w) + ']' for w in wt) + '].',
            'Definition comb_ps:=filter is_comb (processes P).',
            'Lemma wtab_ok:TabC comb_ps wtab.', 'Proof. apply tab_okb_sound. vm_compute;reflexivity. Qed.']
    info = {}
    def runit(bf, slices):
        old = X.Exec
        X.Exec = X._Atoms if atoms else X._Tracing
        try:
            return X.close_facts(ast.procs[proc]['body'], None, bf + slices, fuel, [])
        finally:
            X.Exec = old
    cands = []
    for cl in cls:
        slices = [(wire('opcode'), cl['opcode'])]
        if ct.isa_f3(cl) is not None:
            slices.append((wire('funct3'), ct.isa_f3(cl)))
        if cl['name'] in ct.SHIFT_IMM or cl['group'] == 'OP':
            slices.append((wire('funct7'), cl['funct7']))
        n0 = cl['name']
        for ch in scen_names:
            bf = base0 + scen_facts(ch)
            _, extra, _ov = runit(bf, slices)
            loadids = (c['ex_load']['id'], c['mem_load']['id'])
            if atoms:    # v3: an atom mentioning a load flag is pinned to 0 (the domain has no loads)
                noload = [e for e in extra if {i for _, i in X.inputs(e)} & set(loadids)]
            else:
                noload = [e for e in extra if e[2] in loadids]    # the domain has no loads
            bits = [e for e in extra if e[1] == 1 and e not in noload]
            others = [e for e in extra if e[1] != 1] + noload
            for vals in itertools.product((0, 1), repeat=len(bits)):
                bff = bf + list(zip(bits, vals)) + [(e, 0) for e in others]
                _, ex2, ov = runit(bff, slices)
                assert not ex2
                allfacts = bff + slices
                outs = sorted((r, w, z) for r, (w, z) in ov.items() if later(r))
                n = n0 + '_f' + ''.join(map(str, ch)) + ('_c' + ''.join(map(str, vals)) if vals else '')
                cands.append((n, n0, ch, bits, vals, allfacts, outs))
    # non-vacuity filter (tools/cpu_tmpl_factcheck.py, z3): every emitted fact set must be satisfiable
    verdict = FC.check_sets({c_[0]: c_[5] for c_ in cands})
    unsat = [c_[0] for c_ in cands if verdict[c_[0]][0] != 'sat']
    if unsat and check == 'fail' and not atoms:
        raise SystemExit(f'factcheck: {len(unsat)} vacuous fact sets, e.g. {unsat[:4]}')
    if unsat and not atoms:
        print(f'WARNING factcheck: {len(unsat)} of {len(cands)} fact sets are unsatisfiable (vacuous): {unsat[:4]}', file=sys.stderr)
    if atoms:     # inconsistent atom combinations are pruned (recorded), the rest must be satisfiable
        pruned = unsat
        cands = [c_ for c_ in cands if verdict[c_[0]][0] == 'sat']
    else:
        pruned = []
    for n, n0, ch, bits, vals, allfacts, outs in cands:
        info[n] = dict(outputs=len(outs), facts=len(allfacts), class_=n0, fwd=list(ch), cmp=[list(e)[2] if e[0] == 'EVar' else T.coq(e) for e in bits], cmpvals=list(vals))
        idx = ';'.join(f'{j}%nat' for j in range(len(allfacts)))
        body += [f'Definition facts_{n}:Facts:={D.coq_facts(allfacts)}.',
                 f'Definition ks_{n}:list(nat*list nat):=[({k}%nat,[{idx}])].',
                 f'Definition outs_{n}:list((signal*nat)*Z):=[' + '; '.join(f'(({r}%nat,{w}%nat),{z})' for r, w, z in outs) + '].',
                 f'Theorem {n}_ctl seed fixed:CombLFP P seed fixed->FactsHold fixed facts_{n}->DecOut fixed outs_{n}.',
                 f'Proof. intros HL HF. exact(chain_outs_tab P comb_ps wtab ks_{n} facts_{n} outs_{n} seed fixed eq_refl wtab_ok HF HL (ltac:(vm_compute;reflexivity))). Qed.']
    info['__meta__'] = dict(pruned_unsat=len(pruned), emitted=len(cands))
    exports = [f'{module}.{n}_ctl' for n in info if n != '__meta__']
    pre = D.PREAMBLE.replace('Lang.ExtendedSVSymExec', 'Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain').replace('ExtendedSVSymExec @ASTNS@', 'ExtendedSVSymExec ExtendedSVFactChain @ASTNS@').replace('@AST@', pr['ast']['module']).replace('@ASTNS@', pr['ast']['program'].split('.')[0]).replace('@PROG@', pr['ast']['program'].split('.')[-1])
    text = (f'(** {design}: ID-stage controller facts per class (tools/cpu_tmpl_bzctl.py). proof_author: {T.PROOF_AUTHOR}; external_llm_api_calls=0. *)\n' + pre +
            f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {e}.\n' for e in exports))
    return text, exports, info


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='bzeeno')
    ap.add_argument('--classes', default='all')
    ap.add_argument('--module', default='BzTmplCtl')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--atoms', action='store_true', help='ctl v3: enumerate unwritten 1-bit sub-expressions instead of pinning 5-bit leaves')
    a = ap.parse_args()
    text, exports, info = run(a.design, a.classes, a.module, atoms=a.atoms)
    if not a.accept:
        Path(a.out).write_text(text); print(a.out, len(text.splitlines()), info); sys.exit(0)
    import cpu_tmpl_accept as acc
    prof = json.loads(Path(f'framework/auto-contract-profiles/{a.design}.json').read_text())
    lp = [(prof['pipeline_roles']['ast']['file'].rsplit('/', 1)[0], prof['pipeline_roles']['ast']['module'].split('.')[0])]
    r = acc.accept(a.out, a.namespace, a.module, text, exports, lp, extra=dict(generator='tools/cpu_tmpl_bzctl.py', design=a.design, per_class=info))
    print(json.dumps({k: r[k] for k in r if k != 'per_class'}, indent=1)); sys.exit(0 if r['accepted'] else 1)
