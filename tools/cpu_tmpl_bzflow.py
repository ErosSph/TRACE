#!/usr/bin/env python3
"""Bzeeno ID-stage control-flow outputs per class: flush 157, pcsrc 159, jalr select 167 at any comb fixed point of the ID stage
(module BzTmplFlow).  Same dispatch as cpu_tmpl_bzdisp.py / cpu_tmpl_bztrans.py (the 27 guard parts of TmplBzDisp over the scenario theorems of
ctl v3), conclusion `Fl d c157 c159 c167`.  Branch classes: one conclusion per value of the compare bit (148 or 149).
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path
import cpu_isa_classes as isa
import cpu_tmpl_bzdisp as DP
import cpu_tmpl_bztrans as TB

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'

HEAD = r"""(** Bzeeno: control-flow outputs of the ID-stage controller per class (tools/cpu_tmpl_bzflow.py).
    flush 157, pcsrc 159 and jalr select 167 at any comb fixed point whose controller inputs are those of the class.
    proof_author: """ + AUTHOR + r"""; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment GeneratedRuntimeInput.ConfiguredAST
 TmplBzCtl3.BzTmplCtl3 TmplBzDisp.BzTmplDisp TmplBzDisp2.BzTmplDisp2.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVBankAlignment BzeenoLoadUseJalASTConfigured3122be4a95 TmplBzDisp.BzTmplDisp.BzTmplDisp TmplBzDisp2.BzTmplDisp2.BzTmplDisp2.
Local Open Scope Z_scope.
Module BzTmplFlow.
Notation P := bzeeno_load_use_jal_program (only parsing).
Definition Fl (d : State) (c157 c159 c167 : Z) : Prop :=
 norm 1 (read_signal d 157%nat) = c157 /\ norm 2 (read_signal d 159%nat) = c159 /\ norm 1 (read_signal d 167%nat) = c167.
Lemma fl_of d outs c157 c159 c167 : DecOut d outs -> (has outs 157 1 c157 && has outs 159 2 c159 && has outs 167 1 c167)%bool = true -> Fl d c157 c159 c167.
Proof. intros H Hc. repeat rewrite andb_true_iff in Hc. destruct Hc as [[H1 H2] H3]. unfold Fl. repeat split; eapply has_sound; eauto. Qed.
"""


def outs_table():
    """{(class, bit or ''): {157: v, 159: v, 167: v}} over all scenarios (asserted uniform per (class, bit))."""
    t = DP.CTL.read_text()
    res = {}
    for m in re.finditer(r'^Definition outs_(\w+?)_f(\d)(\d)_c(\d*):list\(\(signal\*nat\)\*Z\):=(.*)\.$', t, re.M):
        cl, cs = m.group(1), m.group(4)
        bit = cs[:-2]
        d = {int(a): int(c) for a, b, c in re.findall(r'\(\((\d+)%nat,(\d+)%nat\),(-?\d+)\)', m.group(5))}
        for k in (157, 159, 167):
            res.setdefault((cl, bit), {}).setdefault(k, set()).add(d[k])
    out = {}
    for key, d in res.items():
        for k, v in d.items():
            assert len(v) == 1, (key, k, v)
        out[key] = {k: next(iter(v)) for k, v in d.items()}
    return out


def build(only=None):
    sets, gp, metas = TB.meta()
    outs = outs_table()
    keys = sorted(gp)
    gname = lambda k: f'gp_{k[0]}{k[1]}_{k[2]}'
    nk = len(keys)
    L = [HEAD]
    exports = ['fl_of']
    for cl in (only or [c['name'] for c in isa.classes()]):
        common, scen = metas[cl]
        prem = [(f[0], f[1]) for f in common if f[0][0] == 'EVar']
        cmpid = sorted({e[2] for k, fl in sets.items() if re.match(f'facts_{cl}_f', k) for e, v in fl if e[0] == 'EVar' and (e, v) not in common})
        assert len(cmpid) <= 1, (cl, cmpid)
        premt = ' -> '.join(f'norm {e[1]} (read_signal d {e[2]}%nat) = {v}' for e, v in prem)
        bits = ['0', '1'] if cmpid else ['']
        concl = []
        for b in bits:
            o = outs[(cl, b)]
            concl.append((b, o[157], o[159], o[167]))
        if cmpid:
            cid = cmpid[0]
            ct = ' /\\ '.join(f'(norm 1 (read_signal d {cid}%nat) = {b} -> Fl d {c1} {c2} {c3})' for b, c1, c2, c3 in concl)
        else:
            ct = 'Fl d {} {} {}'.format(*concl[0][1:])
        L.append(f'Theorem {cl}_f seed d : CombLFP P seed d -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> {premt} -> {ct}.')
        L.append('Proof. intros HL H153 H151 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + '.')
        L.append(f' pose proof (cm_{cl}_hold d H153 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + ') as CM.')
        if cmpid:
            L.append(' split; intro Hx.')
        pat = ''
        for i in range(nk - 1):
            pat += f'[G{i}|'
        pat += f'G{nk-1}' + ']' * (nk - 1)
        for bi, (b, c1, c2, c3) in enumerate(concl):
            L.append(f' destruct (guard_cover d H153 H151) as {pat}.')
            for i, k in enumerate(keys):
                nm = metas[cl][1][(k, b)]
                if not cmpid:
                    kl, kh = '[]', '(fh_nil d)'
                else:
                    kl, kh = f'[(EVar 1 {cmpid[0]}%nat,{b})]', f'(fh_one d {cmpid[0]}%nat 1 {b} Hx)'
                L.append(f' {{ exact (fl_of d _ {c1} {c2} {c3} (BzTmplCtl3.{nm}_ctl seed d HL (covered_hold d BzTmplCtl3.facts_{nm} {gname(k)} cm_{cl} {kl} '
                         f'ltac:(vm_compute; reflexivity) G{i} CM {kh})) ltac:(vm_compute; reflexivity)). }}')
        L.append('Qed.')
        exports.append(f'{cl}_f')
    L.append('End BzTmplFlow.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L.extend(f'Print Assumptions BzTmplFlow.{e}.' for e in exports)
    return '\n'.join(L) + '\n', exports


if __name__ == '__main__':
    t, ex = build(sys.argv[2].split(',') if len(sys.argv) > 2 else None)
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()), len(ex))
