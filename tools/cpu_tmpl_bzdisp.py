#!/usr/bin/env python3
"""Scenario dispatcher for the Bzeeno ID-stage controller facts (ctl v3, r-tmpl-bz-ctl-20261103-a3).

For every class C a theorem `C_n` (and `C_out`): from the premises that the INV supplies (resetn wire 142 = 1, the load-flag wires 153/151 = 0,
the class slices 143/144/145) and ANY values of the hazard leaves (ex_wreg 152, mem_wreg 150, exe_rd 155, mem_rd 154, rs1 146, rs2 147, and
the compare bit of branches) it finds the scenario theorem `<C>_f<ka><kb>_c<atoms>_ctl` whose facts hold, proves `FactsHold` by evaluation, and
returns the controller output.  Case split: the 1-bit leaves and the six 5-bit tests (exe_rd = 0, exe_rd = rs1, exe_rd = rs2, mem_rd = 0, ...)
are destructed; the scenario name is computed here (first firing guard of each forwarding chain, load guards never fire), Coq checks the facts.
Bit combinations without a scenario (pruned as inconsistent in ctl v3) are closed by arithmetic (transitivity of the equality tests).
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import itertools
import json
import re
import sys
from pathlib import Path
import cpu_tmpl_factcheck as FC
import cpu_isa_classes as isa

CTL = Path('results/r-tmpl-bz-ctl-20261103-a4/BzTmplCtl3.v')

HEAD = r"""(** Bzeeno: scenario dispatcher for the ctl v3 facts (tools/cpu_tmpl_bzdisp.py). proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment GeneratedRuntimeInput.ConfiguredAST TmplBzCtl3.BzTmplCtl3.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVBankAlignment BzeenoLoadUseJalASTConfigured3122be4a95.
Local Open Scope Z_scope.
Module BzTmplDisp.
Notation P := bzeeno_load_use_jal_program (only parsing).
Lemma bit_cases (x:Z) : norm 1 x = 0 \/ norm 1 x = 1.
Proof. pose proof (norm_bounds 1 x) as H. cbn in H. lia. Qed.
Lemma n50 : norm 5 0 = 0. Proof. reflexivity. Qed.
Lemma decout_get s outs r w z : DecOut s outs -> In ((r,w),z) outs -> norm w (read_signal s r) = z.
Proof. intros H I. exact (H _ I). Qed.
Ltac fh := let e := fresh "e" in let z := fresh "z" in let Hin := fresh "Hin" in
  intros e z Hin; cbn [In] in Hin;
  repeat (destruct Hin as [Hin|Hin]; [ inversion Hin; subst; clear Hin; cbn [eval_expr];
     repeat match goal with H : ?l = _ |- context [?l] => rewrite H end; reflexivity | ]);
  try contradiction.
Ltac inl := simpl; repeat first [ left; reflexivity | right ]; match goal with |- False => fail 1 | _ => idtac end.
Ltac contra := exfalso; rewrite ?n50 in *;
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H end; lia.
Scheme Equality for UnaryOp.
Scheme Equality for BinaryOp.
Scheme Equality for Expr.
Definition fact_eqb (a b : Expr * Z) : bool := Expr_beq (fst a) (fst b) && Z.eqb (snd a) (snd b).
Lemma fact_eqb_sound a b : fact_eqb a b = true -> a = b.
Proof. destruct a, b. unfold fact_eqb. cbn. intro H. apply andb_prop in H as [H1 H2]. apply internal_Expr_dec_bl in H1. apply Z.eqb_eq in H2. subst. reflexivity. Qed.
(* FactsHold of a scenario list F from its parts G, H, K (computed inclusion) *)
Definition covered (F G H K : Facts) : bool := forallb (fun f => existsb (fact_eqb f) G || existsb (fact_eqb f) H || existsb (fact_eqb f) K) F.
Lemma covered_hold d F G H K : covered F G H K = true -> FactsHold d G -> FactsHold d H -> FactsHold d K -> FactsHold d F.
Proof. intros Hc HG HH HK e z Hin. unfold covered in Hc. rewrite forallb_forall in Hc. pose proof (Hc _ Hin) as H1. cbn in H1.
 apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
 - apply existsb_exists in H1 as [x [Hx E]]. apply fact_eqb_sound in E. subst. exact (HG _ _ Hx).
 - apply existsb_exists in H1 as [x [Hx E]]. apply fact_eqb_sound in E. subst. exact (HH _ _ Hx).
 - apply existsb_exists in H1 as [x [Hx E]]. apply fact_eqb_sound in E. subst. exact (HK _ _ Hx).
Qed.
Lemma fh_nil d : FactsHold d [].
Proof. intros e z H. contradiction. Qed.
Lemma fh_one d id w v : norm w (read_signal d id) = v -> FactsHold d [(EVar w id, v)].
Proof. intros H e z Hin. cbn in Hin. destruct Hin as [Hin|[]]. inversion Hin; subst. cbn [eval_expr]. first [exact H | reflexivity]. Qed.
"""


def coq(e):
    if isinstance(e, str):
        return e
    h = e[0]
    if h == 'EVar':
        return f'(EVar {e[1]} {e[2]}%nat)'
    if h == 'EConst':
        return f'(EConst {e[1]} {e[2]})'
    return '(' + ' '.join([h] + [coq(x) for x in e[1:]]) + ')'


def coqfacts(fl):
    return '[' + '; '.join(f'({coq(e)},{v})' for e, v in fl) + ']'


def classes():
    return [c['name'] for c in isa.classes()]


TESTS = {
    'Z0r': 'norm 5 0 =? norm 5 (read_signal d 155%nat)', 'E1': 'norm 5 (read_signal d 155%nat) =? norm 5 (read_signal d 146%nat)',
    'E2': 'norm 5 (read_signal d 155%nat) =? norm 5 (read_signal d 147%nat)', 'Z0q': 'norm 5 0 =? norm 5 (read_signal d 154%nat)',
    'F1': 'norm 5 (read_signal d 154%nat) =? norm 5 (read_signal d 146%nat)', 'F2': 'norm 5 (read_signal d 154%nat) =? norm 5 (read_signal d 147%nat)'}


def build(only=None):
    sets = FC.scan(CTL.read_text())
    L = [HEAD]
    # class independent guard parts, keyed by (ka, kb, e1e2)
    gp = {}
    allcls = classes()
    meta = {}
    for cl in allcls:
        mine = {k: v for k, v in sets.items() if re.match(f'facts_{cl}_f', k)}
        common = [f for f in next(iter(mine.values())) if all(f in o for o in mine.values())]
        scen = {}
        for k, v in mine.items():
            m = re.match(rf'facts_{cl}_f(\d)(\d)_c(\d*)$', k)
            key = (int(m.group(1)), int(m.group(2)), m.group(3)[-2:])
            cmpbit = m.group(3)[:-2]
            sp = [f for f in v if f not in common and f[0][0] != 'EVar']
            gp.setdefault(key, sp)
            assert gp[key] == sp, (cl, k)
            scen[(key, cmpbit)] = k[len('facts_'):]
        meta[cl] = (common, scen)
    keys = sorted(gp)
    gname = lambda k: f'gp_{k[0]}{k[1]}_{k[2]}'
    for k in keys:
        L.append(f'Definition {gname(k)} : Facts := {coqfacts(gp[k])}.')
    cover = ' \\/ '.join(f'FactsHold d {gname(k)}' for k in keys)
    L.append(f'Theorem guard_cover d : norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> {cover}.')
    L.append('Proof. intros H153 H151.')
    leaves = ['a', 'm', 'Z0r', 'E1', 'E2', 'Z0q', 'F1', 'F2']
    bitleaf = {'a': 152, 'm': 150}

    def disj(idx, n):
        # position idx of an n-ary right-nested disjunction
        t = ''
        for _ in range(idx):
            t += 'right; '
        if idx < n - 1:
            t += 'left'
        return t.rstrip('; ') if t else 'idtac'

    def leaf(val):
        a, m = val['a'], val['m']
        z0r, e1, e2, z0q, f1, f2 = (val[k] for k in ('Z0r', 'E1', 'E2', 'Z0q', 'F1', 'F2'))
        gea, geb = a and not z0r and e1, a and not z0r and e2
        gma, gmb = m and not z0q and f1, m and not z0q and f2
        ka = 0 if gea else (1 if gma else 3)
        kb = 0 if geb else (1 if gmb else 3)
        key = (ka, kb, f'{int(e1)}{int(e2)}')
        if key not in gp:
            return 'contra'
        idx = keys.index(key)
        return f'(({disj(idx, len(keys))}); fh)'

    def rec(i, val):
        if i == len(leaves):
            return leaf(val)
        k = leaves[i]
        if k in bitleaf:
            parts = [rec(i + 1, {**val, k: b}) for b in (0, 1)]
            return f'destruct (bit_cases (read_signal d {bitleaf[k]}%nat)) as [Hb{i}|Hb{i}];\n [' + '\n | '.join(parts) + ']'
        parts = [rec(i + 1, {**val, k: t}) for t in (True, False)]
        return f'destruct ({TESTS[k]}) eqn:Hb{i};\n [' + '\n | '.join(parts) + ']'
    L.append(' ' + rec(0, {}) + '.')
    L.append('Qed.')
    exports = ['guard_cover']
    nk = len(keys)
    for cl in (only or allcls):
        common, scen = meta[cl]
        prem = [(f[0], f[1]) for f in common if f[0][0] == 'EVar']
        cmpid = sorted({e[2] for k, fl in sets.items() if re.match(f'facts_{cl}_f', k) for e, v in fl if e[0] == 'EVar' and (e, v) not in common})
        assert len(cmpid) <= 1, (cl, cmpid)
        cm = [f for f in common if f[0][0] != 'EVar'] + prem
        L.append(f'Definition cm_{cl} : Facts := {coqfacts(common)}.')
        premt = ' -> '.join(f'norm {e[1]} (read_signal d {e[2]}%nat) = {v}' for e, v in prem)
        # common facts hold from the premises (stall guard and A1 vanish with the load flag 153 = 0)
        L.append(f'Lemma cm_{cl}_hold d : norm 1 (read_signal d 153%nat) = 0 -> {premt} -> FactsHold d cm_{cl}.')
        L.append('Proof. intros H153 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + '.')
        L.append(' intros e z Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin|Hin]; [ inversion Hin; subst; clear Hin; cbn [eval_expr]; rewrite ?H153, ?' + ', ?'.join(f'Hp{i}' for i in range(len(prem))) +
                 '; rewrite ?Z.land_0_r, ?Z.land_0_l; cbn; reflexivity | ]); try contradiction.')
        L.append('Qed.')
        L.append(f'Theorem {cl}_n seed d : CombLFP P seed d -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> {premt}' +
                 (f' -> {{xc}}' if cmpid else '') + ' ->')
        L[-1] = L[-1].replace('{xc}', f'(norm 1 (read_signal d {cmpid[0]}%nat) = 0 \\/ norm 1 (read_signal d {cmpid[0]}%nat) = 1)' if cmpid else '')
        L.append(' norm 1 (read_signal d 156%nat) = 1.')
        L.append('Proof. intros HL H153 H151 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + (' Hxc' if cmpid else '') + '.')
        L.append(f' pose proof (cm_{cl}_hold d H153 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + ') as CM.')
        L.append(' destruct (guard_cover d H153 H151) as [' + '|'.join('[' * 0 + f'G{i}' for i in range(nk)) + '] .' if False else '')
        pat = ''
        for i in range(nk - 1):
            pat += f'[G{i}|'
        pat += f'G{nk-1}' + ']' * (nk - 1)
        L.append(f' destruct (guard_cover d H153 H151) as {pat}.')
        for i, k in enumerate(keys):
            def call(nm, kl, kh):
                return (f'exact (decout_get _ _ _ _ _ (BzTmplCtl3.{nm}_ctl seed d HL (covered_hold d BzTmplCtl3.facts_{nm} {gname(k)} cm_{cl} {kl} '
                        f'ltac:(vm_compute; reflexivity) G{i} CM {kh})) ltac:(inl))')
            if not cmpid:
                nm = scen[(k, '')]
                L.append(f' {{ {call(nm, "[]", "(fh_nil d)")}. }}')
            else:
                cid = cmpid[0]
                L.append(f' {{ destruct Hxc as [Hxc|Hxc].')
                for bit in ('0', '1'):
                    nm = scen[(k, bit)]
                    L.append(f'   {{ ' + call(nm, f'[(EVar 1 {cid}%nat,{bit})]', f'(fh_one d {cid}%nat 1 {bit} Hxc)') + '. }')
                L.append(' }')
        L.append('Qed.')
        exports.append(f'{cl}_n')
    L.append('End BzTmplDisp.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L.extend(f'Print Assumptions BzTmplDisp.{e}.' for e in exports)
    return '\n'.join(L) + '\n', exports


if __name__ == '__main__':
    t, ex = build(sys.argv[2].split(',') if len(sys.argv) > 2 else None)
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()), len(ex))
