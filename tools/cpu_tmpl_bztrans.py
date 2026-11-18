#!/usr/bin/env python3
"""Bzeeno template route, transport goal (goal_transport of BzTmplStep): generators for
  disp2  : BzTmplDisp2  - the scenario dispatcher of cpu_tmpl_bzdisp.py extended from `156 = 1` to all controller outputs the EX clause needs
                          (class constants + the forwarding selects 160/161 as computed functions ASEL/BSEL of the hazard leaves),
  fwdin  : BzTmplFwdIn  - copy chains 312/313 <- 33/34 <- 146/147 (operand register indices of the RF read ports),
  core / cls / main : see below (added incrementally).
Class table: cpu_isa_classes.classes().  Untrusted generator.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path
import cpu_tmpl_factcheck as FC
import cpu_isa_classes as isa
import cpu_tmpl_bzdisp as DP

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
CTL = DP.CTL
KEYS = [156, 158, 162, 163, 164, 165, 166, 168, 169, 173, 174, 175]
SELMAP = {0: 1, 1: 2, 2: 3, 3: 0}   # scenario index ka -> select value of the forwarding mux (0 = register file, 1 = EX result, 2 = MEM result)


def ctl_outs():
    """per class: constants of KEYS over all non-load scenarios (asserted uniform)."""
    t = CTL.read_text()
    res = {}
    for m in re.finditer(r'^Definition outs_(\w+?)_f(\d)(\d)_c(\d*):list\(\(signal\*nat\)\*Z\):=(.*)\.$', t, re.M):
        cl, ka, kb = m.group(1), int(m.group(2)), int(m.group(3))
        if ka == 2 or kb == 2:
            continue
        d = {int(a): (int(b), int(c)) for a, b, c in re.findall(r'\(\((\d+)%nat,(\d+)%nat\),(-?\d+)\)', m.group(5))}
        for k in KEYS:
            res.setdefault(cl, {}).setdefault(k, set()).add(d[k])
    out = {}
    for cl, d in res.items():
        for k, v in d.items():
            assert len(v) == 1, (cl, k, v)
        out[cl] = {k: next(iter(v)) for k, v in d.items()}
    return out


def disp2_head():
    return r'''(** Bzeeno: scenario dispatcher, controller outputs of the EX clause (tools/cpu_tmpl_bztrans.py disp2).
    Extends TmplBzDisp (`<C>_n`: 156 = 1) to `Cout`: 156 = 1, the forwarding selects 160/161 = ASEL/BSEL (functions of the hazard leaves) and the
    class constants 158 162 163 164 165 166 168 169 173 174 175.  proof_author: ''' + AUTHOR + r'''; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVWordInvariant Lang.ExtendedSVBankAlignment GeneratedRuntimeInput.ConfiguredAST TmplBzCtl3.BzTmplCtl3 TmplBzDisp.BzTmplDisp.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVBankAlignment BzeenoLoadUseJalASTConfigured3122be4a95 TmplBzDisp.BzTmplDisp.BzTmplDisp.
Local Open Scope Z_scope.
Module BzTmplDisp2.
Notation P := bzeeno_load_use_jal_program (only parsing).
Definition ASEL (d : State) : Z :=
 if (norm 1 (read_signal d 152%nat) =? 1) && negb (norm 5 0 =? norm 5 (read_signal d 155%nat)) && (norm 5 (read_signal d 155%nat) =? norm 5 (read_signal d 146%nat)) then 1
 else if (norm 1 (read_signal d 150%nat) =? 1) && negb (norm 5 0 =? norm 5 (read_signal d 154%nat)) && (norm 5 (read_signal d 154%nat) =? norm 5 (read_signal d 146%nat)) then 2 else 0.
Definition BSEL (d : State) : Z :=
 if (norm 1 (read_signal d 152%nat) =? 1) && negb (norm 5 0 =? norm 5 (read_signal d 155%nat)) && (norm 5 (read_signal d 155%nat) =? norm 5 (read_signal d 147%nat)) then 1
 else if (norm 1 (read_signal d 150%nat) =? 1) && negb (norm 5 0 =? norm 5 (read_signal d 154%nat)) && (norm 5 (read_signal d 154%nat) =? norm 5 (read_signal d 147%nat)) then 2 else 0.
Definition Cout (d : State) (c158 c162 c165 c166 c168 c169 c173 c174 c175 : Z) : Prop :=
 norm 1 (read_signal d 156%nat) = 1 /\ norm 2 (read_signal d 160%nat) = ASEL d /\ norm 2 (read_signal d 161%nat) = BSEL d /\
 norm 6 (read_signal d 158%nat) = c158 /\ norm 1 (read_signal d 162%nat) = c162 /\ norm 1 (read_signal d 163%nat) = 0 /\ norm 1 (read_signal d 164%nat) = 0 /\
 norm 1 (read_signal d 165%nat) = c165 /\ norm 1 (read_signal d 166%nat) = c166 /\ norm 1 (read_signal d 168%nat) = c168 /\ norm 1 (read_signal d 169%nat) = c169 /\
 norm 1 (read_signal d 173%nat) = c173 /\ norm 1 (read_signal d 174%nat) = c174 /\ norm 1 (read_signal d 175%nat) = c175.
Definition has (outs : list ((signal * nat) * Z)) (r w : nat) (z : Z) : bool :=
 existsb (fun o => match o with ((r', w'), z') => Nat.eqb r r' && Nat.eqb w w' && Z.eqb z z' end) outs.
Lemma has_sound d outs r w z : DecOut d outs -> has outs r w z = true -> norm w (read_signal d r) = z.
Proof. intros H Hh. unfold has in Hh. apply existsb_exists in Hh as [[[r' w'] z'] [Hin He]].
 apply andb_prop in He as [He Hz]. apply andb_prop in He as [Hr Hw]. apply Nat.eqb_eq in Hr. apply Nat.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst. exact (H _ Hin). Qed.
Definition chk (outs : list ((signal * nat) * Z)) (sa sb c158 c162 c165 c166 c168 c169 c173 c174 c175 : Z) : bool :=
 has outs 156 1 1 && has outs 160 2 sa && has outs 161 2 sb && has outs 158 6 c158 && has outs 162 1 c162 && has outs 163 1 0 && has outs 164 1 0 &&
 has outs 165 1 c165 && has outs 166 1 c166 && has outs 168 1 c168 && has outs 169 1 c169 && has outs 173 1 c173 && has outs 174 1 c174 && has outs 175 1 c175.
Lemma cout_of d outs sa sb c158 c162 c165 c166 c168 c169 c173 c174 c175 : DecOut d outs -> chk outs sa sb c158 c162 c165 c166 c168 c169 c173 c174 c175 = true ->
 ASEL d = sa -> BSEL d = sb -> Cout d c158 c162 c165 c166 c168 c169 c173 c174 c175.
Proof. intros H Hc HA HB. unfold chk in Hc. repeat rewrite andb_true_iff in Hc.
 destruct Hc as [[[[[[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10] H11] H12] H13] H14].
 unfold Cout. rewrite HA, HB. repeat split; eapply has_sound; eauto. Qed.
Lemma Cout_sel d a b c e f g h i j : Cout d a b c e f g h i j -> norm 2 (read_signal d 160%nat) = ASEL d /\ norm 2 (read_signal d 161%nat) = BSEL d.
Proof. intros [_ [H1 [H2 _]]]. split; assumption. Qed.
'''


def meta():
    sets = FC.scan(CTL.read_text())
    gp = {}
    metas = {}
    for cl in [c['name'] for c in isa.classes()]:
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
        metas[cl] = (common, scen)
    return sets, gp, metas


def disp2(only=None, admit_cover=False):
    sets, gp, metas = meta()
    outs = ctl_outs()
    keys = sorted(gp)
    gname = lambda k: f'gp_{k[0]}{k[1]}_{k[2]}'
    nk = len(keys)
    L = [disp2_head()]
    cover = ' \\/ '.join(f'(FactsHold d {gname(k)} /\\ ASEL d = {SELMAP[k[0]]} /\\ BSEL d = {SELMAP[k[1]]})' for k in keys)
    L.append(f'Theorem guard_cover2 d : norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> {cover}.')
    L.append('Proof. intros H153 H151.' if not admit_cover else 'Proof. Admitted.')
    leaves = ['a', 'm', 'Z0r', 'E1', 'E2', 'Z0q', 'F1', 'F2']
    bitleaf = {'a': 152, 'm': 150}

    def disj(idx, n):
        t = ''
        for _ in range(idx):
            t += 'right; '
        if idx < n - 1:
            t += 'left'
        return t.rstrip('; ') if t else 'idtac'

    rw = ', '.join(f'?Hb{i}' for i in range(len(leaves)))

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
        return (f'(({disj(idx, nk)}); split; [fh | split; [unfold ASEL; rewrite {rw}; reflexivity | unfold BSEL; rewrite {rw}; reflexivity]])')

    def rec(i, val):
        if i == len(leaves):
            return leaf(val)
        k = leaves[i]
        if k in bitleaf:
            parts = [rec(i + 1, {**val, k: b}) for b in (0, 1)]
            return f'destruct (bit_cases (read_signal d {bitleaf[k]}%nat)) as [Hb{i}|Hb{i}];\n [' + '\n | '.join(parts) + ']'
        parts = [rec(i + 1, {**val, k: t}) for t in (True, False)]
        return f'destruct ({DP.TESTS[k]}) eqn:Hb{i};\n [' + '\n | '.join(parts) + ']'
    if not admit_cover:
        L.append(' ' + rec(0, {}) + '.')
        L.append('Qed.')
    exports = ['guard_cover2', 'Cout_sel']
    for cl in (only or [c['name'] for c in isa.classes()]):
        common, scen = metas[cl]
        prem = [(f[0], f[1]) for f in common if f[0][0] == 'EVar']
        cmpid = sorted({e[2] for k, fl in sets.items() if re.match(f'facts_{cl}_f', k) for e, v in fl if e[0] == 'EVar' and (e, v) not in common})
        assert len(cmpid) <= 1, (cl, cmpid)
        premt = ' -> '.join(f'norm {e[1]} (read_signal d {e[2]}%nat) = {v}' for e, v in prem)
        o = outs[cl]
        cons = ' '.join(str(o[k][1]) for k in (158, 162, 165, 166, 168, 169, 173, 174, 175))
        assert o[156][1] == 1 and o[163][1] == 0 and o[164][1] == 0, cl
        hx = (f'(norm 1 (read_signal d {cmpid[0]}%nat) = 0 \\/ norm 1 (read_signal d {cmpid[0]}%nat) = 1) -> ' if cmpid else '')
        L.append(f'Theorem {cl}_o seed d : CombLFP P seed d -> norm 1 (read_signal d 153%nat) = 0 -> norm 1 (read_signal d 151%nat) = 0 -> {premt} -> {hx}Cout d {cons}.')
        L.append('Proof. intros HL H153 H151 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + (' Hxc' if cmpid else '') + '.')
        L.append(f' pose proof (cm_{cl}_hold d H153 ' + ' '.join(f'Hp{i}' for i in range(len(prem))) + ') as CM.')
        pat = ''
        for i in range(nk - 1):
            pat += f'[(G{i} & GA{i} & GB{i})|'
        pat += f'(G{nk-1} & GA{nk-1} & GB{nk-1})' + ']' * (nk - 1)
        L.append(f' destruct (guard_cover2 d H153 H151) as {pat}.')
        fin = None
        for i, k in enumerate(keys):
            def call(nm, kl, kh):
                return (f'exact (cout_of d _ {SELMAP[k[0]]} {SELMAP[k[1]]} {cons} (BzTmplCtl3.{nm}_ctl seed d HL (covered_hold d BzTmplCtl3.facts_{nm} {gname(k)} cm_{cl} {kl} '
                        f'ltac:(vm_compute; reflexivity) G{i} CM {kh})) ltac:(vm_compute; reflexivity) GA{i} GB{i})')
            if not cmpid:
                nm = metas[cl][1][(k, '')]
                L.append(f' {{ {call(nm, "[]", "(fh_nil d)")}. }}')
            else:
                cid = cmpid[0]
                L.append(' { destruct Hxc as [Hxc|Hxc].')
                for bit in ('0', '1'):
                    nm = metas[cl][1][(k, bit)]
                    L.append('   { ' + call(nm, f'[(EVar 1 {cid}%nat,{bit})]', f'(fh_one d {cid}%nat 1 {bit} Hxc)') + '. }')
                L.append(' }')
        L.append('Qed.')
        exports.append(f'{cl}_o')
    L.append('End BzTmplDisp2.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    L.extend(f'Print Assumptions BzTmplDisp2.{e}.' for e in exports)
    return '\n'.join(L) + '\n', exports


def fwdin(module='BzTmplFwdIn'):
    """operand register indices of the RF read ports: 312 and 146 are copies of 33 (rs1 field), 313 and 147 of 34 (rs2 field)."""
    import cpu_tmpl_ast as T
    import cpu_tmpl_roles as roles
    import cpu_tmpl_edge as E
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
    for a, b, base in ((312, 146, 33), (313, 147, 34)):
        for w in (a, b):
            assert ast.comb[w]['rhs'][2] == base, (w, ast.comb[w]['rhs'])
            wire(w)
        L.extend([f'Theorem rsidx_{a} seed d : CombLFP P seed d -> norm 5(read_signal d {a}%nat)=norm 5(read_signal d {b}%nat).',
                  f'Proof. intro HL. rewrite(n_{a} seed d HL). rewrite(n_{b} seed d HL). reflexivity. Qed.'])
        names.append(f'rsidx_{a}')
    hdr = (f'(** bzeeno: operand register-index wires of the RF read ports (tools/cpu_tmpl_bztrans.py fwdin). proof_author: {AUTHOR}; external_llm_api_calls=0. *)\n' +
           E.HDR.replace('@AST@', pr['ast']['module']).replace('@OPEN@', pmod))
    return hdr + f'Module {module}.\n' + '\n'.join(L) + f'\nEnd {module}.\nGoal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)


if __name__ == '__main__':
    what = sys.argv[1]
    if what == 'fwdin':
        Path(sys.argv[2]).write_text(fwdin())
    if what == 'disp2':
        only = sys.argv[3].split(',') if len(sys.argv) > 3 and sys.argv[3] != '-' else None
        t, ex = disp2(only, admit_cover=(len(sys.argv) > 4 and sys.argv[4] == 'admit'))
        Path(sys.argv[2]).write_text(t)
        print(sys.argv[2], len(t.splitlines()), len(ex))
