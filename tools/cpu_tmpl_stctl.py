#!/usr/bin/env python3
"""Steel controls and datapath per ISA class (template route): generic fast engine (ExtendedSVFast4 shared4_sound) for the
constant wires + ExtendedSVSymAliasNba.eqchain2_out for the data equations (Bzeeno Session machinery, tools/cpu_tmpl_bzex.py).
Untrusted generator; Coq re-checks.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import os
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_tmpl_stex as S
import cpu_tmpl_stcase as C
import cpu_tmpl_bzex as B
import cpu_tmpl_symexec as X

JUMPFAM = ('Jal', 'Jalr', 'Beq', 'Bne', 'Blt', 'Bge', 'Bltu', 'Bgeu')
CTRL = [203, 170, 234, 265, 268, 256, 244, 330, 25, 29, 6, 235, 3, 16, 215, 21, 31, 33, 35, 37]
DATA = [243, 223, 277, 23, 17, 18]


def pv(e, M):
    """3-valued evaluation with absorbing AND/OR/ECond (slice right-hand sides only)."""
    k = e[0]
    if k == 'EConst':
        return e[2] & ((1 << e[1]) - 1)
    if k == 'EVar':
        return M.get(e[2])
    if k == 'ESel':
        v, l = pv(e[2], M), pv(e[3], M)
        return None if v is None or l is None else (v >> l) & ((1 << e[1]) - 1)
    if k == 'EUnary':
        v = pv(e[3], M)
        if v is None:
            return None
        return ((~v) if e[2] == 'UNot' else int(v != 0)) & ((1 << e[1]) - 1)
    if k == 'EBinary':
        a, b = pv(e[3], M), pv(e[4], M)
        if e[2] == 'BAnd' and (a == 0 or b == 0):
            return 0
        if e[2] == 'BOr' and e[1] == 1 and (a == 1 or b == 1):
            return 1
        if a is None or b is None:
            return None
        return {'BAnd': a & b, 'BOr': a | b}[e[2]] & ((1 << e[1]) - 1)
    raise ValueError(k)


def scenario(name):
    """staged constants of class `name`: returns (facts1 consts, M1, slice_info, facts3 consts, M3)"""
    P = C.planner()
    c1 = C.class_consts(name)
    if name in JUMPFAM and not os.environ.get('STNOMIS'):
        c1 = c1 + [(238, 0)]
    M1 = C.oracle({name: c1})[name]
    sl = []
    v161 = 0
    for k in P.writers[161]:
        b = P.body(k)
        off, w = b[3][3][2], b[3][1]
        z = pv(b[2], M1)
        if z is None:
            sl = None
            break
        sl.append((k, off, w, b[2], z))
        v161 |= z << off
    if sl is None:
        return c1, M1, [], c1, M1
    c3 = c1 + [(161, v161)]
    M3 = C.oracle({name: c3})[name]
    return c1, M1, sl, c3, M3


class Sess(B.Session):
    def __init__(self, P, spec, M3):
        super().__init__(P, spec)
        for r, v in M3.items():
            self.F[('EVar', P.width_of(r), r)] = v

    def ensure_const(self, root, width):
        e = ('EVar', width, root)
        if e in self.F:
            return self.F[e]
        raise B.NoPlan(f'undecided root {root}')


def plan(name, targets, datas=((217, 'w'), (258, 'a'), (259, 'b'), (253, 'pc'))):
    P = C.planner()
    c1, M1, sl, c3, M3 = scenario(name)
    spec = B.Spec(name, [], list(datas), [(t, 'x') for t in targets])
    S_ = Sess(P, spec, M3)
    S_.plan()
    return S_, M3


if __name__ == '__main__':
    P = C.planner()
    for n in sys.argv[1:]:
        S_, M3 = plan(n, [243, 223, 277, 17, 18, 23])
        print('==', n, 'eqs', len(S_.eq), 'ks', S_.ksE)
        for (w, r) in S_.order:
            print('  ', r, P.ast.sig[r]['path'].split('.')[-1], w, S_.eq[(w, r)])


# ---------------------------------------------------------------- Coq emission
def zl(v):
    return f'({v})' if v < 0 else str(v)


def ex(e):
    import cpu_tmpl_ast as T
    return T.coq(e)


def reads_of(P, k):
    acc = set()

    def go(s):
        if s[0] == 'SAssign':
            acc.update(r for _, r in X.inputs(s[2]))
            lv = s[3]
            while lv[0] == 'LSel':
                acc.update(r for _, r in X.inputs(lv[3]))
                lv = lv[2]
        elif s[0] == 'SSeq':
            for c in s[1]:
                go(c)
        elif s[0] == 'SIf':
            acc.update(r for _, r in X.inputs(s[1]))
            go(s[2]); go(s[3])
        elif s[0] == 'SCase':
            acc.update(r for _, r in X.inputs(s[1]))
            for key, b in s[2]:
                if key is not None:
                    acc.update(r for _, r in X.inputs(key))
                go(b)
    go(P.body(k))
    return acc


def sh(n, l, r):
    return f'(Z.shiftr {n} {l})'


def class_targets(name):
    """(root, width, rhs) data conclusions of class `name` on the variables w a b imm pc."""
    c = C.classes()[name]
    clr0 = lambda y: f'Z.shiftl (Z.shiftr (norm 32 {y}) 1) 1'
    out = [(223, 5, 'norm 5 (Z.shiftr w 7)')]
    kind = c['kind']
    bvar = 'imm' if c['operand_b'] == 'imm' else 'b'
    if kind == 'dataop':
        out.append((243, 32, 'norm 32 (Z.add pc 4)'))
        out.append((277, 32, 'norm 32 (' + c['value'].replace(' b', ' ' + bvar).replace('(b)', '(' + bvar + ')') + ')' if name != 'Lui' else 'norm 32 imm'))
    elif kind == 'jal':
        out.append((243, 32, 'norm 32 (' + clr0('(Z.add pc imm)') + ')'))
        out.append((277, 32, 'norm 32 (Z.add pc 4)'))
    elif kind == 'jalr':
        out.append((243, 32, 'norm 32 (' + clr0('(Z.add a imm)') + ')'))
        out.append((277, 32, 'norm 32 (Z.add pc 4)'))
    else:
        cond = c['cond']
        out.append((243, 32, f'norm 32 (if {cond} then ({clr0("(Z.add pc imm)")}) else (Z.add pc 4))'))
    N = [r for rr, ww, r in out if rr == 243][0]
    nn = N[len('norm 32 '):]
    out.append((23, 32, N))
    out.append((18, 7, f'norm 7 (Z.shiftr (norm 32 {nn}) 2)'))
    out.append((17, 1, f'boolz (negb (Z.ltb (norm 32 {nn}) 512))'))
    return out


PREAMBLE = r'''From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVSymExec Lang.ExtendedSVFactChain Lang.ExtendedSVSymAlias Lang.ExtendedSVSymAliasNba
 Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecOverlay Lang.ExtendedSVBackward Lang.ExtendedSVEval3 Lang.ExtendedSVSymExecFast Lang.ExtendedSVFastCond
 Lang.ExtendedSVEval4 Lang.ExtendedSVFast4 Lang.ExtendedSVSliceBits Lang.ExtendedSVSliceExec Lang.ExtendedSVSliceRootFact
 Lang.ExtendedSVAssignment Lang.ExtendedSVWordInvariant Ex.External.CPUImmediateShapes Ex.External.CPUImmediateRtlShapes
 Ex.External.CPUDatapathFacts Lang.ExtendedSVBankAlignment Ex.External.CPUSubSign33 Steel.SteelAST.
Import ListNotations ExtendedSV ExtendedSVSymExec ExtendedSVFactChain ExtendedSVSymAlias ExtendedSVSymAliasNba ExtendedSVSymExecSym ExtendedSVSymExecOverlay
 ExtendedSVBackward ExtendedSVEval3 ExtendedSVSymExecFast ExtendedSVFastCond ExtendedSVEval4 ExtendedSVFast4 ExtendedSVSliceBits ExtendedSVSliceExec
 ExtendedSVSliceRootFact ExtendedSVAssignment ExtendedSVWordInvariant CPUImmediateShapes CPUImmediateRtlShapes CPUDatapathFacts ExtendedSVBankAlignment CPUSubSign33.
Local Open Scope Z_scope.
Definition P:=SteelAST.steel_program.
Lemma norm_boolz w b : (1 <= w)%nat -> norm w (boolz b) = boolz b.
Proof. intro H. assert (E : 2 ^ 1 <= 2 ^ Z.of_nat w) by (apply Z.pow_le_mono_r; lia). destruct b; cbn [boolz]; rewrite norm_mod; apply Z.mod_small; split; lia. Qed.
Lemma norm32_range a : norm 32 a = a -> 0 <= a < 2 ^ 32.
Proof. intro H. pose proof (norm_mod 32 a) as E. rewrite H in E. pose proof (Z.mod_pos_bound a (2 ^ Z.of_nat 32) ltac:(apply Z.pow_pos_nonneg; lia)). cbn [Z.of_nat Pos.of_succ_nat] in *. rewrite <- E in H0. exact H0. Qed.
Lemma slt_eq a b : norm 32 a = a -> norm 32 b = b ->
 norm 1 (if norm 1 (Z.lxor (norm 1 (Z.shiftr a 31)) (norm 1 (Z.shiftr b 31))) =? 0 then boolz (a <? b) else norm 1 (Z.shiftr a 31))
 = boolz (signed_value 32 a <? signed_value 32 b).
Proof.
 intros Ha Hb. pose proof (norm32_range a Ha) as Ra. pose proof (norm32_range b Hb) as Rb.
 rewrite !n1 by assumption. unfold signed_value.
 change (32 =? 0)%nat with false. change (Z.of_nat (Nat.pred 32)) with 31. rewrite Ha, Hb. cbv iota.
 destruct (Z.testbit a 31) eqn:Ta; destruct (Z.testbit b 31) eqn:Tb.
 all: first [ pose proof (proj1 (tb31 a Ra) Ta) | assert (a < 2 ^ 31) by (destruct (Z_lt_ge_dec a (2 ^ 31)); [assumption|exfalso; assert (X: Z.testbit a 31 = true) by (apply tb31; lia); congruence]) ].
 all: first [ pose proof (proj1 (tb31 b Rb) Tb) | assert (b < 2 ^ 31) by (destruct (Z_lt_ge_dec b (2 ^ 31)); [assumption|exfalso; assert (X: Z.testbit b 31 = true) by (apply tb31; lia); congruence]) ].
 all: repeat match goal with |- context [?x <? ?y] => let E := fresh "E" in destruct (x <? y) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E] end.
 all: first [ reflexivity | (exfalso; lia) ].
Qed.
Ltac cclose := repeat match goal with
 | |- context [(norm ?w ?x =? 0)] => let v := eval vm_compute in (norm w x =? 0) in
     match v with true => change (norm w x =? 0) with true | false => change (norm w x =? 0) with false end end; cbv iota.
Lemma inv_addr2 x : norm 1 (if boolz (x <? 512) =? 0 then 1 else 0) = boolz (negb (x <? 512)).
Proof. destruct (x <? 512); vm_compute; reflexivity. Qed.
Lemma rep12 x : norm 12 (replicate_bits 20 1 (norm 1 x)) = norm 12 (replicate_bits 12 1 (norm 1 x)).
Proof.
 assert (H: norm 1 x = 0 \/ norm 1 x = 1) by (rewrite norm_mod; change (2 ^ Z.of_nat 1) with 2; pose proof (Z.mod_pos_bound x 2 ltac:(lia)); lia).
 destruct H as [H|H]; rewrite H; [rewrite !replicate_zero | rewrite !replicate_ones; vm_compute]; reflexivity.
Qed.
Definition mem_out (t:(signal*nat)*Z) (l:list((signal*nat)*Z)) : bool :=
 existsb (fun u => Nat.eqb (fst (fst t)) (fst (fst u)) && Nat.eqb (snd (fst t)) (snd (fst u)) && Z.eqb (snd t) (snd u)) l.
Lemma decout_sub s l want : DecOut s l -> forallb (fun t => mem_out t l) want = true -> DecOut s want.
Proof.
 intros H HW t Ht. rewrite forallb_forall in HW. specialize (HW t Ht). unfold mem_out in HW. rewrite existsb_exists in HW.
 destruct HW as [u [Hu Hb]]. apply andb_true_iff in Hb as [Hb1 Hb2]. apply andb_true_iff in Hb1 as [Hb1 Hb3].
 apply Nat.eqb_eq in Hb1. apply Nat.eqb_eq in Hb3. apply Z.eqb_eq in Hb2. destruct t as [[r w] z], u as [[r' w'] z']. cbn in *. subst. exact (H _ Hu).
Qed.
Ltac pick_in := repeat first [apply in_eq | apply in_cons].
Ltac cnorm := repeat match goal with
 | |- context [norm ?w (Zpos ?p)] => let v := eval cbv in (norm w (Zpos p)) in change (norm w (Zpos p)) with v
 | |- context [norm ?w Z0] => let v := eval cbv in (norm w Z0) in change (norm w Z0) with v end.
'''
IMMPRE = r'''
From Coq Require Import Lia.
Require Import coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise riscv.Utility.Utility.
Lemma eval_rep d w c b : eval_expr d (EReplicate w c b) = norm w (replicate_bits c (expr_width b) (eval_expr d b)). Proof. reflexivity. Qed.
Lemma eval_sel d w b l : eval_expr d (ESel w b l) = norm w (Z.shiftr (eval_expr d b) (eval_expr d l)). Proof. reflexivity. Qed.
Lemma eval_var d w x : eval_expr d (EVar w x) = norm w (read_signal d x). Proof. reflexivity. Qed.
Lemma eval_const d w v : eval_expr d (EConst w v) = norm w v. Proof. reflexivity. Qed.
Lemma ew_sel w b l : expr_width (ESel w b l) = w. Proof. reflexivity. Qed.
Ltac immclose c := repeat rewrite norm_ones; repeat rewrite rep_sign;
 try (match goal with |- context [Z.testbit c 31] => destruct (Z.testbit c 31) eqn:Tsign end);
 repeat match goal with |- context [Z.of_nat ?n] => let m := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with m end.
Lemma sgnW (n : nat) (v X w : Z) : (n <= 20)%nat -> norm 32 X = w ->
 norm n v = norm n (norm n (replicate_bits 20 1 (norm 1 (Z.shiftr (norm 32 X) (norm 5 31))))) ->
 norm n v = if Z.testbit w 31 then Z.ones (Z.of_nat n) else 0.
Proof.
 intros Hn H1 H2. rewrite H2, H1. rewrite norm_idempotent.
 change (norm 5 31) with 31. rewrite (norm_ones 1 (Z.shiftr w 31)). change (Z.of_nat 1) with 1.
 rewrite (sign_val w (Z.testbit w 31) eq_refl). destruct (Z.testbit w 31).
 - rewrite replicate_ones. rewrite norm_ones. apply Z.bits_inj'. intros k Hk.
   rewrite Z.land_spec, !Z.testbit_ones_nonneg by lia.
   destruct (Z.ltb_spec0 k (Z.of_nat n)); destruct (Z.ltb_spec0 k (Z.of_nat 20)); try reflexivity; lia.
 - rewrite replicate_zero. rewrite norm_ones. apply Z.land_0_l.
Qed.
Lemma rep_ite w : norm 20 (replicate_bits 20 1 (norm 1 (Z.shiftr w 31))) = if Z.testbit w 31 then Z.ones (Z.of_nat 20) else 0.
Proof.
 rewrite (norm_ones 1 (Z.shiftr w 31)). change (Z.of_nat 1) with 1.
 rewrite (sign_val w (Z.testbit w 31) eq_refl). destruct (Z.testbit w 31).
 - rewrite replicate_ones. rewrite norm_ones. apply Z.land_diag.
 - rewrite replicate_zero. rewrite norm_ones. apply Z.land_0_l.
Qed.
Lemma rep_ite12 w : norm 12 (replicate_bits 20 1 (norm 1 (Z.shiftr w 31))) = norm 12 (if Z.testbit w 31 then Z.ones (Z.of_nat 20) else 0).
Proof. rewrite <- rep_ite. rewrite norm_low by lia. reflexivity. Qed.
Lemma immI_form w : norm 32 (Z.lor (Z.shiftl (norm 20 (replicate_bits 20 1 (norm 1 (Z.shiftr w 31)))) (Z.of_nat 12)) (norm 12 (Z.shiftr w 20))) = norm 32 (isa_imm_I w).
Proof. unfold isa_imm_I. immclose w. all: finish_imm. Qed.
Lemma immU_form w : norm 32 (Z.lor (Z.shiftl (norm 20 (Z.shiftr w 12)) (Z.of_nat 12)) 0) = norm 32 (isa_imm_U w).
Proof. unfold isa_imm_U. repeat rewrite norm_ones. repeat match goal with |- context [Z.of_nat ?n] => let m := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with m end. prove_Zeq_bitwise. Qed.
Lemma immB_form w : norm 32 (Z.lor (Z.shiftl (norm 20 (replicate_bits 20 1 (norm 1 (Z.shiftr w 31)))) (Z.of_nat 12))
 (norm 12 (Z.lor (Z.shiftl (norm 1 (Z.shiftr w 7)) (Z.of_nat 11)) (norm 11 (Z.lor (Z.shiftl (norm 6 (Z.shiftr w 25)) (Z.of_nat 5))
 (norm 5 (Z.lor (Z.shiftl (norm 4 (Z.shiftr w 8)) (Z.of_nat 1)) 0))))))) = norm 32 (isa_imm_B w).
Proof. unfold isa_imm_B. immclose w. all: finish_imm. all: (replace (i - 12 + 31) with 31 by lia; rewrite Tsign; reflexivity). Qed.
Lemma immJ_form w : norm 32 (Z.lor (Z.shiftl (norm 12 (replicate_bits 20 1 (norm 1 (Z.shiftr w 31)))) (Z.of_nat 20))
 (norm 20 (Z.lor (Z.shiftl (norm 8 (Z.shiftr w 12)) (Z.of_nat 12)) (norm 12 (Z.lor (Z.shiftl (norm 1 (Z.shiftr w 20)) (Z.of_nat 11))
 (norm 11 (Z.lor (Z.shiftl (norm 10 (Z.shiftr w 21)) (Z.of_nat 1)) 0))))))) = norm 32 (isa_imm_J w).
Proof. rewrite rep12. unfold isa_imm_J. immclose w. all: finish_imm. all: (replace (i - 20 + 31) with 31 by lia; rewrite Tsign; reflexivity). Qed.
Lemma immI_form2 w : norm 32 (Z.lor (Z.shiftl (if Z.testbit w 31 then Z.ones (Z.of_nat 20) else 0) (Z.of_nat 12)) (norm 12 (Z.shiftr w 20))) = norm 32 (isa_imm_I w).
Proof. rewrite <- rep_ite. exact (immI_form w). Qed.
Lemma immB_form2 w : norm 32 (Z.lor (Z.shiftl (if Z.testbit w 31 then Z.ones (Z.of_nat 20) else 0) (Z.of_nat 12))
 (norm 12 (Z.lor (Z.shiftl (norm 1 (Z.shiftr w 7)) (Z.of_nat 11)) (norm 11 (Z.lor (Z.shiftl (norm 6 (Z.shiftr w 25)) (Z.of_nat 5))
 (norm 5 (Z.lor (Z.shiftl (norm 4 (Z.shiftr w 8)) (Z.of_nat 1)) 0))))))) = norm 32 (isa_imm_B w).
Proof. rewrite <- rep_ite. exact (immB_form w). Qed.
Lemma immJ_form2 w : norm 32 (Z.lor (Z.shiftl (norm 12 (if Z.testbit w 31 then Z.ones (Z.of_nat 20) else 0)) (Z.of_nat 20))
 (norm 20 (Z.lor (Z.shiftl (norm 8 (Z.shiftr w 12)) (Z.of_nat 12)) (norm 12 (Z.lor (Z.shiftl (norm 1 (Z.shiftr w 20)) (Z.of_nat 11))
 (norm 11 (Z.lor (Z.shiftl (norm 10 (Z.shiftr w 21)) (Z.of_nat 1)) 0))))))) = norm 32 (isa_imm_J w).
Proof. rewrite <- rep_ite12. exact (immJ_form w). Qed.
'''

DATAS = ((217, 'w'), (258, 'a'), (259, 'b'), (253, 'pc'), (205, 'imm'))


def facts_lit(P, items):
    return '[' + '; '.join(f'({ex(("EVar", P.width_of(r), r))}, {zl(v)})' for r, v in items) + ']'


def outs_lit(P, items):
    return '[' + '; '.join(f'(({r}%nat,{P.width_of(r)}%nat),{zl(v)})' for r, v in items) + ']'


# operand roots of the Steel ALU (rs1 data 258; second operand 157 = alu_2nd_operand, 259 = rs2 data, 205 = immediate)
A_OPS, B_OPS = {258}, {157, 259, 205}
COMMS = {'BAdd': ('?x + ?y', 'Z.add_comm'), 'BAnd': ('Z.land ?x ?y', 'Z.land_comm'), 'BOr': ('Z.lor ?x ?y', 'Z.lor_comm'),
         'BXor': ('Z.lxor ?x ?y', 'Z.lxor_comm'), 'BMul': ('?x * ?y', 'Z.mul_comm')}


def commuted_ops(exprs):
    """commutative operators whose second-operand side is written left of the rs1 operand (tmpl-econd-casesplit)"""
    out = []

    def go(e):
        if e[0] == 'EBinary' and e[2] in COMMS:
            l, r = {x for _, x in X.inputs(e[3])}, {x for _, x in X.inputs(e[4])}
            if l & B_OPS and r & A_OPS and not l & A_OPS and e[2] not in out:
                out.append(e[2])
        for c in e[1:]:
            if isinstance(c, tuple) and c and isinstance(c[0], str) and c[0].startswith('E'):
                go(c)
    for e in exprs:
        go(e)
    return out


def class_block(name, closer='', tg_=None, datas_=None, suffix='ctl', ctl_roots=None, extra_pre=(), consts_extra=(), rw_subst=None):
    """definitions + theorem for one class; returns (defs, thm, cases entries, info)"""
    P = C.planner()
    c1, M1, sl, c3, M3 = scenario(name)
    n = name
    tg = tg_ if tg_ is not None else class_targets(name)
    has161 = len(c3) > len(c1)
    datas = list(datas_ if datas_ is not None else DATAS)
    spec = B.Spec(name, [], datas, [(r, 'x') for r, w, e in tg])
    S_ = Sess(P, spec, M3)
    S_.plan()
    # facts
    o1 = sorted((r, v) for r, v in M1.items() if any(r == x for k, off, w, e, z in sl for _, x in X.inputs(e)))
    o3 = sorted(M3.items())
    f3items = c3
    FB = [(('EVar', P.width_of(r), r), r) for r, v in f3items] + [(('EVar', P.width_of(r), r), r) for r, v in o3]
    L = []
    L.append(f'Definition f1_{n}:Facts:={facts_lit(P, c1)}.')
    L.append(f'Definition o1_{n}:list((signal*nat)*Z):={outs_lit(P, o1)}.')
    L.append(f'Definition cf1_{n}:CaseF:=mkCaseF f1_{n} sc0 o1_{n} [].')
    L.append(f'Definition f3_{n}:Facts:={facts_lit(P, c3)}.')
    L.append(f'Definition o3_{n}:list((signal*nat)*Z):={outs_lit(P, o3)}.')
    L.append(f'Definition cf3_{n}:CaseF:=mkCaseF f3_{n} sc0 o3_{n} [].')
    ks = []
    for k in S_.ksE:
        rd_ = reads_of(P, k)
        idx = [i for i, (e, r) in enumerate(FB) if r in rd_]
        ks.append(f'({k}%nat,[' + ';'.join(f'{i}%nat' for i in idx) + '])')
    L.append(f'Definition ksE_{n}:list(nat*list nat):=[' + '; '.join(ks) + '].')
    L.append(f'Definition eqs_{n}:list Eqn:=[' + '; '.join(B.coq_eqn(w, r, S_.eq[(w, r)]) for (w, r) in S_.order) + '].')
    # theorem
    cvars = 'w a b imm pc'
    hyps = [f'norm {P.width_of(r)} (read_signal d {r}%nat) = {zl(v)}' for r, v in c1]
    hyps += [f'norm {P.width_of(r)} (read_signal d {r}%nat) = {v}' for r, v in datas]
    ctl = [(r, M3[r]) for r in (CTRL if ctl_roots is None else ctl_roots) if r in M3]
    L.append(f'Definition ctl_{n}:list((signal*nat)*Z):={outs_lit(P, ctl)}.')
    leaves = [(r, M3[r]) for (w, r) in S_.leaves if r in M3]
    L.append(f'Definition leaves_{n}:list((signal*nat)*Z):={outs_lit(P, leaves)}.')
    concl = [f'DecOut d ctl_{n}']
    concl += [f'norm {W} (read_signal d {r}%nat) = {rhs}' for r, W, rhs in tg]
    L.append(f'Theorem {n}_{suffix} seed d ({cvars}:Z) : CombLFP P seed d -> ' + ''.join(f'{h} -> ' for h in hyps) + ' /\\ '.join(concl) + '.')
    pf = ['Proof. intros HL ' + ' '.join(f'hc{i}' for i in range(len(c1))) + ' ' + ' '.join(f'hd{i}' for i in range(len(datas))) + '.']
    pf.append(f' assert (HF1 : FactsHold d f1_{n}) by (intros e z HI; cbn in HI; repeat (destruct HI as [HI|HI]; [inversion HI; subst; first [assumption|(cbn [eval_expr]; assumption)]|]); contradiction).')
    pf.append(f' destruct (shared4_sound P comb_ps wtab (mkShared [] []) cases seed d cf1_{n} eq_refl wtab_okb HL cases_ok ltac:(cbn [cases]; pick_in) (fun e z H => match H with end) HF1) as [_ [HO1 _]].')
    pf.append(f' pose proof (facts_app d _ _ HF1 (decout_facts d o1_{n} HO1)) as HF1b.')
    if has161:
        k1, k2 = sl[0], sl[1]
        # want entries
        want = '[' + '; '.join(f'(161%nat,{off},{w}%nat,{ex(e)})' for k, off, w, e, z in sl) + ']'
        pf.append(f' pose proof (slchain_out P comb_ps wtab [(92%nat,[]);(93%nat,[])] (f1_{n} ++ outs_facts o1_{n}) {want} seed d eq_refl wtab_ok HF1b HL ltac:(vm_compute; reflexivity)) as SH.')
        pf.append(f' pose proof (slice_root_fact d 161%nat 3 1 {ex(sl[0][3])} {ex(sl[1][3])} {sl[0][4]} {sl[1][4]} {M3[161]} (SH _ _ _ _ (or_introl eq_refl)) (SH _ _ _ _ (or_intror (or_introl eq_refl)))'
                  f' (xeval4_sound _ d HF1b {ex(sl[0][3])} {sl[0][4]} ltac:(vm_compute; reflexivity)) (xeval4_sound _ d HF1b {ex(sl[1][3])} {sl[1][4]} ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity)) as HF161.')
        pf.append(f' pose proof (facts_app d _ _ HF1 HF161) as HF3.')
    else:
        pf.append(f' pose proof HF1 as HF3.')
    pf.append(f' destruct (shared4_sound P comb_ps wtab (mkShared [] []) cases seed d cf3_{n} eq_refl wtab_okb HL cases_ok ltac:(cbn [cases]; pick_in) (fun e z H => match H with end) HF3) as [_ [HO3 _]].')
    pf.append(f' pose proof (facts_app d _ _ HF3 (decout_facts d o3_{n} HO3)) as HF4.')
    pf.append(f' destruct (eqchain2_out P comb_ps wtab ksE_{n} (f3_{n} ++ outs_facts o3_{n}) [] eqs_{n} seed d eq_refl wtab_ok HF4 HL ltac:(vm_compute; reflexivity)) as [_ HE].')
    for (w, r) in S_.order:
        if suffix == 'imm' and r == 211:      # kernel trap: `cbn` on an EReplicate equation makes every later use hang in the kernel; unfold by rewriting with eq_refl lemmas instead
            pf.append(f' pose proof (HE {w}%nat {r}%nat _ ltac:(pick_in)) as E{r}; rewrite eval_rep, eval_sel, eval_var, eval_const, ew_sel in E{r}.')
        else:
            pf.append(f' pose proof (HE {w}%nat {r}%nat _ ltac:(pick_in)) as E{r}; cbn [eval_expr expr_width] in E{r}.')
    cs = [(r, P.width_of(r), M3[r]) for (w, r) in S_.leaves if r in M3]
    pf.append(f' pose proof (decout_sub d _ leaves_{n} HO3 ltac:(vm_compute; reflexivity)) as HOL.')
    for r, w, z in cs:
        pf.append(f' pose proof (HOL (({r}%nat,{w}%nat),{zl(z)}) ltac:(pick_in)) as C{r}; cbn [fst snd] in C{r}.')
    for i, (r, v) in enumerate(datas):
        W = P.width_of(r)
        pf.append(f' assert (Hn{i} : norm {W} {v} = {v}) by (rewrite <- hd{i}; apply norm_idempotent).')
        pf.append(f' assert (Hm{i} : norm {W + 1} {v} = {v}) by (rewrite <- hd{i}; rewrite norm_wide by lia; reflexivity).')
    pf.append(f' refine (conj (decout_sub d _ ctl_{n} HO3 ltac:(vm_compute; reflexivity)) ?[Rest]).')
    pf.append(' [Rest]: {')
    hn = []
    for i, (r, v) in enumerate(datas):
        hn += [f'rewrite Hn{i}', f'rewrite Hm{i}']
    HN = ' | '.join(hn + ['rewrite norm_lo by lia', 'rewrite norm_wide by lia', 'rewrite Z.add_0_r', 'rewrite Z.shiftr_0_r', 'rewrite Z.gtb_ltb', 'rewrite norm_one_boolz', 'rewrite norm_boolz by lia', 'rewrite rtl_clear0', 'rewrite norm_add_r', 'rewrite Z.add_opp_r', 'rewrite inv_addr2'])
    dleaves = [f'hd{i}' for i, (r, v) in enumerate(datas) if (P.width_of(r), r) in S_.leaves]
    rw = [(rw_subst or {}).get(r, f'E{r}') for (w, r) in S_.order] + [f'C{r}' for r, w, z in cs] + dleaves
    for x in extra_pre:
        pf.append(' ' + x)
    pf.append(' rewrite ' + ', '.join(rw) + '.')
    pf.append(' cnorm. repeat apply conj.')
    AC = ' | '.join(f'(rewrite (Z.add_comm {x} {y}); reflexivity)' for x, y in (('4','pc'), ('imm','pc'), ('imm','a'), ('pc','imm'), ('a','imm'), ('b','a'), ('a','b')))
    cm = commuted_ops([S_.eq[k] for k in S_.order])
    if cm:   # tmpl-econd-casesplit: operands of a commutative operator in the other order than the ISA (rs1 first) -> commutativity retry
        AC += ' | ' + ' | '.join(f'(match goal with |- context [{COMMS[o][0]}] => rewrite ({COMMS[o][1]} x y); reflexivity end)' for o in cm)
    import os
    cl = ' all: (cnorm; repeat first [' + HN + ' | reflexivity]; try (first [exact (slt_eq a b Hn1 Hn2) | exact (slt_eq a imm Hn1 Hn4) | ' + AC + '])).' if not closer else closer
    if not closer and C.classes()[n]['kind'] == 'branch':
        cond = C.classes()[n]['cond']
        if cond.startswith('negb '):
            cond = cond[5:]
        lp = '(cnorm; repeat first [' + HN + ' | reflexivity])'
        cl = (' all: (cnorm; repeat first [' + HN + ' | reflexivity]; try (rewrite (slt_eq a b Hn1 Hn2)); destruct (' + cond + ') eqn:Hc; cbn [boolz negb Z.lnot]; cclose; '
              + lp + '; try (first [' + AC + ']); try reflexivity).')
    if os.environ.get('STSCRATCH') == '1':
        cl = ' all: first [ solve [ ' + cl.strip()[len('all:'):].strip().rstrip('.') + ' ] | (idtac "FAILGOAL ' + n + '"; match goal with |- ?g => idtac g end; admit) ].'
    if S_.opaque:
        # opaque ECond guards (tools/cpu_tmpl_bzex.Session.need_guard): case-split on every guard test that reads an opaque
        # root right after the rewrites; the normalisation and the closer run unchanged on each branch
        assert pf[-1] == ' cnorm. repeat apply conj.'
        pf[-1] = ' ' + B.opaque_split([r for _, r in S_.opaque]) + '; cnorm; repeat apply conj; ' + B.sentences_to_tactic(cl) + '.'
    else:
        pf.append(cl)
    if os.environ.get('STSHOW') == '1':
        pf.append(' all: (match goal with |- ?g => idtac "GOALSHOW" g end).')
    pf.append(' }' )
    pf.append('Admitted.' if os.environ.get('STSCRATCH') == '1' else 'Qed.')
    info = dict(eqs=len(S_.eq), ksE=len(S_.ksE), consts=len(o3), has161=has161)
    if S_.opaque:
        info['opaque_guard_roots'] = {r: S_.opaque_why[r] for _, r in S_.opaque}
    return '\n'.join(L + pf), info


def module_text(module, names, closers=None, suffix='ctl', block_args=None, title='controls and datapath per ISA class', extra_pre=''):
    P = C.planner()
    nc = len(P.ast.comb_ids)
    body = [C.wtab_text(P), 'Definition comb_ps:=filter is_comb (processes P).',
            'Lemma wtab_okb : tab_okb comb_ps wtab = true. Proof. vm_compute; reflexivity. Qed.',
            'Lemma wtab_ok : TabC comb_ps wtab. Proof. apply tab_okb_sound, wtab_okb. Qed.',
            f'Definition sc0:Script:={C.script_text(P)}.']
    blocks, infos = [], {}
    for n in names:
        ba = {'closer': (closers or {}).get(n, ''), 'suffix': suffix}
        ba.update(block_args(n) if block_args else {})
        t, i = class_block(n, **ba)
        blocks.append(t)
        infos[n] = i
    cases = '[' + '; '.join(f'cf1_{n}; cf3_{n}' for n in names) + ']'
    # definitions first (cases need them), theorems after: split each block at "Theorem"
    defs = [b.split('\nTheorem ')[0] for b in blocks]
    thms = ['Theorem ' + b.split('\nTheorem ')[1] for b in blocks]
    body += defs
    body.append(f'Definition cases:list CaseF:={cases}.')
    body.append('Lemma cases_ok : check_shared4 comb_ps wtab (statement_fuel P) (mkShared [] []) cases = true. Proof. vm_compute; reflexivity. Qed.')
    body += thms
    exports = [f'{module}.{n}_{suffix}' for n in names]
    text = (f'(** Steel: ' + title + ' (tools/cpu_tmpl_stctl.py). proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)\n'
            + PREAMBLE + extra_pre + f'Module {module}.\n' + '\n'.join(body) + f'\nEnd {module}.\n' + ''.join(f'Print Assumptions {e}.\n' for e in exports))
    return text, infos, exports


# ---------------------------------------------------------------- immediates (module SteelTmplImm)
IMMTYPE = {'OPIMM': 'I', 'JALR': 'I', 'LUI': 'U', 'AUIPC': 'U', 'JAL': 'J', 'BRANCH': 'B'}


def imm_args(name):
    c = C.classes()[name]
    t = IMMTYPE[c['group']]
    form = {'I': 'immI_form2', 'B': 'immB_form2', 'U': 'immU_form', 'J': 'immJ_form2'}[t]
    sign = t != 'U'
    return dict(tg_=[(205, 32, f'norm 32 (isa_imm_{t} w)')], datas_=[(217, 'w')], suffix='imm', ctl_roots=[],
                extra_pre=([' pose proof (sgnW 20 _ _ w ltac:(lia) hd0 E211) as S211.'] if sign else []), rw_subst=({211: 'S211'} if sign else None),
                closer=' all: (cnorm; repeat first [rewrite Hn0 | rewrite Hm0 | rewrite norm_lo by lia | rewrite norm_wide by lia | rewrite Z.shiftr_0_r]; ' + ('SHOWFINAL' if False else '') + 'exact (' + form + ' w)).')


# ---------------------------------------------------------------- misaligned-target facts (module SteelTmplMis)
def mis_args(name):
    """`misaligned_instruction_address` (238 = take_branch & next_address[1]) as a function of the data, WITHOUT the premise 238 = 0."""
    c = C.classes()[name]
    kind = c['kind']
    if kind == 'jal':
        rhs = 'norm 1 (Z.shiftr (norm 32 (Z.add pc imm)) 1)'
    elif kind == 'jalr':
        rhs = 'norm 1 (Z.shiftr (norm 32 (Z.add a imm)) 1)'
    else:
        full = c['cond']          # the take-branch condition as written (negb kept: Bne/Bge/Bgeu take the branch when the compare is false)
        cond = full[5:] if full.startswith('negb ') else full    # the compare the closer case-splits on
        rhs = f'(if {full} then norm 1 (Z.shiftr (norm 32 (Z.add pc imm)) 1) else 0)'
    if kind in ('jal', 'jalr'):
        closer = ' all: (cnorm; misfin).'
    else:
        hn = ' | '.join(f'rewrite Hn{i} | rewrite Hm{i}' for i in range(5))
        closer = (' all: (cnorm; repeat first [' + hn + ' | rewrite norm_lo by lia | rewrite norm_wide by lia | rewrite Z.shiftr_0_r | rewrite Z.gtb_ltb | rewrite norm_one_boolz | rewrite norm_boolz by lia | rewrite inv_addr2]; '
                  'try (rewrite (slt_eq a b Hn1 Hn2)); destruct (' + cond + ') eqn:Hc; cbn [boolz negb Z.lnot]; cclose; misfin).')
    return dict(tg_=[(238, 1, rhs)], suffix='mis', ctl_roots=[], closer=closer)


MISPRE = r'''
From Coq Require Import Lia.
Require Import coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise.
Ltac misfin := repeat rewrite norm_ones; repeat match goal with |- context [Z.of_nat ?n] => let m := eval cbv in (Z.of_nat n) in change (Z.of_nat n) with m end;
 prove_Zeq_bitwise; try (match goal with Hi : 0 <= ?i, H : ?i < 1 |- _ => assert (i = 0) by lia; subst i; cbn; reflexivity end).
'''
