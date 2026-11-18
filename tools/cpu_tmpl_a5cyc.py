#!/usr/bin/env python3
"""angelo5fix cycle/value layer (S3 closure input): one whole clock cycle `actual_cycle = fall (rise s)` per register.

Emits the Coq module A5TmplCyc:
  * [Pre] (length = signal count, clock 0, reset released, net words, comb fixed point) and [pre_cycle] (Pre is a cycle invariant);
  * [cyc_R]   : Pre s -> norm W (read (actual_cycle s) R) = norm W (eval (drv s) TE_R)      (rise lemma of the accepted stage layers + fall frame);
  * wire bindings of every single-assignment combinational wire ([w_x] = checked_assignment_binding) RESOLVED in topological order
    through the earlier ones (Lang/ExtendedSVExprResolve: [b_x : norm W (read d x) = norm W (eval d r_x)], r_x reads only registers,
    inputs and outputs of the multi-statement comb processes);
  * [cycr_R]  : the same next-state value with TE_R resolved ([ter_R]); [dreg]: registers are unchanged in the driven state.
Untrusted generator; Coq checks everything.  proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0."""
import argparse, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import cpu_tmpl_ast as T

ROOT = Path(__file__).resolve().parent.parent
AUTHOR = 'LLM-generated: Claude Code (claude-opus-5-5)'
AST = ROOT / 'experiments/framework/generated/angelo5-fixed/Angelo5FixedAST.v'
REP = ROOT / 'experiments/framework/generated/angelo5-fixed/report.json'
NSIG = 438
NET = [0, 1, 18, 19, 117, 131, 132, 155, 156, 208, 209, 277, 278, 338, 339]
# register -> (provider module alias, lemma name, texpr term)
S2 = [133, 134, 136, 143, 147, 153, 159, 161, 163, 164, 165, 166, 171, 212, 214, 216, 218, 220, 222, 224, 225, 227, 230, 232, 233, 234, 235, 237,
      282, 284, 286, 288, 290, 292, 293, 294, 295, 296, 297, 298, 302, 305, 313]
S2P = {r: (4 if r < 155 else 8 if r < 172 else 9 if r < 238 else 10) for r in S2}
CSR = [358, 359, 418, 419, 420, 421, 422, 423, 356, 357, 353]
ONE = {5: 0, 6: 0, 13: 0, 14: 0, 126: 2, 127: 2}
NB = {167: 8, 168: 8, 169: 8}
# outputs kept ATOMIC (not substituted): forwarded operands, execute-stage control, CSR misalign; their values come from the per-class / context lemmas
ATOMIC = {106, 107, 228, 229, 240, 242, 271, 272, 273, 274, 410}


def regs_spec(ast):
    out = {}
    for r in S2:
        out[r] = ('S2', f'rise_{r}', f'texpr2m {ast.sig[r]["width"]}%nat {r}%nat (S2.tree_of process_{S2P[r]})')
    for r in CSR:
        out[r] = ('SC', f'rise_{r}', f'texpr2m {ast.sig[r]["width"]}%nat {r}%nat (SC.tree_of process_12)')
    for r, p in ONE.items():
        out[r] = ('S1', f'rise_{r}', f'texpr2m {ast.sig[r]["width"]}%nat {r}%nat (S1.tree1_of process_{p})')
    out[150] = ('ST', 'rise_150', 'ExtendedSVSeqTree.texpr 1%nat 150%nat (ST.tree_of process_3)')
    for r in NB:   # part-select (packed flag) registers: non-blocking symbolic executor, no facts
        out[r] = ('NBX', f'rnb_{r}', f'nbe_{r}')
    return out


HXDEPS = ROOT / 'framework/template-sources/a5hx-deps.json'


def topo(ast):
    """simple wires and the havoc outputs of the multi-statement comb processes (tools/cpu_tmpl_a5hx.py), dependency order"""
    simple = ast.comb
    hx = {int(k): v for k, v in json.loads(HXDEPS.read_text()).items()}
    deps = {x: sorted(y for (w, y) in T.evars(simple[x]['rhs'])) for x in simple}
    deps.update(hx)
    order, seen = [], set()

    def visit(x, stack):
        if x in seen:
            return
        if x in stack:
            raise SystemExit(f'comb cycle at {x}')
        stack.add(x)
        for y in deps[x]:
            if y in deps and y != x:
                visit(y, stack)
        stack.discard(x)
        seen.add(x); order.append(x)
    for x in sorted(deps):
        visit(x, set())
    return order, hx


HEAD = r'''(** angelo5fix cycle/value layer (tools/cpu_tmpl_a5cyc.py): next value of every INV register over one whole cycle
    [actual_cycle = fall (rise s)], with the next-state expression resolved through all single-assignment comb wires.
    proof_author: @AUTHOR@; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVPhaseLength Lang.ExtendedSVCheckedAssignmentBinding
 Lang.ExtendedSVSeqTree Lang.ExtendedSVRootProjection Lang.ExtendedSVSeqTree2 Lang.ExtendedSVSeqTree2One Lang.ExtendedSVExprResolve Angelo5.Angelo5FixedAST
 Lang.ExtendedSVSymExec Lang.ExtendedSVSymExecSym Lang.ExtendedSVSymExecNb Lang.ExtendedSVExprAgreement Lang.ExtendedSVProcessSlice
 TmplA5Edge.A5TmplEdge TmplA5Frame.A5TmplFrame TmplA5Target.A5TmplTarget TmplA5Lfp.A5TmplLfp
 TmplA5Stage.A5TmplStage TmplA5Stage2.A5TmplStage2 TmplA5Stage2Csr.A5TmplStage2Csr TmplA5Stage2One.A5TmplStage2One TmplA5Hx.A5TmplHx.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVEmptyPipeline ExtendedSVPhaseLength ExtendedSVCheckedAssignmentBinding
 ExtendedSVSeqTree ExtendedSVRootProjection ExtendedSVSeqTree2 ExtendedSVExprResolve Angelo5FixedAST ExtendedSVSymExec ExtendedSVSymExecSym ExtendedSVSymExecNb ExtendedSVProcessSlice.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module A5TmplCyc.
Notation P := angelo5_program (only parsing).
Module EDGE := TmplA5Edge.A5TmplEdge.A5TmplEdge.
Module FRM := TmplA5Frame.A5TmplFrame.A5TmplFrame.
Module TG := TmplA5Target.A5TmplTarget.A5TmplTarget.
Module LF := TmplA5Lfp.A5TmplLfp.A5TmplLfp.
Module ST := TmplA5Stage.A5TmplStage.A5TmplStage.
Module S2 := TmplA5Stage2.A5TmplStage2.A5TmplStage2.
Module SC := TmplA5Stage2Csr.A5TmplStage2Csr.A5TmplStage2Csr.
Module S1 := TmplA5Stage2One.A5TmplStage2One.A5TmplStage2One.
Module HX := TmplA5Hx.A5TmplHx.A5TmplHx.
Definition cycle (s:State) : State := TG.fall (TG.rise s).
Definition Pre (s:State) : Prop := length s = @NSIG@%nat /\ read_signal s 0%nat = 0 /\ read_signal s 1%nat = 1 /\ EDGE.NetWords s /\ exists seed, CombLFP P seed s.
Definition Post1 (t:State) : Prop := length t = @NSIG@%nat /\ read_signal t 0%nat = 1 /\ read_signal t 1%nat = 1 /\ EDGE.NetWords t /\ exists seed, CombLFP P seed t.
Definition drv (s:State) : State := phase_driven_state P (TG.clock_event s 1) s.
Lemma ev_lt s v : (changed_signal (TG.clock_event s v) < @NSIG@)%nat.
Proof. unfold TG.clock_event. cbn [changed_signal]. lia. Qed.
Lemma words_post ev pre : changed_signal ev = 0%nat -> Word 1 (new_value ev) -> EDGE.NetWords pre -> EDGE.NetWords (PhaseSemantics P ev pre).
Proof. intros Hc Hn HW. unfold EDGE.NetWords in *. destruct HW as @NETPAT@.
@NETPROOF@
Qed.
Lemma pre_rise s : Pre s -> Post1 (TG.rise s).
Proof. intros (Hl & H0 & H1 & HW & seed & HL). unfold Post1, TG.rise.
 pose proof (LF.phase_length s (TG.clock_event s 1) Hl (ev_lt _ _)) as HLen.
 split; [exact HLen|]. split.
 - rewrite phase_input by (vm_compute; reflexivity). unfold TG.clock_event. cbn [changed_signal new_value]. rewrite read_signal_write_same. reflexivity.
 - split.
   + rewrite phase_input by (vm_compute; reflexivity). unfold TG.clock_event. cbn [changed_signal new_value]. rewrite read_signal_write_other by discriminate. exact H1.
   + split.
     * apply words_post; [reflexivity|vm_compute; reflexivity|exact HW].
     * exists (phase_seed P (TG.clock_event s 1) s). exact (LF.settle_lfp s (TG.clock_event s 1) Hl (ev_lt _ _)). Qed.
Lemma pre_fall t : Post1 t -> Pre (TG.fall t).
Proof. intros (Hl & H0 & H1 & HW & seed & HL). unfold Pre, TG.fall.
 pose proof (LF.phase_length t (TG.clock_event t 0) Hl (ev_lt _ _)) as HLen.
 split; [exact HLen|]. split.
 - rewrite phase_input by (vm_compute; reflexivity). unfold TG.clock_event. cbn [changed_signal new_value]. rewrite read_signal_write_same. reflexivity.
 - split.
   + rewrite phase_input by (vm_compute; reflexivity). unfold TG.clock_event. cbn [changed_signal new_value]. rewrite read_signal_write_other by discriminate. exact H1.
   + split.
     * apply words_post; [reflexivity|vm_compute; reflexivity|exact HW].
     * exists (phase_seed P (TG.clock_event t 0) t). exact (LF.settle_lfp t (TG.clock_event t 0) Hl (ev_lt _ _)). Qed.
Theorem pre_cycle s : Pre s -> Pre (cycle s).
Proof. intro H. exact (pre_fall _ (pre_rise s H)). Qed.
Lemma drv_lfp s : Pre s -> exists seed, CombLFP P seed (drv s).
Proof. intros (Hl & _). eexists. unfold drv. exact (LF.driven_lfp s (TG.clock_event s 1) Hl (ev_lt s 1)). Qed.
Lemma dreg s r : comb_root_unwrittenb P r = true -> r <> 0%nat -> read_signal (drv s) r = read_signal s r.
Proof. intros Hr H0. unfold drv. apply driven_unchanged; [exact Hr|]. unfold TG.clock_event. cbn [changed_signal]. intro E. apply H0. symmetry. exact E. Qed.
'''

CYC = r'''Theorem cyc_@R@ s : Pre s -> norm @W@ (read_signal (cycle s) @R@%nat) = norm @W@ (eval_expr (drv s) (@TE@)).
Proof. intro HP. pose proof HP as HP0. destruct HP0 as (Hl & H0 & H1 & HW & seed & HL). destruct (pre_rise s HP) as (Hl2 & H02 & H12 & HW2 & seed2 & HL2).
 unfold cycle, TG.fall. rewrite (FRM.fall_frame_@R@ (TG.clock_event (TG.rise s) 0) (TG.rise s) seed2 eq_refl eq_refl H02 H12 HW2 HL2 (LF.driven_lfp _ _ Hl2 (ev_lt _ _))).
 exact (@MOD@.@LEM@ (TG.clock_event s 1) s seed eq_refl eq_refl H0 H1 HW HL (LF.driven_lfp s _ Hl (ev_lt _ _))). Qed.
Definition te_@R@ : Expr := Eval vm_compute in (@TE@).
Definition ter_@R@ : Expr := Eval vm_compute in esub Mall te_@R@.
Theorem cycr_@R@ s : Pre s -> norm @W@ (read_signal (cycle s) @R@%nat) = norm @W@ (eval_expr (drv s) ter_@R@).
Proof. intro HP. rewrite (cyc_@R@ s HP). destruct (drv_lfp s HP) as [seed HL].
 assert (E1 : (@TE@) = te_@R@) by (vm_compute; reflexivity). rewrite E1.
 assert (E2 : ter_@R@ = esub Mall te_@R@) by (vm_compute; reflexivity). rewrite E2.
 rewrite (esub_sound _ _ (binds_all seed _ HL)). reflexivity. Qed.'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--regs', default='')
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    ast = T.Ast(AST, REP)
    spec = regs_spec(ast)
    regs = [int(x) for x in a.regs.split(',') if x] or sorted(spec)
    netpat = '(' + ' & '.join(f'W{x}' for x in NET) + ')'
    netproof = []
    for k, x in enumerate(NET):
        sep = ' split; [' if k < len(NET) - 1 else ' '
        if x == 0:
            pr = ('(unfold WordRoot in *; rewrite phase_input by (vm_compute; reflexivity); rewrite Hc, read_signal_write_same; exact Hn)')
        else:
            pr = f'exact (phase_word P 1%nat {x}%nat ev pre ltac:(vm_compute; reflexivity) ltac:(rewrite Hc; discriminate) W{x})'
        netproof.append(sep + pr + ('|].' if k < len(NET) - 1 else '.'))
    L = [HEAD.replace('@AUTHOR@', AUTHOR).replace('@NSIG@', str(NSIG)).replace('@NETPAT@', netpat).replace('@NETPROOF@', '\n'.join(netproof))]
    # wire bindings, resolved in topological order
    order, hx = topo(ast)
    L.append('(** ---- single-assignment comb wires: checked binding, then resolved through the earlier wires ---- *)')
    L.append('Definition M0 : list Bind := [].')
    L.append('Lemma binds_0 seed d : CombLFP P seed d -> Binds d M0. Proof. intros _. exact (binds_nil d). Qed.')
    prev = 'M0'; prevb = 'binds_0'
    for n, x in enumerate(order, 1):
        if x in hx:
            w = ast.sig[x]['width']
            L += [f'Definition e_{x} : Expr := HX.h_{x}.',
                  f'Lemma w_{x} seed d : CombLFP P seed d -> norm {w} (read_signal d {x}%nat) = norm {w} (eval_expr d e_{x}).',
                  f'Proof. exact (HX.hw_{x} seed d). Qed.']
        else:
          c = ast.comb[x]
          k, nm, w, e = c['k'], c['name'], c['width'], T.coq(c['rhs'])
          L += [f'Definition e_{x} : Expr := {e}.',
              f'Lemma w_{x} seed d : CombLFP P seed d -> norm {w} (read_signal d {x}%nat) = norm {w} (eval_expr d e_{x}).',
              f'Proof. intro HL. exact (checked_assignment_binding P (filter is_comb (processes P)) {k}%nat {nm} {"true" if c["nba"] else "false"} e_{x} {w}%nat {x}%nat seed d eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HL). Qed.']
        L += [
              f'Definition r_{x} : Expr := Eval vm_compute in esub {prev} e_{x}.',
              f'Lemma b_{x} seed d : CombLFP P seed d -> norm {w} (read_signal d {x}%nat) = norm {w} (eval_expr d r_{x}).',
              f'Proof. intro HL. assert (E : r_{x} = esub {prev} e_{x}) by (vm_compute; reflexivity). rewrite E. exact (resolve_bind d {prev} {x}%nat {w}%nat e_{x} ({prevb} seed d HL) (w_{x} seed d HL)). Qed.',
              ]
        if x in ATOMIC:
            continue
        L += [f'Definition M{n} : list Bind := ({x}%nat, {w}%nat, r_{x}) :: {prev}.',
              f'Lemma binds_{n} seed d : CombLFP P seed d -> Binds d M{n}. Proof. intro HL. exact (binds_cons d {x}%nat {w}%nat r_{x} {prev} (b_{x} seed d HL) ({prevb} seed d HL)). Qed.']
        prev, prevb = f'M{n}', f'binds_{n}'
    L += [f'Definition Mall : list Bind := {prev}.', f'Lemma binds_all seed d : CombLFP P seed d -> Binds d Mall. Proof. exact ({prevb} seed d). Qed.']
    L.append('(** ---- packed flag registers of process 8: non-blocking symbolic executor (no facts) ---- *)')
    L.append('Lemma nofacts s : FactsHold s []. Proof. intros e z H. destruct H. Qed.')
    for p in sorted(set(NB.values())):
        L += [f'Definition ovnb_{p} : SOv := Eval vm_compute in match nbexec [] (statement_fuel P) (process_body process_{p}) [] with Some o => o | None => [] end.',
              f'Lemma nb_{p} : nbexec [] (statement_fuel P) (process_body process_{p}) [] = Some ovnb_{p}. Proof. vm_compute; reflexivity. Qed.']
    for r, p in NB.items():
        w = ast.sig[r]['width']
        L += [f'Definition nbe_{r} : Expr := Eval vm_compute in match sov_lookup ovnb_{p} {r}%nat with Some (_, e) => e | None => EConst 1 0 end.',
              f'Lemma lknb_{r} : sov_lookup ovnb_{p} {r}%nat = Some ({w}%nat, nbe_{r}). Proof. vm_compute; reflexivity. Qed.',
              f'Lemma unwnb_{r} : comb_root_unwrittenb P {r}%nat = true. Proof. vm_compute; reflexivity. Qed.',
              f'Lemma wrnb_{r} : filter (writes_rootb {r}%nat) (processes P) = [process_{p}]. Proof. vm_compute; reflexivity. Qed.',
              f'Theorem rnb_{r} ev pre seed : changed_signal ev = 0%nat -> new_value ev = 1 -> read_signal pre 0%nat = 0 -> read_signal pre 1%nat = 1 -> EDGE.NetWords pre -> CombLFP P seed pre ->',
              f' CombLFP P (write_signal pre (changed_signal ev) (new_value ev)) (phase_driven_state P ev pre) ->',
              f' norm {w} (read_signal (PhaseSemantics P ev pre) {r}%nat) = norm {w} (eval_expr (phase_driven_state P ev pre) nbe_{r}).',
              f'Proof. intros Hc Hv H0 H1 HW HL HD. refine (seq_nb_value P ev pre {r}%nat process_{p} [] ovnb_{p} {w}%nat nbe_{r} unwnb_{r} (fun H => let Hn : 0%nat = {r}%nat := eq_trans (eq_sym Hc) H in ltac:(discriminate Hn)) _ (nofacts _) nb_{p} lknb_{r}).',
              f' rewrite wrnb_{r}. cbn [filter]. rewrite (EDGE.sel_rise_match_{p} ev pre seed Hc Hv H0 H1 HW HL HD). reflexivity. Qed.']
    L.append('(** ---- next value of the INV registers over one cycle ---- *)')
    for r in regs:
        mod, lem, te = spec[r]
        w = ast.sig[r]['width']
        L.append(CYC.replace('@R@', str(r)).replace('@W@', str(w)).replace('@TE@', te).replace('@MOD@.', '' if mod == 'NBX' else mod + '.').replace('@LEM@', lem))
    L.append('(** ---- cross-state bindings: next value of every INV register as an expression over the driven state ---- *)')
    L.append('Definition Mreg : list Bind := [' + '; '.join(f'({r}%nat, {ast.sig[r]["width"]}%nat, ter_{r})' for r in regs) + '].')
    L.append('Lemma binds2_cycle s : Pre s -> Binds2 (drv s) (cycle s) Mreg.')
    L.append('Proof. intro HP. unfold Mreg.')
    for r in regs:
        L.append(f' apply binds2_cons; [exact (cycr_{r} s HP)|].')
    L.append(' apply binds2_nil. Qed.')
    L.append('''Lemma drv_eval s e : forallb (fun wx => comb_root_unwrittenb P (snd wx) && negb (Nat.eqb (snd wx) 0)) (ExtendedSVExprAgreement.expr_inputs e) = true ->
 eval_expr (drv s) e = eval_expr s e.
Proof. intro H. apply ExtendedSVExprAgreement.eval_expr_agree. intros w x Hin. rewrite forallb_forall in H. specialize (H (w, x) Hin). cbn [snd] in H.
 apply andb_true_iff in H as [H1 H2]. rewrite (dreg s x H1); [reflexivity|]. intro E. subst x. discriminate H2. Qed.''')
    L.append('End A5TmplCyc.')
    ex = ['pre_cycle', 'drv_lfp', 'dreg', 'binds2_cycle', 'drv_eval', 'binds_all'] + [f'cycr_{r}' for r in regs]
    L += [f'Print Assumptions A5TmplCyc.{e}.' for e in ex]
    body = '\n'.join(L) + '\n'
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out, dict(wires=len(order), regs=len(regs))); return
    import cpu_tmpl_accept as acc
    R = 'results/'
    prov = [dict(namespace=n, directory=str((ROOT / R / d).resolve())) for n, d in [
        ('TmplA5Edge', 'r-tmpl-a5-edge-20261104-a2'), ('TmplA5Frame', 'r-tmpl-a5-frame-20261104-a1'), ('TmplA5Target', 'r-tmpl-a5-target-20261104-a2'),
        ('TmplA5Lfp', 'r-tmpl-a5-lfp-20261104-b8'), ('TmplA5Stage', 'r-tmpl-a5-stage-20261104-a1'), ('TmplA5Stage2', 'r-tmpl-a5-stage2-20261104-a2'),
        ('TmplA5Stage2Csr', 'r-tmpl-a5-stage2csr-20261104-a1'), ('TmplA5Stage2One', 'r-tmpl-a5-stage2one-20261104-a1'), ('TmplA5Hx', 'r-tmpl-a5-hx-20261104-a1'),
        ('TmplA5Dec', 'r-tmpl-a5-dec-20261104-a3')]]
    ex = [x.split('Print Assumptions ')[1].rstrip('.') for x in L if x.startswith('Print Assumptions')]
    r = acc.accept(a.out, 'TmplA5Cyc', 'A5TmplCyc', body, ex, [('experiments/framework/generated/angelo5-fixed', 'Angelo5')], providers=prov, timeout=3600, factcheck=False,
                   extra=dict(generator='tools/cpu_tmpl_a5cyc.py', design='angelo5fix', proof_author=AUTHOR, provenance='generalized_rule', wires=len(order), regs=len(regs)))
    print(json.dumps({k: v for k, v in r.items() if k != 'loadpaths'}, indent=1)); sys.exit(0 if r.get('coqc_accepted') else 1)


if __name__ == '__main__':
    main()
