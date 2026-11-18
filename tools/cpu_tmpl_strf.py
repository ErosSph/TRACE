#!/usr/bin/env python3
"""Steel rebased register file (lane j = x(j+1), pad lane 31), write process shape "reset arm first"
(`if reset_internal then <31 constant lane writes> else if ce & we then bank[(rd-1)*32 +: 32] <= wb`), cycle level (rise then fall),
plus the zero-muxed read-port operand clauses (258/259).  Libraries: Lang/ExtendedSVBankRebase.v (RFRelR, operand_clause_rebased, RFRelR_write)
and the additive Lang/ExtendedSVBankRebaseRst.v (rf3_*).  Facts about the AST (shape, constants) are checked by Coq (vm_compute), the
generator only spells them.  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import json, sys
from pathlib import Path
import cpu_tmpl_ast as T

HEAD = r"""(** Steel: rebased register file at cycle level (tools/cpu_tmpl_strf.py).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice Lang.ExtendedSVSeqStep
 Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVBankOperand Lang.ExtendedSVBankRebase Lang.ExtendedSVBankRebaseRst Lang.ExtendedSVEmptyPipeline Steel.SteelAST
 TmplSteelEdge.SteelTmplEdge TmplSteelFrame.SteelTmplFrame TmplSteelTarget.SteelTmplTarget TmplSteelLfp.SteelTmplLfp TmplSteelCyc.SteelTmplCyc.
Import ListNotations ExtendedSV ExtendedSVRegisterBank ExtendedSVBankAlignment ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVSeqStep ExtendedSVCheckedAssignmentBinding ExtendedSVBankOperand
 ExtendedSVBankRebase ExtendedSVBankRebaseRst ExtendedSVEmptyPipeline SteelAST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module SteelTmplRF.
Notation P := steel_program (only parsing).
Module EDGE := TmplSteelEdge.SteelTmplEdge.SteelTmplEdge.
Module FRM := TmplSteelFrame.SteelTmplFrame.SteelTmplFrame.
Module TG := TmplSteelTarget.SteelTmplTarget.SteelTmplTarget.
Module LF := TmplSteelLfp.SteelTmplLfp.SteelTmplLfp.
Module CY := TmplSteelCyc.SteelTmplCyc.SteelTmplCyc.
Definition rf_inner : Stmt := match process_body process_8 with SSeq [SSeq [x]] => x | _ => SSkip end.
Definition rf_sts : list Stmt := match rf_inner with SIf _ (SSeq l) _ => l | _ => [] end.
Definition cr_e : Expr := EVar 1%nat 256%nat.
Definition cg_e : Expr := EBinary 1%nat BAnd (EVar 1%nat 170%nat) (EVar 1%nat 215%nat).
Definition data_e : Expr := EVar 32%nat 277%nat.
Lemma body_shape : process_body process_8 = SSeq [SSeq [SIf cr_e (SSeq rf_sts) (SIf cg_e (SAssign true data_e (LSel 32%nat (LVar 1024%nat 214%nat) (rebased_index 223%nat))) SSkip)]].
Proof. vm_compute. reflexivity. Qed.
Lemma rf_sts_nba : nba_blockb rf_sts = true. Proof. vm_compute; reflexivity. Qed.
Definition rf_js : list Z := map Z.of_nat (seq 0 31).
Lemma rf_sts_upd : forall d, nba_updates d rf_sts = map (fun j => bank_write 214%nat 32%nat j 0) rf_js.
Proof. intro d. vm_compute. reflexivity. Qed.
Lemma rf_js_nonneg : Forall (fun j => 0 <= j) rf_js.
Proof. apply Forall_forall. intros x Hx. unfold rf_js in Hx. apply in_map_iff in Hx as (n & <- & _). apply Nat2Z.is_nonneg. Qed.
Lemma rf_js_in i : 0 <= i < 31 -> In i rf_js.
Proof. intros Hi. unfold rf_js. apply in_map_iff. exists (Z.to_nat i). split; [apply Z2Nat.id; lia|]. apply in_seq. lia. Qed.
Lemma comb_unw : comb_root_unwrittenb P 214%nat = true. Proof. vm_compute; reflexivity. Qed.
Lemma writers : filter (writes_rootb 214%nat) (processes P) = [process_8]. Proof. vm_compute; reflexivity. Qed.
Lemma sel s : CY.Pre s -> filter (process_matches_states s (CY.drv s)) (filter (writes_rootb 214%nat) (processes P)) = [process_8].
Proof. intros (Hl & H0 & H1 & HW & seed & HL). unfold CY.drv. rewrite writers. cbn [filter].
 rewrite (EDGE.sel_rise_match_8 (TG.clock_event s 1) s seed eq_refl eq_refl H0 H1 HW HL (LF.driven_lfp s _ Hl (CY.ev_lt _ _))). reflexivity. Qed.
Lemma nochange s : changed_signal (TG.clock_event s 1) <> 214%nat. Proof. unfold TG.clock_event. cbn [changed_signal]. discriminate. Qed.
Lemma bank_fall s : CY.Pre s -> read_signal (TG.fall (TG.rise s)) 214%nat = read_signal (TG.rise s) 214%nat.
Proof. intro HP. destruct (CY.pre_rise s HP) as (Hl2 & H02 & H12 & HW2 & seed2 & HL2). unfold TG.fall.
 exact (FRM.fall_frame_214 (TG.clock_event (TG.rise s) 0) (TG.rise s) seed2 eq_refl eq_refl H02 H12 HW2 HL2 (LF.driven_lfp _ _ Hl2 (CY.ev_lt _ _))). Qed.
Lemma fuel5 : (5 <= statement_fuel P)%nat. Proof. vm_compute. repeat constructor. Qed.
Theorem rf_reset_lanes s : CY.Pre s -> eval_expr (CY.drv s) cr_e <> 0 ->
 forall i, 0 <= i < 31 -> lane_read 32%nat (read_signal (TG.fall (TG.rise s)) 214%nat) i = 0.
Proof. intros HP Hc i Hi. rewrite (bank_fall s HP). unfold TG.rise.
 refine (rf3_reset_lanes P (TG.clock_event s 1) s 214%nat process_8 cr_e rf_sts _ 32%nat rf_js comb_unw (nochange s) body_shape fuel5 rf_sts_nba (sel s HP) Hc (rf_sts_upd _) rf_js_nonneg i ltac:(lia) _).
 apply rf_js_in; lia. Qed.
Theorem rfrel_reset s : CY.Pre s -> eval_expr (CY.drv s) cr_e <> 0 -> RFRelR (read_signal (TG.fall (TG.rise s)) 214%nat) (fun _ => 0).
Proof. intros HP Hc. apply RFRelR_reset. intros j Hj. exact (rf_reset_lanes s HP Hc j Hj). Qed.
Definition rdv (s:State) : Z := norm 5 (read_signal (CY.drv s) 223%nat).
Definition wbv (s:State) : Z := norm 32 (eval_expr (CY.drv s) data_e).
Theorem rf_lane_write_nz s i : CY.Pre s -> eval_expr (CY.drv s) cr_e = 0 -> eval_expr (CY.drv s) cg_e <> 0 -> rdv s <> 0 -> 0 <= i ->
 lane_read 32%nat (read_signal (TG.fall (TG.rise s)) 214%nat) i = if Z.eqb i (rdv s - 1) then wbv s else lane_read 32%nat (read_signal s 214%nat) i.
Proof. intros HP Hr Hc Hz Hi. rewrite (bank_fall s HP). unfold TG.rise.
 pose proof (norm_bounds 5 (read_signal (CY.drv s) 223%nat)) as HB. change (0 <= norm 5 (read_signal (CY.drv s) 223%nat) < 32) in HB.
 unfold rdv in *.
 refine (rf3_lane_write P (TG.clock_event s 1) s 214%nat process_8 cr_e (SSeq rf_sts) cg_e data_e 32%nat 1024%nat (rebased_index 223%nat) (norm 5 (read_signal (CY.drv s) 223%nat) - 1) i comb_unw (nochange s) body_shape fuel5 (sel s HP) Hr Hc _ ltac:(lia) Hi).
 exact (rebase_eval _ 223%nat Hz). Qed.
Theorem rf_lane_write_x0 s i : CY.Pre s -> eval_expr (CY.drv s) cr_e = 0 -> eval_expr (CY.drv s) cg_e <> 0 -> rdv s = 0 -> 0 <= i ->
 lane_read 32%nat (read_signal (TG.fall (TG.rise s)) 214%nat) i = if Z.eqb i 31 then wbv s else lane_read 32%nat (read_signal s 214%nat) i.
Proof. intros HP Hr Hc Hz Hi. rewrite (bank_fall s HP). unfold TG.rise. unfold rdv in Hz.
 refine (rf3_lane_write P (TG.clock_event s 1) s 214%nat process_8 cr_e (SSeq rf_sts) cg_e data_e 32%nat 1024%nat (rebased_index 223%nat) 31 i comb_unw (nochange s) body_shape fuel5 (sel s HP) Hr Hc _ ltac:(lia) Hi).
 exact (rebase_eval_zero _ 223%nat Hz). Qed.
Theorem rfrel_write s view : CY.Pre s -> eval_expr (CY.drv s) cr_e = 0 -> eval_expr (CY.drv s) cg_e <> 0 -> rdv s <> 0 ->
 RFRelR (read_signal s 214%nat) view -> RFRelR (read_signal (TG.fall (TG.rise s)) 214%nat) (fun i => if Z.eqb i (rdv s) then wbv s else view i).
Proof. intros HP Hr Hc Hz HR. pose proof (norm_bounds 5 (read_signal (CY.drv s) 223%nat)) as HB. change (0 <= norm 5 (read_signal (CY.drv s) 223%nat) < 32) in HB.
 unfold rdv in *.
 refine (RFRelR_write (read_signal s 214%nat) _ view (norm 5 (read_signal (CY.drv s) 223%nat)) (wbv s) HR ltac:(lia) _).
 intros i Hi. exact (rf_lane_write_nz s i HP Hr Hc Hz Hi). Qed.
Theorem rfrel_write_x0 s view : CY.Pre s -> eval_expr (CY.drv s) cr_e = 0 -> eval_expr (CY.drv s) cg_e <> 0 -> rdv s = 0 ->
 RFRelR (read_signal s 214%nat) view -> RFRelR (read_signal (TG.fall (TG.rise s)) 214%nat) view.
Proof. intros HP Hr Hc Hz HR. refine (RFRelR_pad_write _ _ view HR _). intros i Hi.
 rewrite (rf_lane_write_x0 s i HP Hr Hc Hz Hi). destruct (Z.eqb i 31) eqn:E; [|reflexivity].
 apply Z.eqb_eq in E. subst i. rewrite (rf_lane_write_x0 s 31 HP Hr Hc Hz ltac:(lia)). rewrite Z.eqb_refl. reflexivity. Qed.
Theorem rfrel_frame s view : CY.Pre s -> eval_expr (CY.drv s) cr_e = 0 -> eval_expr (CY.drv s) cg_e = 0 ->
 RFRelR (read_signal s 214%nat) view -> RFRelR (read_signal (TG.fall (TG.rise s)) 214%nat) view.
Proof. intros HP Hr Hc HR. rewrite (bank_fall s HP). unfold TG.rise.
 refine (RFRelR_frame _ _ _ HR _).
 exact (rf3_frame P (TG.clock_event s 1) s 214%nat process_8 cr_e (SSeq rf_sts) cg_e _ comb_unw (nochange s) body_shape fuel5 (sel s HP) Hr Hc). Qed.
@OPS@
End SteelTmplRF.
@PRINTS@"""

HEAD_RAM = r"""(** Steel: RAM hold at cycle level, write guard off (tools/cpu_tmpl_strf.py --ram).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankAlignment Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice Lang.ExtendedSVSeqStep
 Lang.ExtendedSVCheckedAssignmentBinding Lang.ExtendedSVBankOperand Lang.ExtendedSVBankRebase Lang.ExtendedSVBankRebaseRst Lang.ExtendedSVEmptyPipeline Steel.SteelAST
 TmplSteelEdge.SteelTmplEdge TmplSteelFrame.SteelTmplFrame TmplSteelTarget.SteelTmplTarget TmplSteelLfp.SteelTmplLfp TmplSteelCyc.SteelTmplCyc.
Import ListNotations ExtendedSV ExtendedSVRegisterBank ExtendedSVBankAlignment ExtendedSVRootProjection ExtendedSVProcessSlice ExtendedSVSeqStep ExtendedSVCheckedAssignmentBinding ExtendedSVBankOperand
 ExtendedSVBankRebase ExtendedSVBankRebaseRst ExtendedSVEmptyPipeline SteelAST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module SteelTmplRam.
Notation P := steel_program (only parsing).
Module EDGE := TmplSteelEdge.SteelTmplEdge.SteelTmplEdge.
Module FRM := TmplSteelFrame.SteelTmplFrame.SteelTmplFrame.
Module TG := TmplSteelTarget.SteelTmplTarget.SteelTmplTarget.
Module LF := TmplSteelLfp.SteelTmplLfp.SteelTmplLfp.
Module CY := TmplSteelCyc.SteelTmplCyc.SteelTmplCyc.
Definition wg_e : Expr := EBinary 1%nat BAnd (EVar 1%nat 6%nat) (EUnary 1%nat UNot (EVar 1%nat 17%nat)).
Definition ram_y : Stmt := match process_body process_2 with SSeq [SSeq [SIf _ y _]] => y | _ => SSkip end.
Lemma body_shape : process_body process_2 = SSeq [SSeq [SIf wg_e ram_y SSkip]]. Proof. vm_compute. reflexivity. Qed.
Lemma comb_unw : comb_root_unwrittenb P 15%nat = true. Proof. vm_compute; reflexivity. Qed.
Lemma writers : filter (writes_rootb 15%nat) (processes P) = [process_2]. Proof. vm_compute; reflexivity. Qed.
Lemma sel s : CY.Pre s -> filter (process_matches_states s (CY.drv s)) (filter (writes_rootb 15%nat) (processes P)) = [process_2].
Proof. intros (Hl & H0 & H1 & HW & seed & HL). unfold CY.drv. rewrite writers. cbn [filter].
 rewrite (EDGE.sel_rise_match_2 (TG.clock_event s 1) s seed eq_refl eq_refl H0 H1 HW HL (LF.driven_lfp s _ Hl (CY.ev_lt _ _))). reflexivity. Qed.
Lemma nochange s : changed_signal (TG.clock_event s 1) <> 15%nat. Proof. unfold TG.clock_event. cbn [changed_signal]. discriminate. Qed.
Lemma ram_fall s : CY.Pre s -> read_signal (TG.fall (TG.rise s)) 15%nat = read_signal (TG.rise s) 15%nat.
Proof. intro HP. destruct (CY.pre_rise s HP) as (Hl2 & H02 & H12 & HW2 & seed2 & HL2). unfold TG.fall.
 exact (FRM.fall_frame_15 (TG.clock_event (TG.rise s) 0) (TG.rise s) seed2 eq_refl eq_refl H02 H12 HW2 HL2 (LF.driven_lfp _ _ Hl2 (CY.ev_lt _ _))). Qed.
Theorem ram_hold s : CY.Pre s -> eval_expr (CY.drv s) wg_e = 0 -> read_signal (TG.fall (TG.rise s)) 15%nat = read_signal s 15%nat.
Proof. intros HP Hc. rewrite (ram_fall s HP). unfold TG.rise.
 exact (if_off_frame P (TG.clock_event s 1) s 15%nat process_2 wg_e ram_y comb_unw (nochange s) body_shape ltac:(vm_compute; repeat constructor) (sel s HP) Hc). Qed.
End SteelTmplRam.
Print Assumptions SteelTmplRam.ram_hold.
"""


def build(module):
    ast = T.Ast('experiments/framework/generated/steel/SteelAST.v', 'experiments/framework/generated/steel/report.json')
    ops, exports = [], [f'{module}.{x}' for x in ('rf_reset_lanes', 'rfrel_reset', 'rf_lane_write_nz', 'rf_lane_write_x0', 'rfrel_write', 'rfrel_write_x0', 'rfrel_frame')]
    for d, idxreg in ((258, 224), (259, 225)):
        k, nm = ast.comb[d]['k'], ast.comb[d]['name']
        ops += [f'Lemma port{d}_at : nth_error (filter is_comb (processes P)) {k}%nat = Some {nm}. Proof. vm_compute; reflexivity. Qed.',
                f'Lemma port{d}_bind : assignment_bindingb (filter is_comb (processes P)) {k}%nat = true. Proof. vm_compute; reflexivity. Qed.',
                f'Lemma port{d}_body : process_body {nm} = SAssign false (ECond 32 (EBinary 1 BEq (EConst 5 0) (EVar 5 {idxreg}%nat)) (EConst 32 0) (ESel 32 (EVar 1024%nat 214%nat) (rebased_index {idxreg}%nat))) (LVar 32 {d}%nat).',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Theorem operand_{d} seed fixed view : CombLFP P seed fixed -> RFRelR (read_signal fixed 214%nat) view -> norm 32 (read_signal fixed {d}%nat) = view (norm 5 (read_signal fixed {idxreg}%nat)).',
                f'Proof. intros HL HR. exact (operand_clause_rebased P _ {k}%nat {nm} false {d}%nat 214%nat 1024%nat {idxreg}%nat seed fixed view eq_refl port{d}_at port{d}_body port{d}_bind ltac:(vm_compute; lia) HL ltac:(lia) HR). Qed.']
        exports.append(f'{module}.operand_{d}')
    text = HEAD.replace('@OPS@', '\n'.join(ops)).replace('@PRINTS@', ''.join(f'Print Assumptions {e}.\n' for e in exports))
    return text.replace('SteelTmplRF', module), exports


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--ram', action='store_true')
    ap.add_argument('--module', default='SteelTmplRF')
    ap.add_argument('--namespace', default='TmplSteelRF')
    a = ap.parse_args()
    if a.ram:
        text, exports = HEAD_RAM, [a.module + '.ram_hold']
        text = text.replace('SteelTmplRam', a.module)
    else:
        text, exports = build(a.module)
    if not a.accept:
        Path(a.out).write_text(text); print(a.out); sys.exit(0)
    import cpu_tmpl_accept as acc
    prov = [dict(namespace=n, directory=str(Path(d).resolve())) for n, d in (
        ('TmplSteelEdge', 'results/r-tmpl-steel-edge-20261104-a3'), ('TmplSteelFrame', 'results/r-tmpl-steel-frame-20261104-a1'),
        ('TmplSteelTarget', 'results/r-tmpl-steel-target-20261104-a1'), ('TmplSteelLfp', 'results/r-tmpl-steel-lfp-20261104-a1'),
        ('TmplSteelCyc', 'results/r-tmpl-steel-cyc-20261104-a1'), ('TmplSteelStage', 'results/r-tmpl-steel-stage-20261104-a3'))]
    r = acc.accept(a.out, a.namespace, a.module, text, exports, [('experiments/framework/generated/steel', 'Steel')], providers=prov,
                   extra=dict(generator='tools/cpu_tmpl_strf.py', design='steel', ram=a.ram, libraries=['src/Lang/ExtendedSVBankRebaseRst.v']))
    print(json.dumps({k: v for k, v in r.items() if k != 'loadpaths'}, indent=1))
    sys.exit(0 if (r['accepted'] or r.get('coqc_accepted')) else 1)
