#!/usr/bin/env python3
"""srv32 template route: step-level modules (base definitions, phase invariants, per-register one-cycle lemmas, wires, front/back end,
INV and transport, D step).  Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STAGE_FILE = ROOT / 'results/r-tmpl-srv32-stage-20261104-a1/Srv32TmplStage.v'
STAGE = 'TmplSrv32Stage.Srv32TmplStage.Srv32TmplStage'
FRAME = 'TmplSrv32Frame.Srv32TmplFrame.Srv32TmplFrame'
EDGE = 'TmplSrv32Edge.Srv32TmplEdge.Srv32TmplEdge'


def stage_rows():
    """(register, width, process) of every rise_R lemma of the stage layer"""
    t = STAGE_FILE.read_text()
    rows = re.findall(r'Theorem rise_(\d+) ev pre seed.*?norm (\d+)\(read_signal\(PhaseSemantics P ev pre\)\d+%nat\)=norm \d+\(eval_expr\(phase_driven_state P ev pre\)'
                      r'\(texpr (\d+)%nat (\d+)%nat \(tree_of process_(\d+)\)\)\)', t, re.S)
    return [(int(r), int(w), int(k)) for r, w, _, _, k in rows]


BASE_HEAD = r'''From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVConstantRoot Lang.ExtendedSVSeqTree
 Lang.ExtendedSVPhaseLength Lang.ExtendedSVBankAlignment Srv32.Srv32AST TmplSrv32Lfp.Srv32Lfp @EDGE_MOD@ @STAGE_MOD@ @FRAME_MOD@.
Import ListNotations ExtendedSV ExtendedSVPhaseLength ExtendedSVWordInvariant ExtendedSVEmptyPipeline ExtendedSVConstantRoot ExtendedSVSeqTree Srv32AST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module @MOD@.
Notation P := srv32_program (only parsing).
Module E := @EDGE@.
Module L := TmplSrv32Lfp.Srv32Lfp.Srv32Lfp.
Module St := @STAGE@.
Module Fr := @FRAME@.
Definition rise : Event := {|changed_signal:=0%nat;old_value:=0;new_value:=1|}.
Definition fall : Event := {|changed_signal:=0%nat;old_value:=1;new_value:=0|}.
Definition cycle (s:State) : State := PhaseSemantics P fall (PhaseSemantics P rise s).
Definition rg (s:State) (k:nat) (w:nat) : Z := norm w (read_signal s k).
Definition Basic (s:State) : Prop := length s = @NSIG@%nat /\ comb_round P s = s /\ E.NetWords s.
Definition Lo (s:State) : Prop := Basic s /\ read_signal s 0%nat = 0 /\ read_signal s 1%nat = 1.
Definition Hi (s:State) : Prop := Basic s /\ read_signal s 0%nat = 1 /\ read_signal s 1%nat = 1.
Lemma stable_lfp s : comb_round P s = s -> CombLFP P s s.
Proof. intro H. apply CombLFP_intro with (n:=0%nat); [reflexivity|exact H]. Qed.
Lemma lfp_stable seed s : CombLFP P seed s -> comb_round P s = s.
Proof. intro H. inversion H; assumption. Qed.
Lemma unw0 : roots_unwrittenb 0%nat (processes P) = true. Proof. vm_compute; reflexivity. Qed.
Lemma unw1 : roots_unwrittenb 1%nat (processes P) = true. Proof. vm_compute; reflexivity. Qed.
Lemma unw2 : roots_unwrittenb 2%nat (processes P) = true. Proof. vm_compute; reflexivity. Qed.
Lemma word18 : program_wordb P 1 18%nat = true. Proof. vm_compute; reflexivity. Qed.
Lemma word19 : program_wordb P 1 19%nat = true. Proof. vm_compute; reflexivity. Qed.
(** item 4: a phase on the clock or the reset with a one-bit value keeps the basic invariant (state length, combinational fixed point, NetWords = the
    four net signals are words); the post-phase NetWords is the counterpart of [words_driven] of the edge layer *)
Lemma basic_phase ev s : Basic s -> (changed_signal ev = 0%nat \/ changed_signal ev = 1%nat) -> Word 1 (new_value ev) -> Basic (PhaseSemantics P ev s).
Proof. intros [Hl [Hs Hw]] Hc Hn.
 assert (Hlt : (changed_signal ev < @NSIG@)%nat) by (destruct Hc as [ -> | -> ]; lia).
 assert (HL : CombLFP P (phase_seed P ev s) (PhaseSemantics P ev s)) by (apply L.settle_lfp; assumption).
 split; [exact (L.phase_length s ev Hl Hlt)|]. split; [exact (lfp_stable _ _ HL)|].
 unfold E.NetWords in *. destruct Hw as (W0 & W1 & W18 & W19).
 assert (R0 : read_signal (PhaseSemantics P ev s) 0%nat = read_signal (write_signal s (changed_signal ev) (new_value ev)) 0%nat) by exact (phase_input P 0%nat ev s unw0).
 assert (R1 : read_signal (PhaseSemantics P ev s) 1%nat = read_signal (write_signal s (changed_signal ev) (new_value ev)) 1%nat) by exact (phase_input P 1%nat ev s unw1).
 repeat split.
 - unfold Word. rewrite R0. destruct Hc as [Hc|Hc]; rewrite Hc.
   + rewrite read_signal_write_same. exact Hn.
   + rewrite read_signal_write_other by discriminate. exact W0.
 - unfold Word. rewrite R1. destruct Hc as [Hc|Hc]; rewrite Hc.
   + rewrite read_signal_write_other by discriminate. exact W1.
   + rewrite read_signal_write_same. exact Hn.
 - exact (phase_word P 1 18%nat ev s word18 ltac:(destruct Hc as [ -> | -> ]; discriminate) W18).
 - exact (phase_word P 1 19%nat ev s word19 ltac:(destruct Hc as [ -> | -> ]; discriminate) W19).
Qed.
Lemma clk_after ev s : (changed_signal ev = 0%nat) -> read_signal (PhaseSemantics P ev s) 0%nat = new_value ev.
Proof. intro Hc. rewrite (phase_input P 0%nat ev s unw0). rewrite Hc. apply read_signal_write_same. Qed.
Lemma rst_after ev s : (changed_signal ev <> 1%nat) -> read_signal (PhaseSemantics P ev s) 1%nat = read_signal s 1%nat.
Proof. intro Hc. rewrite (phase_input P 1%nat ev s unw1). apply read_signal_write_other. congruence. Qed.
Lemma rom_after ev s : (changed_signal ev <> 2%nat) -> read_signal (PhaseSemantics P ev s) 2%nat = read_signal s 2%nat.
Proof. intro Hc. rewrite (phase_input P 2%nat ev s unw2). apply read_signal_write_other. congruence. Qed.
Lemma rise_hi s : Lo s -> Hi (PhaseSemantics P rise s).
Proof. intros [HB [H0 H1]]. split.
 - apply basic_phase; [exact HB|left; reflexivity|vm_compute; reflexivity].
 - split; [rewrite (clk_after rise s eq_refl); reflexivity|]. rewrite (rst_after rise s ltac:(discriminate)). exact H1. Qed.
Lemma fall_lo s : Hi s -> Lo (PhaseSemantics P fall s).
Proof. intros [HB [H0 H1]]. split.
 - apply basic_phase; [exact HB|left; reflexivity|vm_compute; reflexivity].
 - split; [rewrite (clk_after fall s eq_refl); reflexivity|]. rewrite (rst_after fall s ltac:(discriminate)). exact H1. Qed.
Lemma cycle_lo s : Lo s -> Lo (cycle s).
Proof. intro H. exact (fall_lo _ (rise_hi _ H)). Qed.
Lemma cycle_rom s : read_signal (cycle s) 2%nat = read_signal s 2%nat.
Proof. unfold cycle. rewrite (rom_after fall _ ltac:(discriminate)). apply (rom_after rise s ltac:(discriminate)). Qed.
(** the driven state of the rising edge of a low-phase state *)
Definition D (s:State) : State := phase_driven_state P rise s.
Lemma drv_lfp s : Lo s -> CombLFP P (write_signal s 0%nat 1) (D s).
Proof. intros [[Hl _] _]. unfold D. exact (L.driven_lfp s rise Hl ltac:(vm_compute; lia)). Qed.
Lemma lo_lfp s : Lo s -> CombLFP P s s.
Proof. intros [[_ [Hs _]] _]. exact (stable_lfp s Hs). Qed.
Lemma hi_lfp s : Hi s -> CombLFP P s s.
Proof. intros [[_ [Hs _]] _]. exact (stable_lfp s Hs). Qed.
Lemma lo_clk s : Lo s -> read_signal s 0%nat = 0 /\ read_signal s 1%nat = 1 /\ E.NetWords s.
Proof. intros [[_ [_ Hw]] [H0 H1]]. auto. Qed.
Lemma hi_clk s : Hi s -> read_signal s 0%nat = 1 /\ read_signal s 1%nat = 1 /\ E.NetWords s.
Proof. intros [[_ [_ Hw]] [H0 H1]]. auto. Qed.
Lemma fall_drv_lfp s : Hi s -> CombLFP P (write_signal s 0%nat 0) (phase_driven_state P fall s).
Proof. intros [[Hl _] _]. exact (L.driven_lfp s fall Hl ltac:(vm_compute; lia)). Qed.
Lemma d_rst s : Lo s -> read_signal (D s) 1%nat = 1.
Proof. intro H. destruct (lo_clk s H) as (H0 & H1 & HW). unfold D. rewrite (sampled_input P 1%nat rise s unw1). rewrite read_signal_write_other by discriminate. exact H1. Qed.
Lemma resetb_D s : Lo s -> norm 1 (read_signal (D s) 19%nat) = 1.
Proof. intro H. pose proof (drv_lfp s H) as HL. rewrite (E.netn_19 _ _ HL). rewrite (d_rst s H). reflexivity. Qed.
Lemma d_rom s : read_signal (D s) 2%nat = read_signal s 2%nat.
Proof. unfold D. rewrite (sampled_input P 2%nat rise s unw2). rewrite read_signal_write_other by discriminate. reflexivity. Qed.
Lemma nbit x : norm 1 x = 0 \/ norm 1 x = 1.
Proof. pose proof (ExtendedSVBankAlignment.norm_bounds 1 x) as H. change (0 <= norm 1 x < 2) in H. lia. Qed.
Ltac simp_if := repeat match goal with
 | |- context [if ?c then ?a else ?b] =>
     let v := eval vm_compute in c in
     match v with
     | true => change (if c then a else b) with a
     | false => change (if c then a else b) with b
     end end.
Ltac fin := simp_if; cbn; repeat rewrite ?norm_idempotent; try reflexivity.
'''


def nsig():
    """number of declared signals of the configured AST (was the constant 335 of the original srv32 AST; a mutant with an
    added trigger register has more; tmpl-econd-casesplit-20261111-a1)"""
    import cpu_tmpl_ast as T
    g = ROOT / 'experiments/framework/generated/srv32'
    return len(T.Ast(str(g / 'Srv32AST.v'), str(g / 'report.json')).sig)


def base_text(module='Srv32Base'):
    rows = stage_rows()
    L = [BASE_HEAD.replace('@NSIG@', str(nsig())).replace('@EDGE_MOD@', EDGE.rsplit('.', 1)[0]).replace('@STAGE_MOD@', STAGE.rsplit('.', 1)[0]).replace('@FRAME_MOD@', FRAME.rsplit('.', 1)[0])
         .replace('@EDGE@', EDGE).replace('@STAGE@', STAGE).replace('@FRAME@', FRAME).replace('@MOD@', module)]
    ex = []
    for r, w, k in rows:
        # driven registers keep their value; one cycle (rise then fall frame) gives the value of the rising-edge tree evaluated on the driven state
        L.append(f'Lemma drv_{r} s : read_signal (D s) {r}%nat = read_signal s {r}%nat.')
        L.append(f'Proof. unfold D. exact (driven_unchanged P rise s {r}%nat St.comb_unw_{r} ltac:(discriminate)). Qed.')
        L.append(f'Theorem frm_{r} s : Lo s -> read_signal (cycle s) {r}%nat = read_signal (PhaseSemantics P rise s) {r}%nat.')
        L.append(f'Proof. intro H. pose proof (rise_hi s H) as HH. destruct (hi_clk _ HH) as (G0 & G1 & GW).')
        L.append(f' unfold cycle. exact (Fr.fall_frame_{r} fall (PhaseSemantics P rise s) (PhaseSemantics P rise s) eq_refl eq_refl G0 G1 GW (hi_lfp _ HH) (fall_drv_lfp _ HH)). Qed.')
        L.append(f'Theorem cyc_{r} s : Lo s -> norm {w} (read_signal (cycle s) {r}%nat) = norm {w} (eval_expr (D s) (texpr {w}%nat {r}%nat (St.tree_of process_{k}))).')
        L.append(f'Proof. intro H. destruct (lo_clk s H) as (H0 & H1 & HW). rewrite (frm_{r} s H).')
        L.append(f' exact (St.rise_{r} rise s s eq_refl eq_refl H0 H1 HW (lo_lfp s H) (drv_lfp s H)). Qed.')
        ex.append(f'{module}.cyc_{r}')
    L.append('Ltac drv_all := rewrite ' + ', '.join(f'?drv_{r}' for r, w, k in rows) + '.')
    L.append("Theorem frm_244 s : Lo s -> read_signal (cycle s) 244%nat = read_signal (PhaseSemantics P rise s) 244%nat.")
    L.append("Proof. intro H. pose proof (rise_hi s H) as HH. destruct (hi_clk _ HH) as (G0 & G1 & GW).")
    L.append(" unfold cycle. exact (Fr.fall_frame_244 fall (PhaseSemantics P rise s) (PhaseSemantics P rise s) eq_refl eq_refl G0 G1 GW (hi_lfp _ HH) (fall_drv_lfp _ HH)). Qed.")
    L.append(f'End {module}.')
    L.append('')
    L.append('Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.')
    for r, w, k in rows:
        L.append(f'Print Assumptions {module}.cyc_{r}.')
    return '\n'.join(L) + '\n', ex


if __name__ == '__main__':
    what, out = sys.argv[1], sys.argv[2]
    text, ex = {'base': base_text}[what]()
    Path(out).write_text(text)
    print(out, len(text.splitlines()))
