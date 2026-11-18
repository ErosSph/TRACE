#!/usr/bin/env python3
"""srv32 closure, front end: the EX-stage registers captured from the fetched word, for all 29 classes (one script).
Emits the Coq module `Srv32TmplFront`:
  * `exc i` = the EX register clauses of a decoded instruction i (flags of the accepted capture layer Srv32Cap, ex_system/
    ex_system_op/ex_mem2reg = 0, the register fields and the immediate),
  * `cap_<C>`: from a low-phase state with stall_r = flush = 0 and imem_rdata = w, decode w = C fields, one cycle later
    DecOut (exc (C fields)).  Same script for the 29 classes: decode inverse -> Cap lemma -> frame of the fall ->
    field/immediate/system lemmas -> clause list.
Inputs: the statements of results/route-srv32-20261104-reg1/cap/Srv32Cap.v (flag lists), CPUClassTableInverse (fields).
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
CAP = ROOT / 'results/route-srv32-20261104-reg1/cap/Srv32Cap.v'
R3 = ['Add', 'Sub', 'Sll', 'Slt', 'Sltu', 'Xor', 'Srl', 'Sra', 'Or', 'And']
I3 = ['Addi', 'Slti', 'Sltiu', 'Xori', 'Ori', 'Andi']
SH = ['Slli', 'Srli', 'Srai']
BR = ['Beq', 'Bne', 'Blt', 'Bge', 'Bltu', 'Bgeu']
ALL = R3 + I3 + SH + ['Lui', 'Auipc', 'Jal', 'Jalr'] + BR
NF = {c: (2 if c in ('Lui', 'Auipc', 'Jal') else 3) for c in ALL}
OPC = {**{c: 51 for c in R3}, **{c: 19 for c in I3 + SH}, 'Lui': 55, 'Auipc': 23, 'Jal': 111, 'Jalr': 103, **{c: 99 for c in BR}}
F3I = {'Addi': 0, 'Slti': 2, 'Sltiu': 3, 'Xori': 4, 'Ori': 6, 'Andi': 7, 'Slli': 1, 'Srli': 5, 'Srai': 5}


def cap_table():
    t = CAP.read_text()
    out = {}
    for m in re.finditer(r'^Theorem (\w+)_cap ev pre seed \(w : Z\)( \(([\w ]+) : Z\))? : (.*)$', t, re.M):
        body = m.group(4)
        hyps = re.findall(r'norm (\d) \(Z\.shiftr w (\d+)\) = (\w+)', body)
        concl = re.findall(r'norm (\d)%nat \(read_signal \(PhaseSemantics P ev pre\) (\d+)%nat\) = (\w+)', body)
        out[m.group(1)] = dict(vars=(m.group(3) or '').split(), hyps=hyps, concl=concl)
    return out


def fields(c):
    """(reg, width, value) of the decoded fields a0 a1 a2"""
    if c in R3:
        return [(254, 5, 'a0'), (252, 5, 'a1'), (253, 5, 'a2')]
    if c in I3 + SH or c == 'Jalr':
        return [(254, 5, 'a0'), (252, 5, 'a1'), (250, 32, 'norm 32 a2')]
    if c in ('Lui', 'Auipc', 'Jal'):
        return [(254, 5, 'a0'), (250, 32, 'norm 32 a1')]
    if c in BR:
        return [(252, 5, 'a0'), (253, 5, 'a1'), (250, 32, 'norm 32 a2')]


def imm_lemma(c):
    if c in ('Lui', 'Auipc'):
        return 'imm320_U'
    if c == 'Jal':
        return 'imm320_J'
    if c == 'Jalr':
        return 'imm320_jalr'
    if c in BR:
        return 'imm320_B'
    if c in I3:
        return f'imm320_a{F3I[c]}'
    if c in SH:
        return f'imm320_s{F3I[c]}'
    return None


def exc_def(tab):
    arms = []
    for c in ALL:
        fs = ' '.join(f'a{k}' for k in range(NF[c]))
        fl = [f'(({r}%nat,{w}%nat),{v})' for w, r, v in tab[c]['concl']] + ['((269%nat,1%nat),0)', '((270%nat,1%nat),0)', '((258%nat,1%nat),0)']
        fl += [f'(({r}%nat,{w}%nat),{v})' for r, w, v in fields(c)]
        arms.append(f' | Decode.{c} {fs} => [{"; ".join(fl)}]')
    return 'Definition exc (i:Decode.InstructionI) : list ((nat*nat)*Z) :=\n match i with\n' + '\n'.join(arms) + '\n | _ => [] end.'


def cap_text(c, tab):
    n = NF[c]
    fs = ' '.join(f'a{k}' for k in range(n))
    ctor = f'(Decode.{c} {fs})'
    vars_ = tab[c]['vars']
    vv = {'f3': '(norm 3 (Z.shiftr w 12))', 'f7': '(norm 7 (Z.shiftr w 25))', 'b30': '(norm 1 (Z.shiftr w 30))'}
    args = ' '.join(vv[v] for v in vars_)
    nh = len(tab[c]['hyps'])
    regs = [r for _, r, _ in tab[c]['concl']]
    L = [f'Theorem cap_{c} s w {fs} : B.Lo s -> norm 1 (read_signal s 232%nat) = 0 -> norm 1 (read_signal s 234%nat) = 0 ->',
         f' norm 32 (read_signal s 12%nat) = w -> Decode.decode Decode.RV32I w = Decode.IInstruction {ctor} -> DecOut (B.cycle s) (exc {ctor}).',
         'Proof. intros HLo H232 H234 H12 Hdec.',
         f' destruct (CI.inv_{c} w {fs} Hdec) as [E Hb]. split_all. subst_fields.',
         ' destruct (front_ctx s w HLo H232 H234 H12) as (HLs & HL & R0 & R1 & HNW & R19 & D236 & D233).',
         f' pose proof (CP.{c}_cap B.rise s s w {args} eq_refl eq_refl R0 R1 HNW HLs HL R19 D236 D233) as K.',
         ' discharge K. split_all. to_cycle s HLo.',
         f' pose proof (sys_op{OPC[c]} s w HLo D236 D233 ltac:(solve_sl)) as [Y269 [Y270 Y258]].',
         ' destruct (fld_cap s w HLo D236 D233) as [Y252 [Y253 Y254]].']
    im = imm_lemma(c)
    if im:
        a1 = {'Lui': 'ltac:(left; solve_sl)', 'Auipc': 'ltac:(right; solve_sl)'}.get(c, 'ltac:(solve_sl)')
        L.append(f' pose proof (NX.nx_250 s _ HLo D236 ({im} _ _ w HL D233 {a1} {"ltac:(solve_sl) " if c in I3 + SH else ""})) as Y250.')
    L += [' intros t Ht. cbv [exc] in Ht. repeat (destruct Ht as [<-|Ht]; [cbn [fst snd]; first [assumption | solve_fld] |]). contradiction.',
          'Qed.']
    return '\n'.join(L)


HEAD = r'''(** srv32 closure, front end: the EX-stage register clauses [exc i] of a decoded instruction and their capture from the
    fetched word in one cycle, for all 29 classes (tools/cpu_tmpl_srv32_front.py).
    proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqTree Lang.ExtendedSVBankAlignment
 Ex.External.CPUImmediateShapes Ex.External.CPUImmediateRtlShapes Ex.External.CPUISARegView Ex.External.CPUClassTableInverse
 riscv.Utility.Utility riscv.Spec.Decode Ex.External.CPUJumpFamilyProgramDomain Srv32.Srv32AST
 TmplSrv32Base.Srv32Base TmplSrv32Stage.Srv32TmplStage TmplSrv32Cap.Srv32Cap TmplSrv32Wire.Srv32Wire TmplSrv32Nx.Srv32Nx TmplSrv32Imm.Srv32TmplImm.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVSeqTree CPUImmediateShapes CPUImmediateRtlShapes Srv32AST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module Srv32TmplFront.
Notation P := srv32_program (only parsing).
Module B := TmplSrv32Base.Srv32Base.Srv32Base.
Module St := TmplSrv32Stage.Srv32TmplStage.Srv32TmplStage.
Module CP := TmplSrv32Cap.Srv32Cap.Srv32Cap.
Module WI := TmplSrv32Wire.Srv32Wire.Srv32Wire.
Module NX := TmplSrv32Nx.Srv32Nx.Srv32Nx.
Module IM := TmplSrv32Imm.Srv32TmplImm.Srv32TmplImm.
Module CI := CPUClassTableInverse.CPUClassTableInverse.
Module V := CPUISARegView.CPUISARegView.
Definition DecOut (s:State) (l:list ((nat*nat)*Z)) : Prop := forall t, In t l -> norm (snd (fst t)) (read_signal s (fst (fst t))) = snd t.
'''

COMMON = r'''
(** ---- word slices ---- *)
Lemma tbn k x i : 0 <= i -> Z.testbit (norm k x) i = (i <? Z.of_nat k) && Z.testbit x i.
Proof. intro Hi. rewrite norm_ones, Z.land_spec. destruct (Z.ltb_spec0 i (Z.of_nat k)).
 - rewrite Z.testbit_ones_nonneg by lia. replace (i <? Z.of_nat k) with true by (symmetry; apply Z.ltb_lt; lia). rewrite andb_true_r. reflexivity.
 - rewrite Z.testbit_ones_nonneg by lia. replace (i <? Z.of_nat k) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity. Qed.
Lemma sub_slice w s e a k : 0 <= s <= a -> a + Z.of_nat k <= e -> norm k (Z.shiftr w a) = norm k (Z.shiftr (bitSlice w s e) (a - s)).
Proof. intros H1 H2. rewrite (V.bs_norm w s e) by lia. apply Z.bits_inj'. intros i Hi.
 rewrite !tbn by lia. destruct (i <? Z.of_nat k) eqn:E; [|reflexivity]. apply Z.ltb_lt in E. cbn [andb].
 rewrite !Z.shiftr_spec by lia. rewrite tbn by lia. rewrite Z2Nat.id by lia.
 replace (i + (a - s) <? e - s) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb]. rewrite Z.shiftr_spec by lia. f_equal. lia. Qed.
Ltac solve_sl := first [ assumption | reflexivity
 | match goal with H : bitSlice ?w ?s ?e = _ |- norm ?k (Z.shiftr ?w ?a) = _ => rewrite (sub_slice w s e a k) by lia; rewrite H; reflexivity end
 | match goal with H : bitSlice ?w 26 32 = _, H2 : bitSlice ?w 25 26 = 0 |- norm 7 (Z.shiftr ?w 25) = _ => rewrite (V.bs7_shift w H2), H; reflexivity end
 | match goal with |- eval_expr _ (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = _ => cbn [eval_expr]; change (norm 5 0) with 0; match goal with H : norm 32 (read_signal _ 233%nat) = ?w |- _ => rewrite H; solve_sl end end
 | match goal with |- eval_expr _ (ESel 3 (EVar 32 233%nat) (EConst 5 12)) = _ => cbn [eval_expr]; change (norm 5 12) with 12; match goal with H : norm 32 (read_signal _ 233%nat) = ?w |- _ => rewrite H; solve_sl end end ].
Ltac split_all := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac subst_fields := repeat match goal with H : ?a = bitSlice _ _ _ |- _ => is_var a; subst a
 | H : ?a = signExtend _ _ |- _ => is_var a; subst a | H : ?a = machineIntToShamt _ |- _ => is_var a; subst a end.
Ltac discharge K := repeat (lazymatch type of K with ?A -> _ => let H := fresh "Hp" in assert (H : A) by solve_sl; specialize (K H); clear H end).

(** ---- the context at the driven state of a fetching cycle ---- *)
Lemma frm_rise s : B.Lo s -> forall r, In r [257;266;267;264;265;262;288;261;255;256;268;251;279]%nat ->
 read_signal (PhaseSemantics P B.rise s) r = read_signal (B.cycle s) r.
Proof. intros H r Hr. repeat (destruct Hr as [<-|Hr]; [symmetry; first [exact (B.frm_257 s H) | exact (B.frm_266 s H) | exact (B.frm_267 s H)
 | exact (B.frm_264 s H) | exact (B.frm_265 s H) | exact (B.frm_262 s H) | exact (B.frm_288 s H) | exact (B.frm_261 s H) | exact (B.frm_255 s H)
 | exact (B.frm_256 s H) | exact (B.frm_268 s H) | exact (B.frm_251 s H) | exact (B.frm_279 s H)]|]). contradiction. Qed.
Ltac pick_in := repeat first [apply in_eq | apply in_cons].
Ltac to_cycle s HLo := repeat match goal with H : norm ?w (read_signal (PhaseSemantics P B.rise s) ?r) = ?v |- _ =>
 rewrite (frm_rise s HLo r ltac:(pick_in)) in H end.
Theorem front_ctx s w : B.Lo s -> norm 1 (read_signal s 232%nat) = 0 -> norm 1 (read_signal s 234%nat) = 0 -> norm 32 (read_signal s 12%nat) = w ->
 CombLFP P s s /\ CombLFP P (write_signal s (changed_signal B.rise) (new_value B.rise)) (phase_driven_state P B.rise s) /\
 read_signal s 0%nat = 0 /\ read_signal s 1%nat = 1 /\ TmplSrv32Edge.Srv32TmplEdge.Srv32TmplEdge.NetWords s /\
 norm 1 (read_signal (phase_driven_state P B.rise s) 19%nat) = 1 /\ norm 1 (read_signal (phase_driven_state P B.rise s) 236%nat) = 0 /\
 norm 32 (read_signal (phase_driven_state P B.rise s) 233%nat) = w.
Proof. intros HLo H232 H234 H12. pose proof (B.drv_lfp s HLo) as HL. destruct (B.lo_clk s HLo) as (R0 & R1 & HNW).
 refine (conj (B.lo_lfp s HLo) (conj HL (conj R0 (conj R1 (conj HNW (conj (B.resetb_D s HLo) _)))))).
 assert (D232 : norm 1 (read_signal (B.D s) 232%nat) = 0) by (rewrite B.drv_232; exact H232).
 assert (D234 : norm 1 (read_signal (B.D s) 234%nat) = 0) by (rewrite B.drv_234; exact H234).
 assert (D12 : norm 32 (read_signal (B.D s) 12%nat) = w) by (rewrite B.drv_12; exact H12).
 split; [exact (proj1 (WI.stall_wires _ _ _ _ _ HL D232 eq_refl eq_refl eq_refl))|].
 change (phase_driven_state P B.rise s) with (B.D s). rewrite (WI.inst_noflush _ _ w HL D234 D12). rewrite <- H12. apply norm_idempotent. Qed.

(** ---- fields, immediates, the system/load flags of the captured word ---- *)
Ltac rise_tree s H R e w r :=
 rewrite (e s H); let t := eval vm_compute in (texpr w r (St.tree_of R)) in change (texpr w r (St.tree_of R)) with t; cbn [eval_expr].
Theorem fld_cap s w : B.Lo s -> norm 1 (read_signal (B.D s) 236%nat) = 0 -> norm 32 (read_signal (B.D s) 233%nat) = w ->
 norm 5 (read_signal (B.cycle s) 252%nat) = bitSlice w 15 20 /\ norm 5 (read_signal (B.cycle s) 253%nat) = bitSlice w 20 25 /\
 norm 5 (read_signal (B.cycle s) 254%nat) = bitSlice w 7 12.
Proof. intros H H0 H1. pose proof (B.resetb_D s H) as R1. rewrite !V.bs_norm by lia. cbn [Z.sub Z.to_nat Pos.to_nat Pos.iter_op].
 split; [|split].
 - rise_tree s H process_4 B.cyc_252 5%nat 252%nat. rewrite R1, H0, H1. change (norm 5 15) with 15. cbn. rewrite !norm_idempotent. reflexivity.
 - rise_tree s H process_4 B.cyc_253 5%nat 253%nat. rewrite R1, H0, H1. change (norm 5 20) with 20. cbn. rewrite !norm_idempotent. reflexivity.
 - rise_tree s H process_4 B.cyc_254 5%nat 254%nat. rewrite R1, H0, H1. change (norm 5 7) with 7. cbn. rewrite !norm_idempotent. reflexivity.
Qed.
'''


def sys_lemmas():
    L = []
    for op in sorted(set(OPC.values())):
        L += [f'Theorem sys_op{op} s w : B.Lo s -> norm 1 (read_signal (B.D s) 236%nat) = 0 -> norm 32 (read_signal (B.D s) 233%nat) = w -> norm 7 (Z.shiftr w 0) = {op} ->',
              ' norm 1 (read_signal (B.cycle s) 269%nat) = 0 /\\ norm 1 (read_signal (B.cycle s) 270%nat) = 0 /\\ norm 1 (read_signal (B.cycle s) 258%nat) = 0.',
              'Proof. intros H H0 H1 Hop. pose proof (B.resetb_D s H) as R1. pose proof (B.drv_lfp s H) as HL.',
              ' destruct (WI.const_wires _ _ HL) as (_ & _ & _ & _ & _ & _ & _ & C37 & _).',
              ' split; [|split].',
              ' - rise_tree s H process_4 B.cyc_269 1%nat 269%nat. rewrite R1, H0, H1. change (norm 5 0) with 0. rewrite Hop. reflexivity.',
              ' - rise_tree s H process_4 B.cyc_270 1%nat 270%nat. rewrite R1, H0, H1. change (norm 5 0) with 0. rewrite Hop. reflexivity.',
              ' - rise_tree s H process_5 B.cyc_258 1%nat 258%nat. rewrite R1, H1. change (norm 5 0) with 0. rewrite Hop. cbn [boolz Z.eqb norm].',
              '   destruct (B.nbit (read_signal (B.D s) 258%nat)) as [M|M]; rewrite ?M, ?C37; reflexivity.',
              'Qed.']
    return '\n'.join(L)


IMMW = r'''
(** the immediate wire 320 of the decoded word, per format *)
Lemma eval_rimm_B2 s W : eval_expr s (IM.rimm_B2 W) = norm 32 (isa_imm_B (eval_expr s W)).
Proof. unfold IM.rimm_B2, isa_imm_B. CPUImmediateRtlShapes.close_rimm s W. all: finish_imm. all: (replace (i - 12 + 31) with 31 by lia; rewrite Tsign; reflexivity). Qed.
Lemma w233 d w : norm 32 (read_signal d 233%nat) = w -> eval_expr d (EVar 32 233%nat) = w. Proof. intro H. exact H. Qed.
Theorem imm320_U seed d w : CombLFP P seed d -> norm 32 (read_signal d 233%nat) = w -> norm 7 (Z.shiftr w 0) = 55 \/ norm 7 (Z.shiftr w 0) = 23 ->
 norm 32 (read_signal d 320%nat) = norm 32 (isa_imm_U w).
Proof. intros HL H Ho. assert (Ev : forall c, norm 7 (Z.shiftr w 0) = c -> eval_expr d (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = c)
 by (intros c Hc; cbn [eval_expr]; change (norm 5 0) with 0; rewrite H; exact Hc).
 destruct Ho as [Ho|Ho]; [rewrite (IM.imm_u55 seed d w HL H (Ev _ Ho))|rewrite (IM.imm_u23 seed d w HL H (Ev _ Ho))]; rewrite eval_imm_U, (w233 d w H); reflexivity. Qed.
Ltac immw L F H HL Ho := rewrite (L _ _ _ HL H Ho); rewrite F, (w233 _ _ H); reflexivity.
Theorem imm320_J seed d w : CombLFP P seed d -> norm 32 (read_signal d 233%nat) = w -> eval_expr d (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = 111 ->
 norm 32 (read_signal d 320%nat) = norm 32 (isa_imm_J w).
Proof. intros HL H Ho. immw IM.imm_j eval_rimm_J H HL Ho. Qed.
Theorem imm320_jalr seed d w : CombLFP P seed d -> norm 32 (read_signal d 233%nat) = w -> eval_expr d (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = 103 ->
 norm 32 (read_signal d 320%nat) = norm 32 (isa_imm_I w).
Proof. intros HL H Ho. immw IM.imm_jalr eval_rimm_I H HL Ho. Qed.
Theorem imm320_B seed d w : CombLFP P seed d -> norm 32 (read_signal d 233%nat) = w -> eval_expr d (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = 99 ->
 norm 32 (read_signal d 320%nat) = norm 32 (isa_imm_B w).
Proof. intros HL H Ho. immw IM.imm_b eval_rimm_B2 H HL Ho. Qed.
'''


def imm_ar():
    L = []
    for f3 in (0, 2, 3, 4, 6, 7):
        L += [f'Theorem imm320_a{f3} seed d w : CombLFP P seed d -> norm 32 (read_signal d 233%nat) = w -> eval_expr d (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = 19 ->',
              f' eval_expr d (ESel 3 (EVar 32 233%nat) (EConst 5 12)) = {f3} -> norm 32 (read_signal d 320%nat) = norm 32 (isa_imm_I w).',
              f'Proof. intros HL H Ho Hf. rewrite (IM.imm_a{f3} _ _ _ HL H Ho Hf). rewrite eval_rimm_I, (w233 _ _ H). reflexivity. Qed.']
    for f3 in (1, 5):
        L += [f'Theorem imm320_s{f3} seed d w : CombLFP P seed d -> norm 32 (read_signal d 233%nat) = w -> eval_expr d (ESel 7 (EVar 32 233%nat) (EConst 5 0)) = 19 ->',
              f' eval_expr d (ESel 3 (EVar 32 233%nat) (EConst 5 12)) = {f3} -> norm 32 (read_signal d 320%nat) = norm 32 (norm 5 (Z.shiftr w 20)).',
              f'Proof. intros HL H Ho Hf. rewrite (IM.imm_a{f3} _ _ _ HL H Ho Hf). cbn [eval_expr expr_width]. change (norm 5 20) with 20. rewrite H.',
              ' reflexivity. Qed.']
    return '\n'.join(L)


TAILFLD = r'''
(** the immediate clause: decoded field = normalised immediate *)
Lemma shamt_field w : bitSlice w 25 26 = 0 -> norm 32 (norm 5 (Z.shiftr w 20)) = norm 32 (machineIntToShamt (bitSlice w 20 26)).
Proof. intro H. unfold machineIntToShamt, id. f_equal. rewrite (V.bs_norm w 20 26) by lia. apply Z.bits_inj'. intros i Hi.
 rewrite !tbn by lia. change (Z.of_nat 5) with 5. change (Z.of_nat (Z.to_nat (26 - 20))) with 6.
 destruct (Z.ltb_spec0 i 5); destruct (Z.ltb_spec0 i 6); cbn [andb]; try lia; try reflexivity.
 assert (i = 5) by lia. subst i. rewrite Z.shiftr_spec by lia. rewrite (V.bs_norm w 25 26) in H by lia. change (Z.to_nat (26 - 25)) with 1%nat in H.
 assert (T : Z.testbit (norm 1 (Z.shiftr w 25)) 0 = false) by (rewrite H; reflexivity). rewrite tbn in T by lia. rewrite Z.shiftr_spec in T by lia.
 cbn in T |- *. symmetry. exact T. Qed.
Ltac solve_fld := first [ assumption
 | match goal with H : norm 32 (read_signal ?x 250%nat) = norm 32 (norm 5 (Z.shiftr ?w 20)) |- norm 32 (read_signal ?x 250%nat) = _ =>
     rewrite H; apply shamt_field; assumption end
 | match goal with H : norm 32 (read_signal ?x 250%nat) = norm 32 _ |- norm 32 (read_signal ?x 250%nat) = _ => rewrite H; reflexivity end ].
'''


def main():
    tab = cap_table()
    assert set(tab) == set(ALL), sorted(set(ALL) - set(tab))
    body = [HEAD, exc_def(tab), COMMON, sys_lemmas(), IMMW, imm_ar(), TAILFLD]
    for c in ALL:
        body.append(cap_text(c, tab))
    disp = ' | '.join(f'exact (cap_{c} s w _ _{"" if NF[c] == 2 else " _"} HLo H232 H234 H12 Hdec)' for c in ALL)
    body.append('''Theorem cap_all s w i : B.Lo s -> norm 1 (read_signal s 232%nat) = 0 -> norm 1 (read_signal s 234%nat) = 0 ->
 norm 32 (read_signal s 12%nat) = w -> Decode.decode Decode.RV32I w = Decode.IInstruction i ->
 CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true -> DecOut (B.cycle s) (exc i).
Proof. intros HLo H232 H234 H12 Hdec HLg. destruct i.
 all: try (exfalso; cbv in HLg; discriminate HLg).
 all: first [''' + disp + '''].
Qed.''')
    body.append('End Srv32TmplFront.')
    exports = ['front_ctx', 'fld_cap'] + [f'cap_{c}' for c in ALL] + ['cap_all']
    body.append('\n'.join(f'Print Assumptions Srv32TmplFront.{e}.' for e in exports))
    Path(sys.argv[1]).write_text('\n'.join(body) + '\n')


if __name__ == '__main__':
    main()
