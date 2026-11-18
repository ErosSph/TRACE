#!/usr/bin/env python3
"""srv32 closure, back end: one committing EX cycle of a valid token (pulse state S0 or S3), for all 29 classes (one script, the
tools/cpu_tmpl_stop.py pattern).  Emits the Coq module `Srv32TmplBack`:
  * `Outcome s f i`: the WB registers after the cycle (wb_alu2reg, wb_dst_sel, wb_result, wb_mem2reg), the trap wires of the driven
    state, and the redirect bit with the next fetch pc (no redirect: ISA pc + 12 and the ISA successor is pc + 4; redirect: the ISA
    successor);
  * `back_<C>`: from the EX clauses `Srv32TmplFront.exc (C fields)` at the state, the operands (forwarded read ports 245/246 =
    ISA registers) and the pc registers, Outcome.  Script: decode inverse -> lift lemmas of results/r-tmpl-srv32-lift-20261104-a1
    (`<C>_lift_result/_next`), EX next-pc facts of Srv32Ex (`<C>_ex_next`), the trap wires (`ex_trap_valid`), the WB next-value
    lemmas of Srv32Nx -> one premise discharger.
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0."""
import re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
LIFT = ROOT / 'results/r-tmpl-srv32-lift-20261104-a1/Srv32TmplLift.v'
R3 = ['Add', 'Sub', 'Sll', 'Slt', 'Sltu', 'Xor', 'Srl', 'Sra', 'Or', 'And']
I3 = ['Addi', 'Slti', 'Sltiu', 'Xori', 'Ori', 'Andi']
SH = ['Slli', 'Srli', 'Srai']
BR = ['Beq', 'Bne', 'Blt', 'Bge', 'Bltu', 'Bgeu']
ALL = R3 + I3 + SH + ['Lui', 'Auipc', 'Jal', 'Jalr'] + BR
NF = {c: (2 if c in ('Lui', 'Auipc', 'Jal') else 3) for c in ALL}


def kind289(c):
    return {'Lui': 'lui', 'Auipc': 'auipc', 'Jal': 'jal', 'Jalr': 'jalr'}.get(c, 'none' if c in BR else 'alu')


def class_text(c):
    n = NF[c]
    fs = ' '.join(f'a{k}' for k in range(n))
    ctor = f'(Decode.{c} {fs})'
    L = [f'Theorem back_{c} s (f:FormalSpec.State) w {fs} : B.Lo s -> norm 1 (read_signal s 232%nat) = 0 -> norm 1 (read_signal s 295%nat) = 0 ->',
         ' norm 1 (read_signal s 296%nat) = 0 -> norm 1 (read_signal s 292%nat) = 0 ->',
         f' FR.DecOut s (FR.exc {ctor}) -> Decode.decode Decode.RV32I w = Decode.IInstruction {ctor} ->',
         ' norm 32 (read_signal s 241%nat) = uw (getPc f) -> norm 32 (read_signal s 239%nat) = norm 32 (uw (getPc f) + 8) ->',
         ' norm 32 (read_signal (B.D s) 245%nat) = V.isa_view f (norm 5 (read_signal s 252%nat)) ->',
         ' norm 32 (read_signal (B.D s) 246%nat) = V.isa_view f (norm 5 (read_signal s 253%nat)) ->',
         f' LI.ipc f {ctor} mod 4 = 0 -> LI.jalr_ok {ctor} -> uw (getPc f) mod 4 = 0 -> Outcome s f {ctor}.',
         'Proof. intros HLo H232 H295 H296 H292 K Hdec Hpc Hfe O1 O2 Hm Hj Hp4.',
         f' destruct (CI.inv_{c} w {fs} Hdec) as [E Hb]. split_all. cbn [LI.jalr_ok] in Hj.',
         ' destruct (bctx s HLo H232 H295 H296 H292) as (HL & D272 & D237 & D238 & D236 & C32 & C23 & C24 & C25).',
         ' pose proof (dec_d s _ HLo K) as FD. cbv [FR.exc] in K, FD. explode K. explode FD.',
         ' assert (D241 : norm 32 (read_signal (B.D s) 241%nat) = uw (getPc f)) by (rewrite (dreg s 241%nat ltac:(inn)); exact Hpc).',
         ' assert (D239 : norm 32 (read_signal (B.D s) 239%nat) = norm 32 (uw (getPc f) + 8)) by (rewrite (dreg s 239%nat ltac:(inn)); exact Hfe).',
         ' pose proof (Pv.alu_op1_copy _ _ _ HL O1) as P247. rewrite view_norm in P247.',
         ' assert (D281 : norm 1 (read_signal (B.D s) 281%nat) = 0) by (apply (WI.ld_m2r0 _ _ HL); fact).',
         ' assert (D258 : norm 1 (read_signal (B.D s) 258%nat) = 0) by fact.']
    uses_imm = c in I3 + SH + ['Jalr']
    if c in R3 or c in BR:
        L.append(' pose proof (Pv.alu_op2_reg _ _ _ HL ltac:(fact) O2) as P248. rewrite view_norm in P248.')
    elif uses_imm:
        L.append(' pose proof (Pv.alu_op2_imm _ _ (norm 32 a2) HL ltac:(fact) ltac:(fact)) as P248. rewrite norm_idempotent in P248.')
    # lift lemmas
    if c in R3:
        L.append(f' pose proof (LT.{c}_lift_result _ _ f a0 a1 a2 HL) as R. discharge R.')
    elif c in I3:
        L.append(f' pose proof (LT.{c}_lift_result _ _ f a0 a1 a2 HL) as R. discharge R.')
    elif c in SH:
        L.append(f' pose proof (LT.{c}_lift_result _ _ f a0 a1 a2 (norm 32 a2) HL) as R. discharge R.')
    elif c in ('Lui', 'Auipc', 'Jal'):
        L.append(f' pose proof (LT.{c}_lift_result _ _ f a0 a1 HL) as R. discharge R.')
    elif c == 'Jalr':
        L.append(f' pose proof (LT.{c}_lift_result _ _ f a0 a1 a2 HL) as R. discharge R.')
    if c in R3 + I3 + SH + ['Lui', 'Auipc']:
        L.append(f' pose proof (Pv.{c}_ex_next _ _ (norm 32 (uw (getPc f) + 8)) HL) as N. discharge N. destruct N as (N324 & N325 & N280).')
    elif c == 'Jal':
        L.append(f' pose proof (LT.Jal_lift_next _ _ f a0 a1 HL) as N. discharge N. destruct N as (N324 & N325 & N280).')
    elif c == 'Jalr':
        L.append(f' pose proof (LT.Jalr_lift_next _ _ f a0 a1 a2 HL) as N. discharge N. destruct N as (N324 & N325 & N280).')
    else:
        L.append(f' pose proof (LT.{c}_lift_next _ _ f a0 a1 a2 (norm 32 (uw (getPc f) + 8)) HL) as N. discharge N. destruct N as (N325 & N324t & N324n).')
    # trap wires, WB next values
    if c in BR:
        f3 = {'Beq': 0, 'Bne': 1, 'Blt': 4, 'Bge': 5, 'Bltu': 6, 'Bgeu': 7}[c]
        L += [f' assert (N280 : norm 1 (read_signal (B.D s) 280%nat) = 0) by (exact (IM.br_ill{f3} _ _ HL D272 ltac:(fact) ltac:(fact) ltac:(fact) ltac:(fact))).',
              ' match type of N325 with context [boolz (isa_branch_guard ?i ?x ?y)] => destruct (isa_branch_guard i x y) eqn:G end.',
              '  + specialize (N324t eq_refl). pose proof (trap0 s HLo _ _ HL D272 ltac:(fact) N280 D258 ltac:(fact) ltac:(fact) ltac:(fact) C23 C24 C25 ltac:(fact) N324t',
              '      ltac:(rewrite norm2_mod; exact Hm)) as [T274 T275].',
              '    branch_out s HLo D237 D272 D258 D281 N325 T274 T275 N324t G.',
              '  + specialize (N324n eq_refl). pose proof (trap0 s HLo _ _ HL D272 ltac:(fact) N280 D258 ltac:(fact) ltac:(fact) ltac:(fact) C23 C24 C25 ltac:(fact) N324n',
              '      ltac:(apply np_al; exact Hp4)) as [T274 T275].',
              '    branch_out_n s HLo D237 D272 D258 D281 N325 T274 T275 N324n G Hp4.',
              'Qed.']
        return '\n'.join(L)
    if c in ('Jal', 'Jalr'):
        L += [' pose proof (trap0 s HLo _ _ HL D272 ltac:(fact) N280 D258 ltac:(fact) ltac:(fact) ltac:(fact) C23 C24 C25 ltac:(fact) N324',
              '   ltac:(rewrite norm2_mod; exact Hm)) as [T274 T275].',
              f' jump_out s HLo D237 D272 D258 D281 R N325 T274 T275 N324 Hm NX.nx_289_{c.lower()}_D.', 'Qed.']
        return '\n'.join(L)
    L += [' pose proof (trap0 s HLo _ _ HL D272 ltac:(fact) N280 D258 ltac:(fact) ltac:(fact) ltac:(fact) C23 C24 C25 ltac:(fact) N324',
          '   ltac:(apply np_al; exact Hp4)) as [T274 T275].',
          f' data_out s HLo D237 D272 D258 D281 R N325 T274 T275 N324 Hp4 NX.nx_289_{kind289(c)}_D.', 'Qed.']
    return '\n'.join(L)


HEAD = r'''(** srv32 closure, back end: one committing EX cycle of a valid token for all 29 classes (tools/cpu_tmpl_srv32_back.py).
    proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import coqutil.Z.BitOps Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVSeqTree Lang.ExtendedSVBankAlignment
 Lang.ExtendedSVRootProjection Ex.External.CPUImmediateShapes Ex.External.CPUISARegView Ex.External.CPUClassTableInverse
 Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PBranchISACondition Ex.RvCore.FormalSpec
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Naive coqutil.Map.Interface coqutil.Map.Z_keyed_SortedListMap
 riscv.Utility.Utility riscv.Utility.Words32Naive riscv.Utility.DefaultMemImpl32 riscv.Utility.MkMachineWidth riscv.Spec.Decode Ex.External.CPUJumpFamilyProgramDomain Srv32.Srv32AST
 TmplSrv32Base.Srv32Base TmplSrv32Wire.Srv32Wire TmplSrv32Nx.Srv32Nx TmplSrv32Ex.Srv32Ex TmplLiftIsa.TmplLiftIsa TmplSrv32Lift.Srv32TmplLift
 TmplSrv32Front.Srv32TmplFront TmplSrv32Imm.Srv32TmplImm.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankAlignment ExtendedSVRootProjection ExtendedSVSeqTree CPUImmediateShapes CV32E40PReq40StateRel CV32E40PBranchISACondition Srv32AST.
Local Open Scope Z_scope.
Local Opaque PhaseSemantics phase_driven_state.
Module Srv32TmplBack.
Notation P := srv32_program (only parsing).
Module B := TmplSrv32Base.Srv32Base.Srv32Base.
Module WI := TmplSrv32Wire.Srv32Wire.Srv32Wire.
Module NX := TmplSrv32Nx.Srv32Nx.Srv32Nx.
Module Pv := TmplSrv32Ex.Srv32Ex.Srv32Ex.
Module LI := TmplLiftIsa.TmplLiftIsa.TmplLiftIsa.
Module LT := TmplSrv32Lift.Srv32TmplLift.Srv32TmplLift.
Module FR := TmplSrv32Front.Srv32TmplFront.Srv32TmplFront.
Module IM := TmplSrv32Imm.Srv32TmplImm.Srv32TmplImm.
Module CI := CPUClassTableInverse.CPUClassTableInverse.
Module V := CPUISARegView.CPUISARegView.
Notation uw := word.unsigned.
Ltac pick_in := repeat first [apply in_eq | apply in_cons].
Lemma inb_In (r:nat) l : existsb (Nat.eqb r) l = true -> In r l.
Proof. intro H. apply existsb_exists in H as [x [Hx E]]. apply Nat.eqb_eq in E. subst x. exact Hx. Qed.
Ltac inn := apply inb_In; vm_compute; reflexivity.
Lemma decout_cons s t l : FR.DecOut s (t :: l) -> norm (snd (fst t)) (read_signal s (fst (fst t))) = snd t /\ FR.DecOut s l.
Proof. intro K. split; [exact (K t (or_introl eq_refl))|intros u Hu; exact (K u (or_intror Hu))]. Qed.
Ltac explode K := repeat (let F := fresh "F" in apply decout_cons in K; destruct K as [F K]; cbn [fst snd] in F).
Ltac split_all := repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac subst_fields := repeat match goal with H : ?a = bitSlice _ _ _ |- _ => is_var a; subst a
 | H : ?a = signExtend _ _ |- _ => is_var a; subst a | H : ?a = machineIntToShamt _ |- _ => is_var a; subst a end.

(** what a committing valid token leaves in WB, the trap wires, and the next fetch pc *)
Definition Outcome (s:State) (f:FormalSpec.State) (i:Decode.InstructionI) : Prop :=
 norm 1 (read_signal (B.cycle s) 289%nat) = (if LI.dwr i then 1 else 0) /\
 (LI.dwr i = true -> norm 5 (read_signal (B.cycle s) 294%nat) = LI.drd i /\ norm 32 (read_signal (B.cycle s) 290%nat) = uw (LI.dval f i)) /\
 norm 1 (read_signal (B.cycle s) 293%nat) = 0 /\ norm 1 (read_signal (B.D s) 274%nat) = 0 /\ norm 1 (read_signal (B.D s) 275%nat) = 0 /\
 ((norm 1 (read_signal (B.cycle s) 295%nat) = 0 /\ LI.ipc f i = norm 32 (uw (getPc f) + 4) /\ norm 32 (read_signal (B.cycle s) 239%nat) = norm 32 (uw (getPc f) + 12))
  \/ (norm 1 (read_signal (B.cycle s) 295%nat) = 1 /\ norm 32 (read_signal (B.cycle s) 239%nat) = LI.ipc f i)).

(** ---- class independent ---- *)
Lemma unw_regs : forallb (comb_root_unwrittenb P) [232;234;239;240;241;244;12;289;290;292;293;294;295;296;297;298;299;250;251;252;253;254;255;256;257;258;261;262;264;265;266;267;268;269;270;279;288]%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma dreg s r : In r [232;234;239;240;241;244;12;289;290;292;293;294;295;296;297;298;299;250;251;252;253;254;255;256;257;258;261;262;264;265;266;267;268;269;270;279;288]%nat ->
 read_signal (B.D s) r = read_signal s r.
Proof. intro Hr. unfold B.D. apply driven_unchanged.
 - pose proof unw_regs as U. rewrite forallb_forall in U. exact (U r Hr).
 - cbn [B.rise changed_signal]. intro E. subst r. cbn in Hr. repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]). exact Hr. Qed.
Lemma dec_d s i : B.Lo s -> FR.DecOut s (FR.exc i) -> FR.DecOut (B.D s) (FR.exc i).
Proof. intros _ K t Ht. rewrite dreg; [exact (K t Ht)|]. destruct i; cbv [FR.exc] in Ht; try contradiction;
 repeat (destruct Ht as [<-|Ht]; [cbn [fst]; inn|]); contradiction. Qed.
Lemma bctx s : B.Lo s -> norm 1 (read_signal s 232%nat) = 0 -> norm 1 (read_signal s 295%nat) = 0 -> norm 1 (read_signal s 296%nat) = 0 ->
 norm 1 (read_signal s 292%nat) = 0 ->
 CombLFP P (write_signal s 0%nat 1) (B.D s) /\ norm 1 (read_signal (B.D s) 272%nat) = 0 /\ norm 1 (read_signal (B.D s) 237%nat) = 0 /\
 norm 1 (read_signal (B.D s) 238%nat) = 0 /\ norm 1 (read_signal (B.D s) 236%nat) = 0 /\ norm 1 (read_signal (B.D s) 32%nat) = 1 /\
 norm 1 (read_signal (B.D s) 23%nat) = 0 /\ norm 1 (read_signal (B.D s) 24%nat) = 0 /\ norm 1 (read_signal (B.D s) 25%nat) = 0.
Proof. intros HLo H232 H295 H296 H292. pose proof (B.drv_lfp s HLo) as HL.
 assert (D232 : norm 1 (read_signal (B.D s) 232%nat) = 0) by (rewrite dreg by inn; exact H232).
 assert (D295 : norm 1 (read_signal (B.D s) 295%nat) = 0) by (rewrite dreg by inn; exact H295).
 assert (D296 : norm 1 (read_signal (B.D s) 296%nat) = 0) by (rewrite dreg by inn; exact H296).
 destruct (WI.stall_wires _ _ _ _ _ HL D232 eq_refl eq_refl eq_refl) as (S236 & S237 & S238 & _ & _).
 destruct (WI.const_wires _ _ HL) as (_ & C23 & C24 & C25 & _ & _ & C32 & _ & _).
 refine (conj HL (conj _ (conj S237 (conj S238 (conj S236 (conj C32 (conj C23 (conj C24 C25)))))))).
 rewrite (Pv.ex_flush_or _ _ _ _ HL D295 D296). reflexivity. Qed.
Lemma view_norm (f:FormalSpec.State) r : norm 32 (V.isa_view f r) = V.isa_view f r.
Proof. rewrite <- V.view_formal. rewrite norm_mod. apply Z.mod_small. pose proof (word.unsigned_range (formal_register_word f r)) as H. exact H. Qed.
Lemma norm2_mod x : norm 2 x = x mod 4. Proof. rewrite norm_mod. reflexivity. Qed.
Lemma m4 v : (v mod 4294967296) mod 4 = v mod 4.
Proof. symmetry. apply Znumtheory.Zmod_div_mod; [lia|lia|exists 1073741824; reflexivity]. Qed.
Lemma np_al p : p mod 4 = 0 -> norm 2 (norm 32 (Z.add 4 (norm 32 (p + 8)))) = 0.
Proof. intro H. rewrite !norm_mod. change (2 ^ Z.of_nat 2) with 4. change (2 ^ Z.of_nat 32) with 4294967296.
 rewrite m4. rewrite Z.add_mod by lia. rewrite m4. rewrite (Z.add_mod p 8) by lia. rewrite H. reflexivity. Qed.
Theorem trap0 s (HLo:B.Lo s) seed np (HL : CombLFP P seed (B.D s)) : norm 1 (read_signal (B.D s) 272%nat) = 0 -> norm 1 (read_signal (B.D s) 279%nat) = 0 ->
 norm 1 (read_signal (B.D s) 280%nat) = 0 -> norm 1 (read_signal (B.D s) 258%nat) = 0 -> norm 1 (read_signal (B.D s) 257%nat) = 0 ->
 norm 1 (read_signal (B.D s) 269%nat) = 0 -> norm 1 (read_signal (B.D s) 270%nat) = 0 -> norm 1 (read_signal (B.D s) 23%nat) = 0 ->
 norm 1 (read_signal (B.D s) 24%nat) = 0 -> norm 1 (read_signal (B.D s) 25%nat) = 0 -> norm 1 (read_signal (B.D s) 262%nat) = 0 ->
 norm 32 (read_signal (B.D s) 324%nat) = np -> norm 2 np = 0 -> norm 1 (read_signal (B.D s) 274%nat) = 0 /\ norm 1 (read_signal (B.D s) 275%nat) = 0.
Proof. intros. exact (Pv.ex_trap_valid seed (B.D s) np _ _ _ _ HL H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 eq_refl eq_refl eq_refl eq_refl H11). Qed.
'''

HELP = r'''
Lemma clear0 np : norm 2 np = 0 -> norm 32 (Z.shiftl (Z.shiftr np 1) 1) = norm 32 np.
Proof. intro H. f_equal. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2.
 rewrite norm_mod in H. change (2 ^ Z.of_nat 2) with 4 in H.
 assert (E : np mod 2 = 0) by (rewrite (Znumtheory.Zmod_div_mod 2 4 np) by (try lia; exists 2; reflexivity); rewrite H; reflexivity).
 pose proof (Z.div_mod np 2 ltac:(lia)) as D. rewrite E in D. lia. Qed.
Ltac fact := assumption.
Ltac solve_prem := first [ fact | assumption | reflexivity
 | match goal with |- norm 32 (read_signal _ 247%nat) = uw (formal_register_word ?f ?x) =>
     match goal with P : norm 32 (read_signal _ 247%nat) = V.isa_view f (norm 5 (read_signal ?s 252%nat)) |- _ =>
       rewrite P; match goal with F : norm 5 (read_signal s 252%nat) = x |- _ => rewrite F end; symmetry; apply V.view_formal end end
 | match goal with |- norm 32 (read_signal _ 248%nat) = uw (formal_register_word ?f ?x) =>
     match goal with P : norm 32 (read_signal _ 248%nat) = V.isa_view f (norm 5 (read_signal ?s 253%nat)) |- _ =>
       rewrite P; match goal with F : norm 5 (read_signal s 253%nat) = x |- _ => rewrite F end; symmetry; apply V.view_formal end end
 | match goal with |- norm 32 (read_signal _ 248%nat) = _ => match goal with P : norm 32 (read_signal _ 248%nat) = _ |- _ => rewrite P; reflexivity end end
 | match goal with |- norm 5 (norm 32 ?a) = ?a => match goal with H : a = machineIntToShamt (bitSlice ?w 20 26) |- _ => rewrite H; apply (proj1 (shamt_ok w ltac:(assumption))) end end
 | match goal with |- 0 <= ?a < 32 => match goal with H : a = machineIntToShamt (bitSlice ?w 20 26) |- _ => rewrite H; apply (proj2 (shamt_ok w ltac:(assumption))) end end
 | match goal with |- LI.ipc _ _ mod 2 = 0 => apply mod4_2; assumption end ].
Ltac discharge K := repeat (lazymatch type of K with ?A -> _ => let H := fresh "Hp" in assert (H : A) by solve_prem; specialize (K H); clear H end).
'''


def main():
    text = LIFT.read_text()
    body = [HEAD, HELP_PRE, HELP, OUT]
    for c in ALL:
        body.append(class_text(c))
    disp = ' | '.join(f'exact (back_{c} s f w _ _{"" if NF[c] == 2 else " _"} HLo H232 H295 H296 H292 K Hdec Hpc Hfe O1 O2 Hm Hj Hp4)' for c in ALL)
    body.append('''Theorem back_all s (f:FormalSpec.State) w i : B.Lo s -> norm 1 (read_signal s 232%nat) = 0 -> norm 1 (read_signal s 295%nat) = 0 ->
 norm 1 (read_signal s 296%nat) = 0 -> norm 1 (read_signal s 292%nat) = 0 ->
 FR.DecOut s (FR.exc i) -> Decode.decode Decode.RV32I w = Decode.IInstruction i ->
 CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true ->
 norm 32 (read_signal s 241%nat) = uw (getPc f) -> norm 32 (read_signal s 239%nat) = norm 32 (uw (getPc f) + 8) ->
 norm 32 (read_signal (B.D s) 245%nat) = V.isa_view f (norm 5 (read_signal s 252%nat)) ->
 norm 32 (read_signal (B.D s) 246%nat) = V.isa_view f (norm 5 (read_signal s 253%nat)) ->
 LI.ipc f i mod 4 = 0 -> LI.jalr_ok i -> uw (getPc f) mod 4 = 0 -> Outcome s f i.
Proof. intros HLo H232 H295 H296 H292 K Hdec HLg Hpc Hfe O1 O2 Hm Hj Hp4. destruct i.
 all: try (exfalso; cbv in HLg; discriminate HLg).
 all: first [''' + disp + '''].
Qed.''')
    body.append('End Srv32TmplBack.')
    exports = ['bctx', 'trap0'] + [f'back_{c}' for c in ALL] + ['back_all']
    body.append('\n'.join(f'Print Assumptions Srv32TmplBack.{e}.' for e in exports))
    Path(sys.argv[1]).write_text('\n'.join(body) + '\n')


HELP_PRE = r'''
Lemma FR_fact s r w v l : FR.DecOut s l -> In ((r,w),v) l -> norm w (read_signal s r) = v.
Proof. intros K H. exact (K _ H). Qed.
Lemma mod4_2 x : x mod 4 = 0 -> x mod 2 = 0.
Proof. intro H. rewrite (Znumtheory.Zmod_div_mod 2 4 x) by (try lia; exists 2; reflexivity). rewrite H. reflexivity. Qed.
Lemma shamt_ok w : bitSlice w 25 26 = 0 -> norm 5 (norm 32 (machineIntToShamt (bitSlice w 20 26))) = machineIntToShamt (bitSlice w 20 26) /\
 0 <= machineIntToShamt (bitSlice w 20 26) < 32.
Proof. intro H. pose proof (V.shamt_imm w H) as E. unfold machineIntToShamt, id in *.
 assert (B5 : 0 <= bitSlice w 20 26 < 32).
 { rewrite <- E. pose proof (norm_bounds 5 (norm 32 (isa_imm_I w))) as X. change (2 ^ Z.of_nat 5) with 32 in X. exact X. }
 split; [|exact B5]. rewrite !norm_mod. rewrite (Z.mod_small _ (2 ^ Z.of_nat 32)) by (change (2 ^ Z.of_nat 32) with 4294967296; lia).
 apply Z.mod_small. change (2 ^ Z.of_nat 5) with 32. exact B5. Qed.
'''

OUT = r'''
Lemma np12 p : norm 32 (Z.add 4 (norm 32 (p + 8))) = norm 32 (p + 12).
Proof. rewrite !norm_mod. rewrite Z.add_mod_idemp_r by (change (2 ^ Z.of_nat 32) with 4294967296; lia). f_equal. lia. Qed.
Lemma ipc_norm (f:FormalSpec.State) i : norm 32 (LI.ipc f i) = LI.ipc f i.
Proof. destruct i; cbn [LI.ipc]; try apply norm_idempotent; try (match goal with |- context [if ?g then _ else _] => destruct g end; apply norm_idempotent).
 rewrite <- LI.clear0_jalr. apply norm_idempotent. Qed.
Ltac out_common s HLo D237 D258 :=
 unfold Outcome; cbn [LI.dwr LI.drd LI.dval];
 refine (conj _ (conj _ (conj (NX.nx_293_D s 0 HLo D237 D258) _))).
Ltac data_out s HLo D237 D272 D258 D281 R N325 T274 T275 N324 Hp4 K289 :=
 out_common s HLo D237 D258;
 [ apply K289; first [exact HLo | assumption | fact]
 | intros _; split; [apply (NX.nx_294_D s); [exact HLo|exact D237|fact] | apply (NX.nx_290_D s); [exact HLo|exact D237|exact R]]
 | refine (conj T274 (conj T275 (or_introl (conj _ (conj eq_refl _)))));
   [ rewrite (NX.nx_295_D s 0 0 HLo D237 N325 T274); reflexivity
   | rewrite (NX.nx_239_nf_D s _ HLo D237 D272 T274 N324); rewrite clear0 by (apply np_al; exact Hp4); rewrite norm_idempotent; apply np12 ] ].
Ltac jump_out s HLo D237 D272 D258 D281 R N325 T274 T275 N324 Hm K289 :=
 out_common s HLo D237 D258;
 [ apply K289; first [exact HLo | assumption | fact]
 | intros _; split; [apply (NX.nx_294_D s); [exact HLo|exact D237|fact] | apply (NX.nx_290_D s); [exact HLo|exact D237|exact R]]
 | refine (conj T274 (conj T275 (or_intror (conj _ _))));
   [ rewrite (NX.nx_295_D s 1 0 HLo D237 N325 T274); reflexivity
   | rewrite (NX.nx_239_nf_D s _ HLo D237 D272 T274 N324); rewrite clear0 by (rewrite norm2_mod; exact Hm); apply ipc_norm ] ].
Ltac branch_out s HLo D237 D272 D258 D281 N325 T274 T275 N324 G :=
 try (rewrite G in N325); cbn [boolz] in N325;
 out_common s HLo D237 D258;
 [ apply NX.nx_289_none_D; first [exact HLo | assumption | fact]
 | let H := fresh in intro H; discriminate H
 | refine (conj T274 (conj T275 (or_intror (conj _ _))));
   [ rewrite (NX.nx_295_D s 1 0 HLo D237 N325 T274); reflexivity
   | rewrite (NX.nx_239_nf_D s _ HLo D237 D272 T274 N324); rewrite clear0 by (rewrite norm2_mod; assumption); apply ipc_norm ] ].
Ltac branch_out_n s HLo D237 D272 D258 D281 N325 T274 T275 N324 G Hp4 :=
 try (rewrite G in N325); cbn [boolz] in N325;
 out_common s HLo D237 D258;
 [ apply NX.nx_289_none_D; first [exact HLo | assumption | fact]
 | let H := fresh in intro H; discriminate H
 | refine (conj T274 (conj T275 (or_introl (conj _ (conj _ _)))));
   [ rewrite (NX.nx_295_D s 0 0 HLo D237 N325 T274); reflexivity
   | cbn [LI.ipc]; rewrite G; reflexivity
   | rewrite (NX.nx_239_nf_D s _ HLo D237 D272 T274 N324); rewrite clear0 by (apply np_al; exact Hp4); rewrite norm_idempotent; apply np12 ] ].
'''

if __name__ == '__main__':
    main()
