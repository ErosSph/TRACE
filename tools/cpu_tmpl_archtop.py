#!/usr/bin/env python3
"""goal_arch assembly (module DarkTmplArch): the architectural relation `tmpl_arch`, its reset instance, and the two
step theorems `arch_commit` / `arch_bubble`, generated from the class table.

* arch_commit: a committing cycle (FLUSH=0). The ISA post state is the family post state (CPUJumpFamilyPostShape),
  the class is found by decoding the normalised ROM word (checked_decode_normalized + the slot invariant), and the
  per-class lemma rfarch_C (module TmplDarkArchRF) gives the register-bank relation and the RAM frame.
* arch_bubble: FLUSH != 0 (also all XRES cycles): bank and RAM are kept (module TmplDarkBubble).
The slot invariant and the PC-chain facts are premises here; the D step takes them from the cursor invariant.
"""
import sys
import json
from pathlib import Path
import cpu_tmpl_controls as ctl
import cpu_tmpl_params as PR
import cpu_isa_classes as isa
import cpu_class_table as ct
import cpu_tmpl_bubble as bub
import cpu_tmpl_arch as arch

HDR = arch.HDR.replace('Require Import coqutil.Z.BitOps', 'Require Import Ex.External.CPUJumpFamilyPostShape Ex.External.CV32E40PDataOpProgramScope Ex.External.CPUISABranchFamilyEffects Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUProgramDomain Ex.External.CPUJumpFamilyProgramExecution Ex.External.DarkRISCV38DerivedProgramDomain Ex.External.CPUByteBankArchitecture\n TmplDarkArchRF.DarkTmplArchRF TmplDarkBubble.DarkTmplBubble Lang.ExtendedSVStallFlush coqutil.Z.BitOps', 1)
HDR += """Import ExtendedSVStallFlush CPUProgramDomain DarkRISCV38DerivedProgramDomain CPUByteBankArchitecture.
Module ARF := TmplDarkArchRF.DarkTmplArchRF.DarkTmplArchRF.
Module BUB := TmplDarkBubble.DarkTmplBubble.DarkTmplBubble.
Module JF := CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.
Module PS := CPUJumpFamilyPostShape.CPUJumpFamilyPostShape.
Notation dec_norm := (Decode.decode Decode.RV32I).
"""

CORE = r"""
Definition jf_holds(image:list Z)(a:FormalSpec.State):Prop:=exists index,JF.AtProgram image index a.
Definition jf_domain(image:list Z)(HC:JF.check_program image=true):Domain(initial image):=
 {|holds:=jf_holds image;initial_holds:=ex_intro _ 0%nat(CPUJumpFamilyProgramExecution.CPUJumpFamilyProgramExecution.checked_original_initial image HC);
   run1_preserves:=fun a b HA HR=>match HA with ex_intro _ index HAt=>match JF.checked_run1_stays_in_program image index a b HC HAt HR with ex_intro _ nx(conj HN _)=>ex_intro _ nx HN end end|}.
Definition tmpl_arch(image:list Z)(HC:JF.check_program image=true)(s:Runtime)(isa:FormalSpec.State):Prop:=
 RF.RFZero(read_signal(rtl s)@id:BANK@%nat)isa /\ getInstMem isa=FormalSpec.formal_initial_imem(image_program image) /\ BytesRelated 128(ram s)(getDataMem isa) /\
 holds(initial image)(jf_domain image HC)isa /\ (norm 1(read_signal(rtl s)@id:RESET_REG@%nat)=1 -> isa=initial image).
Theorem rfzero_initial image:RF.RFZero(read_signal(rtl actual_reset)@id:BANK@%nat)(initial image).
Proof. pose proof(target_initial_architecture image)as H. unfold ArchRelated in H. destruct H as[_[_[HRF _]]].
 split;[exact HRF|]. unfold actual_reset. cbn[rtl]. vm_compute. reflexivity. Qed.
Theorem tmpl_arch_reset image HC:tmpl_arch image HC actual_reset(initial image).
Proof. pose proof(target_initial_architecture image)as H. unfold ArchRelated in H. destruct H as[_[_[_[HI HR]]]].
 split;[exact(rfzero_initial image)|]. split;[exact HI|]. split;[exact HR|]. split;[exact(initial_holds(initial image)(jf_domain image HC))|].
 intros _. reflexivity. Qed.
Lemma isa_view_initial image i:isa_view(initial image)i=0.
Proof. unfold isa_view,regs_view. destruct(Z.eqb i 0);[reflexivity|]. cbn[getRegs initial FormalSpec.initial_state]. rewrite map.get_empty. reflexivity. Qed.
Lemma flush_cases v:norm 2 v<>0 -> norm 2 v=1 \/ norm 2 v=2 \/ norm 2 v=3.
Proof. pose proof(ExtendedSVBankAlignment.norm_bounds 2 v)as H. change(2^Z.of_nat 2)with 4 in H. lia. Qed.

Lemma bubble_rf image s r:CY.env_ok s -> RF.RFZero(read_signal(rtl s)@id:BANK@%nat)r ->
 (norm 1(read_signal(rtl s)@id:RESET_REG@%nat)=1 -> r=initial image) -> norm 2(read_signal(rtl s)@id:VALID_CTR@%nat)<>0 ->
 RF.RFZero(read_signal(rtl(actual_cycle image s))@id:BANK@%nat)r /\ ram(actual_cycle image s)=ram s.
Proof. intros HE HZ Hx HF.
 pose proof(actual_driven_is_LFP rise(rtl s))as HL. set(d:=phase_driven_state P rise(rtl s))in *.
 set(seed:=write_signal(rtl s)(changed_signal rise)(new_value rise))in *.
 assert(Hdr:forall R,comb_root_unwrittenb P R=true -> R<>@id:CLK@%nat -> read_signal d R=read_signal(rtl s)R)by(intros R H1 H2;exact(CY.driven_read(rtl s)R H1 H2)).
 assert(Hbank:read_signal d @id:BANK@%nat=read_signal(rtl s)@id:BANK@%nat)by(apply Hdr;[vm_compute;reflexivity|discriminate]).
 assert(HZd:RF.RFZero(read_signal d @id:BANK@%nat)r)by(rewrite Hbank;exact HZ).
 assert(Hx1:forall v,norm 1(read_signal(rtl s)@id:RESET_REG@%nat)=v -> norm 1(read_signal d @id:RESET_REG@%nat)=v)by(intros v H;rewrite(Hdr @id:RESET_REG@%nat CY.comb_unw_@id:RESET_REG@ ltac:(discriminate));exact H).
 assert(Hf1:forall v,norm 2(read_signal(rtl s)@id:VALID_CTR@%nat)=v -> norm 2(read_signal d @id:VALID_CTR@%nat)=v)by(intros v H;rewrite(Hdr @id:VALID_CTR@%nat CY.comb_unw_@id:VALID_CTR@ ltac:(discriminate));exact H).
 assert(Hhl:norm 1(read_signal d @id:STALL@%nat)=0)by exact(CY.driven_halt s HE).
 assert(Hcore:(norm 1(read_signal(rtl s)@id:RESET_REG@%nat)=0 -> norm 32(eval_expr d CT.orig_t_rf_value)=if Z.eqb 0(norm 5(read_signal d @id:RD@%nat))then 0 else norm 32(read_signal d @id:DREG@%nat)) /\
   (norm 1(read_signal(rtl s)@id:RESET_REG@%nat)=1 -> norm 32(eval_expr d CT.orig_t_rf_value)=0) /\ norm 1(read_signal d @id:DBUS_REQ@%nat)=0).
 { destruct(one_bit_cases(rtl s)@id:RESET_REG@%nat)as[X|X];destruct(flush_cases _ HF)as[K|[K|K]].
@BUBCASES@ }
 destruct Hcore as[Hc0[Hc1 Hd8]].
 refine(conj _(ARF.ram_keep image s Hd8)).
 pose proof(RF.cycle_rf_rel image s(RF.isa_view r)HE(RF.rfzero_to_rfrel _ _ HZ))as Hrel.
 apply RF.rfrel_to_rfzero.
 destruct(one_bit_cases(rtl s)@id:RESET_REG@%nat)as[X|X].
 - assert(Hv:norm 32(eval_expr d CT.orig_t_rf_value)=isa_view r(norm 5(read_signal d @id:RD@%nat))).
   { rewrite(Hc0 X). destruct(Z.eqb 0(norm 5(read_signal d @id:RD@%nat)))eqn:E0.
     - apply Z.eqb_eq in E0. rewrite <- E0. reflexivity.
     - rewrite(RF.operand_isa_68 seed d r HL HZd),ARF.isa_view_eq. reflexivity. }
   eapply(rfrel_after_keep _ r r(norm 5(read_signal d @id:RD@%nat)));[exact Hrel|exact Hv|reflexivity].
 - assert(Hv:norm 32(eval_expr d CT.orig_t_rf_value)=isa_view r(norm 5(read_signal d @id:RD@%nat))).
   { rewrite(Hc1 X). rewrite(Hx X). rewrite isa_view_initial. reflexivity. }
   eapply(rfrel_after_keep _ r r(norm 5(read_signal d @id:RD@%nat)));[exact Hrel|exact Hv|reflexivity]. Qed.


Lemma commit_rf image (HC:JF.check_program image=true) s r post index:CY.env_ok s -> RF.RFZero(read_signal(rtl s)@id:BANK@%nat)r -> IV.CoherentFields(rtl s) ->
 norm 1(read_signal(rtl s)@id:RESET_REG@%nat)=0 -> norm 2(read_signal(rtl s)@id:VALID_CTR@%nat)=0 ->
 norm 32(read_signal(rtl s)@id:SLOT_WORD@%nat)=norm 32(rom image(norm 32(read_signal(rtl s)@id:EXEC_PC@%nat))) ->
 norm 32(read_signal(rtl s)@id:EXEC_PC@%nat)=word.unsigned(getPc r) ->
 norm 32(read_signal(rtl s)@id:SLOT_PC@%nat)=norm 32(word.unsigned(getPc r)+4) ->
 JF.AtProgram image index r -> FormalSpec.run1 r=(Some tt,post) ->
 RF.RFZero(read_signal(rtl(actual_cycle image s))@id:BANK@%nat)post /\ ram(actual_cycle image s)=ram s.
Proof. intros HE HZ HC' HX HF Hslot Hpc Hlink HAt Hrun.
 destruct(PS.checked_post_shape image index r post HC HAt Hrun)as[i[HD Hcases]].
 destruct(JF.checked_current_instruction image index r HC HAt)as[i0[HD0[HCur[HL0 _]]]].
 assert(Hii:i0=i)by(rewrite HD in HD0;congruence). subst i0.
 pose proof(PS.checked_decode_normalized image index r i HC HAt HCur)as HDw.
 set(w:=(nth index image 0)mod 2^32)in *.
 assert(Hw:norm 32(read_signal(rtl s)@id:SLOT_WORD@%nat)=w).
 { rewrite Hslot,Hpc. destruct HAt as[HI0[HP _]]. rewrite HP. unfold rom.
   replace(4*Z.of_nat index/4)with(Z.of_nat index)by(rewrite Z.mul_comm;symmetry;apply Z.div_mul;lia).
   rewrite Nat2Z.id. rewrite ExtendedSVBankAlignment.norm_mod. reflexivity. }
 destruct Hcases as[[HI Ha]|[[rd[imm[Hi Ha]]]|[[rd[imm[Hi Ha]]]|[op[rs1[rs2[imm[Hi Ha]]]]]]]].
 - pose proof(f_equal getRegs Ha)as Hregs. clear Ha. destruct i;try(cbn[CV32E40PDataOpProgramScope.CV32E40PDataOpProgramScope.DataOp21 CV32E40PDataOpProgramScope.CV32E40PDataOpProgramScope.dataop21b]in HI;discriminate). all:(first[@ALTS@
 fail 1 "no class matched"]).
 - subst i. pose proof(f_equal getRegs Ha)as Hregs. clear Ha. (first[@ALTS@
 fail 1 "no class matched"]).
 - subst i. pose proof(f_equal getRegs Ha)as Hregs. clear Ha. (first[@ALTS@
 fail 1 "no class matched"]).
 - subst i. pose proof(f_equal getRegs Ha)as Hregs. clear Ha. destruct op;cbn[CPUISABranchFamilyEffects.CPUISABranchFamilyEffects.instruction]in HDw,Hregs;(first[@ALTS@
 fail 1 "no class matched"]).
Qed.

Theorem arch_bubble image HC s r:CY.env_ok s -> tmpl_arch image HC s r -> norm 2(read_signal(rtl s)@id:VALID_CTR@%nat)<>0 ->
 tmpl_arch image HC(actual_cycle image s)r.
Proof. intros HE Ha HF. destruct Ha as[HZ[HI[HR[HH Hx]]]].
 destruct(bubble_rf image s r HE HZ Hx HF)as[HZ' Hram].
 split;[exact HZ'|]. split;[exact HI|]. split;[rewrite Hram;exact HR|]. split;[exact HH|].
 intro H1. apply Hx. pose proof HE as[H0[H6[H17[Hz Hnz]]]].
 pose proof(CY.act_xres image s H0)as Ex. rewrite H1 in Ex.
 destruct(reset_cycles s)eqn:E.
 - destruct(Hz eq_refl)as[Hr2 _]. rewrite Hr2 in Ex. discriminate.
 - destruct(Hnz ltac:(discriminate))as[_[X _]]. exact X. Qed.

Theorem arch_commit image HC s r post:CY.env_ok s -> tmpl_arch image HC s r -> IV.CoherentFields(rtl s) ->
 norm 2(read_signal(rtl s)@id:VALID_CTR@%nat)=0 ->
 norm 32(read_signal(rtl s)@id:SLOT_WORD@%nat)=norm 32(rom image(norm 32(read_signal(rtl s)@id:EXEC_PC@%nat))) ->
 norm 32(read_signal(rtl s)@id:EXEC_PC@%nat)=word.unsigned(getPc r) ->
 norm 32(read_signal(rtl s)@id:SLOT_PC@%nat)=norm 32(word.unsigned(getPc r)+4) ->
 FormalSpec.run1 r=(Some tt,post) -> tmpl_arch image HC(actual_cycle image s)post.
Proof. intros HE Ha Hco HF Hslot Hpc Hlink Hrun. destruct Ha as[HZ[HI[HR[HH Hx]]]].
 pose proof(CY.env_commit_xres s HE HF)as HX.
 destruct HH as[index HAt].
 destruct(commit_rf image HC s r post index HE HZ Hco HX HF Hslot Hpc Hlink HAt Hrun)as[HZ' Hram].
 destruct(JF.checked_run1_stays_in_program image index r post HC HAt Hrun)as[nx[HAt' Hdm]].
 split;[exact HZ'|]. split;[exact(proj1(proj2(proj2 HAt')))|]. split;[rewrite Hram,Hdm;exact HR|]. split;[exists nx;exact HAt'|].
 intro H1. pose proof HE as[H0[H6[H17[Hz Hnz]]]].
 pose proof(CY.act_xres image s H0)as Ex. rewrite H1 in Ex.
 destruct(reset_cycles s)eqn:E.
 - destruct(Hz eq_refl)as[Hr2 _]. rewrite Hr2 in Ex. discriminate.
 - destruct(Hnz ltac:(discriminate))as[_[_ Hf]]. rewrite HF in Hf. destruct Hf as[Hf|Hf];discriminate. Qed.
"""


def text(module='DarkTmplArch', design='darkriscv'):
    g = ctl.Gen(design, module)
    ids = g.id
    # bubble cases in the order of the destruct: X in {0,1} x K in {1,2,3}
    cases = []
    for x in (0, 1):
        for k in (1, 2, 3):
            cases.append(f' - pose proof(BUB.Bub{x}_{k}_controls seed d HL(conj(Hx1 _ X)(conj Hhl(Hf1 _ K))))as[Hr Hd]. '
                         f'refine(conj(fun H=>_)(conj(fun H=>_)Hd)); [{"exfalso; rewrite X in H; discriminate" if x else "exact Hr"}|{"exact Hr" if x else "exfalso; rewrite X in H; discriminate"}].')
    alts = []
    for c in isa.classes():
        n = c['name']
        k = len(arch.split_args(ct.args(c)))
        und = ' '.join(['_'] * k)
        extra = ' Hpc' if n == 'Auipc' else (' Hlink' if c['kind'] in ('jal', 'jalr') else '')
        alts.append(f' exact(ARF.rfarch_{n} image s r post w {und} HE HZ HC\' HX HF Hw(INVC.inv_{n} w {und} HDw){extra} Hregs)|')
    core = CORE.replace('@BUBCASES@', '\n'.join(cases)).replace('@ALTS@', ' '.join(alts))
    names = ['tmpl_arch_reset', 'arch_bubble', 'arch_commit']
    t = HDR + f'Module {module}.\n' + core + f'End {module}.\n'
    t += ''.join(f'Print Assumptions {module}.{n}.\n' for n in names)
    return PR.Params(design).render(t), [f'{module}.{n}' for n in names]


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('--module', default='DarkTmplArch')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=True)
    ap.add_argument('--provider', action='append', default=[])
    ap.add_argument('--accept', action='store_true')
    a = ap.parse_args()
    body, exports = text(a.module)
    if not a.accept:
        Path(a.out).write_text(body)
        print(a.out)
        sys.exit(0)
    import cpu_tmpl_accept as acc
    prov = [dict(namespace=x.split('=')[0], directory=str(Path(x.split('=')[1]).resolve())) for x in a.provider]
    lp = [(d['directory'], d['namespace']) for d in json.loads(Path('framework/auto-contract-profiles/darkriscv.json').read_text())['coq_load_paths']
          if d['namespace'] == 'Dark38']
    r = acc.accept(a.out, a.namespace, a.module, body, exports, lp, providers=prov, extra=dict(generator='tools/cpu_tmpl_archtop.py', design='darkriscv'))
    print(json.dumps(r, indent=1))
    sys.exit(0 if r['accepted'] else 1)
