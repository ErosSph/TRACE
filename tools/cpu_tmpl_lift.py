#!/usr/bin/env python3
"""ISA-LIFT stage of the template route (stage S2), all designs. Untrusted generator; Coq checks everything.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.

  --kinds isa    design independent module TmplLiftIsa (generalises cpu_tmpl_bztrans_isa: dpay/isa_eff, plus ISA next pc `ipc`,
                 `isa_pc` (checked ISA step), `isa_pc_ok` (aligned, in program), jalr/boolz helper lemmas)
  --kinds lift   per design module <D>TmplLift: per class C the facts of the design's provider module (framework/lift-roles/<D>.json)
                 are instantiated at ISA values (operands uw(reg s rs), pc uw(getPc s), imm norm 32 imm) and their conclusions are
                 equated with result_word / link, isa_branch_guard, ipc (next pc, JALR &~1) ; premises of the provider stay verbatim.
  --kinds iface  regression: Bzeeno `<C>_ex_isa` statements regenerated from the same role parametrised builder (delegates to bzex).
generalized_rule: (G1) ISA lemmas stated once on `InstructionI` with a generated match; (G2) the lift builder is parametrised by roles
(provider theorem pattern, variable roles, wire ids), not by a design.
"""
import argparse, json, re, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_isa_classes as isa
import cpu_class_table as ct
import cpu_tmpl_bztrans_isa as bti

ROOT = Path(__file__).resolve().parent.parent
AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
BR = [c['name'] for c in isa.classes() if c['kind'] == 'branch']

REQ_EXTRA = ' Ex.External.CPUISAJalEffects Ex.External.CPUISABranchFamilyEffects Ex.External.CV32E40PBranchISACondition Ex.External.CPUDatapathFacts Ex.External.CPUImmediateShapes Ex.External.CPUISAJalrTargetValue coqutil.Z.BitOps coqutil.Z.bitblast coqutil.Z.prove_Zeq_bitwise.'

PRE_LEMMAS = r"""
Lemma norm32_range x : 0 <= norm 32 x < 2 ^ 32.
Proof. rewrite ExtendedSVBankAlignment.norm_mod. change (Z.of_nat 32) with 32. apply Z.mod_pos_bound. lia. Qed.
Lemma clear0_jalr x : norm 32 (Z.shiftl (Z.shiftr (norm 32 x) 1) 1) = Z.land (norm 32 x) (2 ^ 32 - 2).
Proof. rewrite CPUDatapathFacts.CPUDatapathFacts.clear0_land. rewrite (CPUISAJalrTargetValue.clear_bit0 _ (norm32_range x)).
 rewrite !CPUImmediateShapes.norm_ones. change (Z.of_nat 32) with 32. prove_Zeq_bitwise. Qed.
Lemma tb0_norm x : norm 32 x mod 2 = 0 -> Z.testbit x 0 = false.
Proof. intro H. rewrite ExtendedSVBankAlignment.norm_mod in H. change (Z.of_nat 32) with 32 in H.
 rewrite <- (Z.mod_pow2_bits_low x 32 0) by lia. rewrite Z.bit0_odd.
 apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. rewrite Hk.
 rewrite Z.odd_mul. change (Z.odd 2) with false. rewrite andb_false_r. reflexivity. Qed.
Lemma boolz_bool (p q : bool) : boolz p = boolz q -> p = q.
Proof. destruct p, q; cbn; congruence. Qed.
"""


def ipc_def():
    arms = []
    for n in BR:
        arms.append(f' | Decode.{n} r1 r2 imm => if isa_branch_guard (Decode.{n} r1 r2 imm) (formal_register_word c r1) (formal_register_word c r2) then norm 32 (uw (getPc c) + imm) else norm 32 (uw (getPc c) + 4)')
    return ('Definition ipc (c : FormalSpec.State) (i : Decode.InstructionI) : Z :=\n match i with\n'
            ' | Decode.Jal _ imm => norm 32 (uw (getPc c) + imm)\n | Decode.Jalr _ _ imm => Z.land (norm 32 imm) (2 ^ 32 - 2)\n'
            + '\n'.join(arms) + '\n | _ => norm 32 (uw (getPc c) + 4) end.')


ISA_LEMMAS = r"""
Lemma uw_add_of_Z (pc : word) (imm : Z) : uw (word.add pc (word.of_Z imm : word)) = norm 32 (uw pc + imm).
Proof. rewrite word.unsigned_add, word.unsigned_of_Z. unfold word.wrap. rewrite Z.add_mod_idemp_r by lia.
 rewrite ExtendedSVBankAlignment.norm_mod. reflexivity. Qed.
Lemma nextpc_val (c : FormalSpec.State) words index : PD.AtProgram words index c -> uw (getNextPc c) = norm 32 (uw (getPc c) + 4).
Proof. intros [_ [_ [_ HN]]]. rewrite HN. unfold CPUISAJalEffects.link. exact (V.uw_link (getPc c)). Qed.
@IPC@
Definition jalr_ok (i : Decode.InstructionI) : Prop := match i with Decode.Jalr _ rs _ => rs = 0 | _ => True end.
Theorem isa_pc words (HC : PD.check_program words = true) t (c y : FormalSpec.State) i :
 PD.AtProgram words (Z.to_nat (t / 4)) c -> t = uw (getPc c) -> J.checked_pc_effect t c = Some y ->
 Decode.decode Decode.RV32I (norm 32 (nth (Z.to_nat (t / 4)) words 0)) = Decode.IInstruction i ->
 uw (getPc y) = ipc c i /\ jalr_ok i.
Proof. intros HAt Ht HE Hdec.
 destruct (J.checked_pc_effect_sound t c y HE) as [Hrun _].
 destruct (PS.checked_post_shape words _ c y HC HAt Hrun) as [i' [Hd' Hcases]].
 rewrite (word_norm words _ HC (proj1 HAt)) in Hdec. rewrite Hd' in Hdec. injection Hdec as <-.
 pose proof (nextpc_val c words _ HAt) as HNV.
 destruct Hcases as [[HD Ha]|[[rd [imm [Hi Ha]]]|[[rd [imm [Hi Ha]]]|[op [rs1 [rs2 [imm [Hi Ha]]]]]]]].
 - subst y. destruct i'; try (unfold CV32E40PDataOpProgramScope.CV32E40PDataOpProgramScope.DataOp21 in HD; cbn in HD; discriminate HD).
   all: (split; [unfold ipc; cbn [dataop_post getPc]; exact HNV | exact I]).
 - subst y i'. split; [|exact I]. unfold ipc, CV32E40PJumpFenceExecution.jump_post. cbn [getPc CV32E40PJumpFenceExecution.reference_jump_target]. apply uw_add_of_Z.
 - subst y i'. split.
   + unfold ipc, CV32E40PJumpFenceExecution.jump_post. cbn [getPc]. rewrite PD.jalr_x0_target_unsigned. unfold PD.jalr_target. rewrite ExtendedSVBankAlignment.norm_mod. reflexivity.
   + reflexivity.
 - subst y i'. split; [|destruct op; exact I].
   destruct op; unfold ipc, CV32E40PBranchExecution.branch_post; cbn [getPc]; unfold CV32E40PBranchExecution.branch_next_pc, CV32E40PBranchExecution.reference_branch_taken, CV32E40PBranchExecution.reference_branch_target.
   all: cbn [CV32E40PBranchExecution.branch_rs1 CV32E40PBranchExecution.branch_rs2 CV32E40PBranchExecution.branch_immediate CPUISABranchFamilyEffects.instruction].
   all: (destruct (isa_branch_guard _ _ _); [apply uw_add_of_Z | exact HNV]).
Qed.
(** the ISA post pc of a checked step is 4-aligned and inside the program: the RTL misaligned-target / take_trap premises follow from it *)
Theorem isa_pc_ok words (HC : PD.check_program words = true) t (c y : FormalSpec.State) :
 PD.AtProgram words (Z.to_nat (t / 4)) c -> J.checked_pc_effect t c = Some y ->
 uw (getPc y) mod 4 = 0 /\ 0 <= uw (getPc y) < 4 * Z.of_nat (length words).
Proof. intros HAt HE. destruct (J.checked_pc_effect_sound t c y HE) as [Hrun _].
 destruct (PD.checked_run1_stays_in_program words _ c y HC HAt Hrun) as [n [[Hn [HP _]] _]].
 rewrite HP. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia]. Qed.
Theorem isa_pc_even words (HC : PD.check_program words = true) t (c y : FormalSpec.State) i :
 PD.AtProgram words (Z.to_nat (t / 4)) c -> t = uw (getPc c) -> J.checked_pc_effect t c = Some y ->
 Decode.decode Decode.RV32I (norm 32 (nth (Z.to_nat (t / 4)) words 0)) = Decode.IInstruction i ->
 ipc c i mod 2 = 0 /\ jalr_ok i.
Proof. intros HAt Ht HE Hdec. destruct (isa_pc words HC t c y i HAt Ht HE Hdec) as [H1 H2]. split; [|exact H2].
 destruct (isa_pc_ok words HC t c y HAt HE) as [H4 _]. rewrite H1 in H4. revert H4. generalize (ipc c i). intros x H4. apply Z.mod_divide in H4; [|lia]. destruct H4 as [k ->]. apply Z.mod_divide; [lia|]. exists (2 * k). lia. Qed.
"""


def isa_text(module='TmplLiftIsa'):
    t = bti.build()
    t = t.replace('BzTmplTrIsa', module)
    head, rest = t.split('Section Isa.', 1)
    head = head.replace('Ex.RvCore.FormalSpec coqutil.Word.Interface', 'Ex.RvCore.FormalSpec' + REQ_EXTRA.rstrip('.') + ' coqutil.Word.Interface', 1)
    head = head.replace('Import ListNotations ExtendedSV ExtendedSVBankAlignment CV32E40PDataOpExecution CV32E40PReq40StateRel.',
                        'Import ListNotations ExtendedSV ExtendedSVBankAlignment CV32E40PDataOpExecution CV32E40PReq40StateRel CV32E40PBranchISACondition.')
    body, tail = rest.split('End Isa.', 1)
    body = body.replace('Print Assumptions', '')
    ex = ['upd_wr', 'word_norm', 'isa_eff', 'isa_pc', 'isa_pc_ok', 'isa_pc_even', 'clear0_jalr', 'tb0_norm', 'boolz_bool', 'norm32_range']
    out = head + PRE_LEMMAS + 'Section Isa.' + body + ISA_LEMMAS.replace('@IPC@', ipc_def()) + 'End Isa.\nEnd ' + module + '.\n'
    out += 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n' + ''.join(f'Print Assumptions {module}.{e}.\n' for e in ex)
    return out, [f'{module}.{e}' for e in ex]


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--design', default='steel')
    ap.add_argument('--kinds', default='isa')
    ap.add_argument('--module')
    ap.add_argument('--namespace')
    ap.add_argument('--out', required=False)
    ap.add_argument('--accept', action='store_true')
    ap.add_argument('--providers', default='', help='ns=dir,ns=dir')
    ap.add_argument('--audit-roles', metavar='DESIGN', help='check a lift-roles file against the accepted provider results and print the lift obligations')
    ap.add_argument('--regress', action='store_true', help='bzeeno: regenerate the 23 `<C>_ex_isa` theorems and diff against the accepted module')
    a = ap.parse_args()
    if a.audit_roles:
        import cpu_tmpl_lift_design as LD
        sys.exit(LD.audit_roles(a.audit_roles))
    if a.regress:
        import cpu_tmpl_lift_design as LD
        sys.exit(LD.regress_bzeeno())
    if a.kinds == 'isa':
        mod = a.module or 'TmplLiftIsa'
        text, ex = isa_text(mod)
    else:
        import cpu_tmpl_lift_design as LD
        mod = a.module
        text, ex = LD.build(a.design, a.kinds, mod)
    if not a.accept:
        Path(a.out).write_text(text); print(a.out, len(text.splitlines()), 'lines', len(ex), 'exports'); sys.exit(0)
    import cpu_tmpl_accept as acc
    prov = [dict(namespace=x.split('=')[0], directory=x.split('=')[1]) for x in a.providers.split(',') if x]
    lp = []
    mf = ROOT / 'framework' / 'lift-roles' / f'{a.design}.json'
    if mf.exists():
        lp = [tuple(json.loads(mf.read_text())['ast_dir'])]
    r = acc.accept(a.out, a.namespace, mod, text, ex, lp, providers=prov, extra=dict(generator='tools/cpu_tmpl_lift.py', design=a.design, kinds=a.kinds))
    print(json.dumps({k: r[k] for k in r if k != 'per_class'}, indent=1)); sys.exit(0 if r.get('accepted') or r.get('coqc_accepted') else 1)
