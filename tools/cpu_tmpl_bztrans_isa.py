#!/usr/bin/env python3
"""Bzeeno transport, ISA side of the stage payloads (module BzTmplTrIsa), generated from the class table.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import cpu_isa_classes as isa

AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
ARITY = {'Lui': 2, 'Auipc': 2, 'Jal': 2}


def arity(n):
    return ARITY.get(n, 3)


def dest_classes():
    return [c['name'] for c in isa.classes() if c['writes_rd']]


def branch_classes():
    return [c['name'] for c in isa.classes() if c['kind'] == 'branch']


def pat(n, names=None):
    names = names or {}
    return 'Decode.' + n + ''.join(' ' + names.get(k, '_') for k in range(arity(n)))


HEAD = r"""(** Bzeeno transport: ISA side of the stage payloads (tools/cpu_tmpl_bztrans_isa.py).
    The register effect of one checked ISA step as a forwarding payload: `dpay c i = Some (rd, value)` iff the instruction writes rd /= 0;
    `isa_eff`: the ISA register view after the step is `upd (dpay c i)` on the view before.  Design independent.
    proof_author: @AUTHOR@; external_llm_api_calls=0. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVBankAlignment Ex.External.CPUProgramROM Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUJumpFamilyPostShape
 Ex.External.CPUISARegView Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
 Ex.External.CV32E40PJumpFenceExecution Ex.External.CV32E40PBranchExecution Ex.External.CPUClassTableInverse
 Ex.External.CPUGeneratedJointITree Ex.External.CPUPipelineStages
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Utility riscv.Utility.MkMachineWidth riscv.Spec.Decode.
Import ListNotations ExtendedSV ExtendedSVBankAlignment CV32E40PDataOpExecution CV32E40PReq40StateRel.
Local Open Scope Z_scope.
Module BzTmplTrIsa.
Module PS := Ex.External.CPUJumpFamilyPostShape.CPUJumpFamilyPostShape.
Module PD := Ex.External.CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.
Module Inv := Ex.External.CPUClassTableInverse.CPUClassTableInverse.
Module V := Ex.External.CPUISARegView.CPUISARegView.
Module J := Ex.External.CPUGeneratedJointITree.CPUGeneratedJointITree.
Section Isa.
Context {word : Interface.word 32} {BW : Bitwidth 32} {MW : MachineWidth word}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Local Notation uw := word.unsigned.

Definition wr (rd v : Z) : option (Z * Z) := if Z.eqb rd 0 then None else Some (rd, v).
Definition upd := CPUPipelineStages.CPUPipelineStages.upd (Reg:=Z) (Val:=Z) Z.eqb.
Lemma upd_wr rd v r base : upd (wr rd v) r base = if (Z.eqb r rd && negb (Z.eqb rd 0))%bool then v else base.
Proof. unfold upd, wr, CPUPipelineStages.CPUPipelineStages.upd. destruct (Z.eqb rd 0) eqn:E0; cbn.
 - rewrite andb_false_r. reflexivity.
 - rewrite Z.eqb_sym. destruct (Z.eqb r rd); reflexivity. Qed.
Lemma eff_write (c y : FormalSpec.State) rd (v : word) : getRegs y = (if Z.eq_dec rd 0 then getRegs c else map.put (getRegs c) rd v) ->
 forall r, V.isa_view y r = upd (wr rd (uw v)) r (V.isa_view c r).
Proof. intros H r. rewrite (V.view_after_write c y rd v H r), upd_wr. reflexivity. Qed.
Lemma eff_keep (c y : FormalSpec.State) : getRegs y = getRegs c -> forall r, V.isa_view y r = V.isa_view c r.
Proof. intros H r. exact (V.view_after_keep c y H r). Qed.
(** the program word at a checked point is normalised *)
Lemma word_norm words index : PD.check_program words = true -> (index < length words)%nat -> norm 32 (nth index words 0) = nth index words 0.
Proof. intros HC HI. destruct (PD.checked_entry words index HC HI) as [i [_ [[H0 H1] _]]].
 rewrite ExtendedSVBankAlignment.norm_mod. apply Z.mod_small. split; [exact H0|]. exact H1. Qed.
"""

TAIL = r"""Theorem isa_eff words (HC : PD.check_program words = true) t (c y : FormalSpec.State) i :
 PD.AtProgram words (Z.to_nat (t / 4)) c -> t = uw (getPc c) -> J.checked_pc_effect t c = Some y ->
 Decode.decode Decode.RV32I (norm 32 (nth (Z.to_nat (t / 4)) words 0)) = Decode.IInstruction i ->
 forall r, V.isa_view y r = upd (dpay c i) r (V.isa_view c r).
Proof. intros HAt Ht HE Hdec.
 destruct (J.checked_pc_effect_sound t c y HE) as [Hrun _].
 destruct (PS.checked_post_shape words _ c y HC HAt Hrun) as [i' [Hd' Hcases]].
 rewrite (word_norm words _ HC (proj1 HAt)) in Hdec. rewrite Hd' in Hdec. injection Hdec as <-.
 destruct Hcases as [[HD Ha]|[[rd [imm [Hi Ha]]]|[[rd [imm [Hi Ha]]]|[op [rs1 [rs2 [imm [Hi Ha]]]]]]]].
 - subst y. destruct i'; try (unfold CV32E40PDataOpProgramScope.CV32E40PDataOpProgramScope.DataOp21 in HD; cbn in HD; discriminate HD).
   all: (intro r; unfold dpay, dwr, drd, dval; cbn; apply eff_write; reflexivity).
 - subst y i'. intro r. unfold dpay, dwr, drd, dval; cbn. apply eff_write. reflexivity.
 - subst y i'. intro r. unfold dpay, dwr, drd, dval; cbn. apply eff_write. reflexivity.
 - subst y i'. destruct op; intro r; unfold dpay, dwr; cbn; try rewrite upd_none; apply eff_keep; reflexivity.
Qed.
End Isa.
End BzTmplTrIsa.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
"""


def build():
    ds = dest_classes()
    drd = ' | '.join(pat(n, {0: 'rd'}) for n in ds)
    dwr = ' | '.join(pat(n) for n in ds)
    L = [HEAD.replace('@AUTHOR@', AUTHOR)]
    L.append('Lemma upd_none r base : upd None r base = base. Proof. reflexivity. Qed.')
    L.append(f'Definition drd (i : Decode.InstructionI) : Z := match i with {drd} => rd | _ => 0 end.')
    L.append(f'Definition dwr (i : Decode.InstructionI) : bool := match i with {dwr} => true | _ => false end.')
    L.append('Definition dval (c : FormalSpec.State) (i : Decode.InstructionI) : word :=\n match i with Decode.Jal _ _ | Decode.Jalr _ _ _ => word.add (getPc c) (word.of_Z 4) | _ => result_word c i end.')
    L.append('Definition dpay (c : FormalSpec.State) (i : Decode.InstructionI) : option (Z * Z) := if dwr i then wr (drd i) (uw (dval c i)) else None.')
    L.append(TAIL)
    L.extend(f'Print Assumptions BzTmplTrIsa.{e}.' for e in ('upd_wr', 'word_norm', 'isa_eff'))
    return '\n'.join(L) + '\n'


if __name__ == '__main__':
    import sys
    from pathlib import Path
    Path(sys.argv[1]).write_text(build())
