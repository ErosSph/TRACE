#!/usr/bin/env python3
"""INV definitions of the Bzeeno staged design (template route, tools/cpu_tmpl_bzinv.py).

Runtime = list Event (state `rs words events`), Token = instruction PC.  stages = [MEM; EX; ID] (oldest first, index 0 = EX/MEM
registers 286/287, index 1 = ID/EX 250/245, index 2 = IF/ID 141/139; the MEM/WB registers 308/309 hold the token that already
retired: the observer reads them after the rise, the RF write happens at the fall).
Per-class parts (ExCl, MemCl) are generated from the accepted ISA bridge of r-tmpl-bz-ex-iface (`<C>_ex_isa` statements: the
operand / control premises and the ISA value), i.e. from the class table through that module; nothing is hand-typed per class.
Untrusted generator. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import re
import sys
from pathlib import Path
import cpu_isa_classes as C

IFACE = Path('results/r-tmpl-bz-ex-iface-20261103-a1/BzTmplExIface.v')
PAT = {  # constructor patterns for the classes whose ex_isa statement does not show the instruction
    'Jal': 'Decode.Jal rd imm', 'Jalr': 'Decode.Jalr rd rs1 imm',
}


def sub(txt):
    txt = re.sub(r'\bread_signal d\b', 'read_signal S', txt)
    txt = re.sub(r'\bs\b', 'cut', txt)
    txt = re.sub(r'\bExPrem_(\w+) d\b', r'EI.ExPrem_\1 S', txt)
    return txt


def parse():
    src = IFACE.read_text()
    res = {}
    for m in re.finditer(r'^Theorem (\w+)_ex_isa seed d s(.*?) : CombLFP P seed d -> ExPrem_\w+ d -> (.*)\.$', src, re.M):
        name, args, rest = m.groups()
        parts = rest.split(' -> ')
        concl, hyps = parts[-1], parts[:-1]
        res[name] = (args.split(), hyps, concl)
    return res


def build():
    cls = C.classes()
    isa = parse()
    ex_arms, mem_arms = [], []
    for c in cls:
        n = c['name']
        if c['kind'] == 'branch':
            pat = {'Beq': 'Decode.Beq', 'Bne': 'Decode.Bne', 'Blt': 'Decode.Blt', 'Bge': 'Decode.Bge', 'Bltu': 'Decode.Bltu', 'Bgeu': 'Decode.Bgeu'}[n] + ' rs1 rs2 imm'
            ex_arms.append(f' | {pat} => norm 1 (read_signal S 236%nat) = 0')
            mem_arms.append(f' | {pat} => norm 1 (read_signal S 279%nat) = 0')
            continue
        args, hyps, concl = isa[n]
        m = re.search(r'\(Decode\.(\w+)((?: \w+)*)\)', concl)
        pat = f'Decode.{m.group(1)}{m.group(2)}' if m else PAT[n]
        pv = set(pat.split()[1:])
        ex = [h for h in map(sub, hyps)]
        exv = [a for a in args if a not in pv and a not in ('seed', 'd', 's')]
        # the shift-immediate hyps mention b (existential) and sh (pattern var)
        body = f'EI.ExPrem_{n} S /\\ norm 1 (read_signal S 236%nat) = 1' + ''.join(f' /\\ {h}' for h in ex)
        if exv:
            body = 'exists ' + ' '.join(exv) + ', ' + body
        ex_arms.append(f' | {pat} => {body}')
        rhs = sub(concl).split(' = ', 1)[1]
        mem_arms.append(f' | {pat} => norm 1 (read_signal S 279%nat) = 1 /\\ norm 32 (read_signal S 284%nat) = {rhs}')
    return '\n'.join(ex_arms), '\n'.join(mem_arms)


TEXT = r"""(** Bzeeno staged design: INV definitions (tools/cpu_tmpl_bzinv.py).  proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
    Runtime = list Event, Token = instruction PC, stages = [MEM; EX; ID] (oldest first).  Per-stage token clauses at the token's reference cut:
      ID  (IF/ID 141 valid, 139 pc, 140 word, 138 pc+4),  EX (ID/EX 250, 245, control constants + operands of the class, 249 = link),
      MEM (EX/MEM 286, 287, 279 write flag, 283 rd field, 284 ISA write value, 278 wmem = 0).
    Arch: RF bank = ISA register view of the RETIRED state (lane 0 = 0 through isa_view), RAM unchanged.
    Front: fetch cursor (valid ID: 119 = pc_id + 4; empty ID: 119 = pc of the frontier), the program domain at the frontier, bubble hygiene,
    environment history and clock boundary. *)
From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVPackedROM Lang.ExtendedSVBankOperand
 Ex.External.CPUProgramROM Ex.External.CPUJumpFamilyProgramDomain Ex.External.CPUISARegView
 Ex.External.CV32E40PReq41Instruction Ex.External.CV32E40PReq40StateRel Ex.External.CV32E40PDataOpExecution
 Ex.External.CV32E40PISAWordInterpretation Ex.External.CPUClassValueBridge Ex.External.CV32E40PBranchISACondition
 Ex.RvCore.FormalSpec Ex.RvCore.Machine coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 riscv.Utility.Utility riscv.Utility.MkMachineWidth
 GeneratedRuntimeInput.ConfiguredAST GeneratedWriteValidityBoot.WriteValidityBoot GeneratedClockCycleJoint.CycleJoint
 TmplBzEnv.BzTmplEnv TmplBzExIface.BzTmplExIface.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVBankOperand CV32E40PReq40StateRel CV32E40PDataOpExecution CV32E40PISAWordInterpretation CV32E40PBranchISACondition.
Local Open Scope Z_scope.
Module BzTmplInv.
Module EI := TmplBzExIface.BzTmplExIface.BzTmplExIface.
Module E := TmplBzEnv.BzTmplEnv.BzTmplEnv.
Section Inv.
Context {word : Interface.word 32} {BW : Bitwidth 32}.
Context {Registers : map.map Decode.Register word} {Mem : map.map word byte}.
Context {word_ok : word.ok word} {registers_ok : map.ok Registers} {mem_ok : map.ok Mem}.
Local Notation uw := word.unsigned.
Let reg (s:FormalSpec.State) r := formal_register_word s r.
Variable words : list Z.

(** ---------- views of the RTL state ---------- *)
Definition rg (S : State) (r : nat) (w : nat) : Z := norm w (read_signal S r).
Definition iword (t : Z) : Z := norm 32 (nth (Z.to_nat (t / 4)) words 0).
Definition nop_word : Z := 28691.
(** the token's cut is a program point of the checked image, at the token's pc *)
Definition Dom (t : Z) (cut : FormalSpec.State) : Prop :=
 CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.AtProgram words (Z.to_nat (t / 4)) cut /\ t = uw (getPc cut).

(** ---------- per-class parts (generated from the ISA bridge of the EX interface) ---------- *)
Definition ExCl (S : State) (cut : FormalSpec.State) (i : Decode.InstructionI) : Prop :=
 match i with
@EXARMS@
 | _ => False
 end.
Definition MemCl (S : State) (cut : FormalSpec.State) (i : Decode.InstructionI) : Prop :=
 match i with
@MEMARMS@
 | _ => False
 end.

(** ---------- per-stage token relations (sd_stage) ---------- *)
Definition StageID (S : State) (t : Z) (cut : FormalSpec.State) : Prop :=
 rg S 141 1 = 1 /\ rg S 139 32 = t /\ rg S 140 32 = iword t /\ rg S 138 32 = norm 32 (t + 4) /\ Dom t cut.
Definition StageEX (S : State) (t : Z) (cut : FormalSpec.State) : Prop :=
 rg S 250 1 = 1 /\ rg S 245 32 = t /\ rg S 249 32 = norm 32 (t + 4) /\ rg S 244 5 = bitSlice (iword t) 7 12 /\
 rg S 233 1 = 0 /\ rg S 232 1 = 0 /\ Dom t cut /\
 exists i, Decode.decode Decode.RV32I (iword t) = Decode.IInstruction i /\ ExCl S cut i.
Definition StageMEM (S : State) (t : Z) (cut : FormalSpec.State) : Prop :=
 rg S 286 1 = 1 /\ rg S 287 32 = t /\ rg S 283 5 = bitSlice (iword t) 7 12 /\ rg S 278 1 = 0 /\ rg S 277 1 = 0 /\ Dom t cut /\
 exists i, Decode.decode Decode.RV32I (iword t) = Decode.IInstruction i /\ MemCl S cut i.
Definition stage_rel (events : list Event) (k : nat) (t : Z) (cut : FormalSpec.State) : Prop :=
 let S := E.rs words events in
 match k with 0%nat => StageMEM S t cut | 1%nat => StageEX S t cut | 2%nat => StageID S t cut | _ => False end.

(** ---------- stage tags: [MEM; EX; ID] ---------- *)
Definition tok (S : State) (v pc : nat) : option Z := if Z.eqb (rg S v 1) 0 then None else Some (rg S pc 32).
Definition stages (events : list Event) : list (option Z) :=
 let S := E.rs words events in [tok S 286 287; tok S 250 245; tok S 141 139].

(** ---------- architecture: RF bank = retired ISA registers; RAM unchanged ---------- *)
Definition arch_rel (events : list Event) (retired : FormalSpec.State) : Prop :=
 RFRel (read_signal (E.rs words events) 319%nat) (CPUISARegView.isa_view retired) /\
 read_signal (E.rs words events) 327%nat = read_signal (E.rs words []) 327%nat.

(** ---------- front: environment, bubble hygiene, fetch cursor ---------- *)
Definition Struct (S : State) : Prop :=
 (rg S 141 1 = 0 -> rg S 140 32 = nop_word /\ rg S 139 32 = 0 /\ rg S 138 32 = 0) /\
 (rg S 250 1 = 0 -> rg S 244 5 = 0 /\ rg S 233 1 = 0 /\ rg S 232 1 = 0) /\
 (rg S 286 1 = 0 -> rg S 283 5 = 0 /\ rg S 278 1 = 0 /\ rg S 277 1 = 0) /\
 (rg S 141 1 = 1 -> rg S 119 32 = norm 32 (rg S 139 32 + 4)) /\
 (rg S 232 1 = 0 /\ rg S 277 1 = 0) /\
 (exists i, Decode.decode Decode.RV32I (rg S 140 32) = Decode.IInstruction i /\ CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.legal_instruction i = true).
Definition front_rel (events : list Event) (frontier : FormalSpec.State) : Prop :=
 let S := E.rs words events in
 Forall GeneratedWriteValidityBoot.WriteValidityBoot.Environment events /\ ClockBoundary S /\ Struct S /\
 (exists index, CPUJumpFamilyProgramDomain.CPUJumpFamilyProgramDomain.AtProgram words index frontier) /\ (rg S 141 1 = 0 -> rg S 119 32 = uw (getPc frontier)).
End Inv.
End BzTmplInv.
Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.
Print Assumptions BzTmplInv.ExCl.
Print Assumptions BzTmplInv.MemCl.
Print Assumptions BzTmplInv.stage_rel.
Print Assumptions BzTmplInv.stages.
Print Assumptions BzTmplInv.arch_rel.
Print Assumptions BzTmplInv.front_rel.
"""


def text():
    ex, mem = build()
    return TEXT.replace('@EXARMS@', ex).replace('@MEMARMS@', mem)


if __name__ == '__main__':
    t = text()
    Path(sys.argv[1]).write_text(t)
    print(sys.argv[1], len(t.splitlines()))
