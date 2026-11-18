"""Extract ISA register destinations and prove their frame against original ExecuteI."""
import argparse
import hashlib
import json
from pathlib import Path
import cpu_r_synthesis as synthesis
from cpu_certificate_acceptance import run_stage


def render(source):
    plan=synthesis.isa_demands(source)
    arms=[]
    for row in plan['instructions']:
        destinations=[x['field']for x in row['reference_uses']['destinations']]
        arms.append(' | Decode.'+row['instruction']+' '+' '.join(row['operands'])+
                    ' => ['+';'.join(destinations)+']')
    return r'''From Coq Require Import List ZArith.
Require Import Ex.External.CPUISARegisterFrameRules Ex.External.CPUISAInstructionExecution
 Ex.External.CPUISAExecutionEffects Ex.External.CPUOriginalISAReference
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec Ex.RvCore.Machine
 riscv.Spec.ExecuteI riscv.Proofs.DecodeByExtension coqutil.Word.Interface coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ListNotations CPUISARegisterFrameRules CPUISAInstructionExecution
 CPUISAExecutionEffects CPUOriginalISAReference CPURegisterEffectRelation.
Definition destination_registers(i:Decode.InstructionI):list Z:=match i with
'''+ '\n'.join(arms)+r'''
 | _=>[] end.

Lemma decode_i_destination_fields code:
 destination_registers(decodeI 32 code)=
 firstn(length(destination_registers(decodeI 32 code))) [Utility.bitSlice code 7 12].
Proof.
 unfold decodeI;cbv beta zeta.
 repeat match goal with |-context[if ?condition then _ else _]=>destruct condition end;
 reflexivity.
Qed.
Theorem original_decode_destination_fields code instruction:
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 destination_registers instruction=
 firstn(length(destination_registers instruction)) [Utility.bitSlice code 7 12].
Proof.
 rewrite <-decode_seq_correct;unfold decode_seq;
 cbn[bitwidth supportsM supportsA supportsF].
 destruct(isValidI(decodeI 32 code))eqn:HV.
 - intro H;inversion H;subst;apply decode_i_destination_fields.
 - destruct(isValidCSR(decodeCSR 32 code));discriminate.
Qed.
Theorem original_destination_address code instruction address rest:
 Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->
 destination_registers instruction=address::rest ->
 address=Utility.bitSlice code 7 12.
Proof.
 intros HD HS;pose proof(original_decode_destination_fields code instruction HD)as HF.
 rewrite HS in HF;cbn[length firstn]in HF;now inversion HF.
Qed.
Print Assumptions decode_i_destination_fields.
Print Assumptions original_decode_destination_fields.
Print Assumptions original_destination_address.
Section Frame.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}.
Theorem original_execute_frame i:WritesOnly(destination_registers i)(ExecuteI.execute i).
Proof. destruct i;cbn[destination_registers ExecuteI.execute];solve_frame. Qed.

Theorem original_token_frame {Token:Type}(token_pc token_word:Token->Z)
 token before after i address:
 instruction_effect token_pc token_word token before=Some after ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction i ->
 (0<=address<32)%Z ->~In address(destination_registers i) ->
 ISAView after address=ISAView before address.
Proof.
 intros HS HD HB HN.
 destruct(token_execute token_pc token_word token before after i HS HD)as[middle [HE HEND]].
 pose proof(original_execute_frame i before tt middle HE address HB HN)as HF.
 unfold ISAView in *;rewrite(end_cycle_register_frame middle after HEND);exact HF.
Qed.
End Frame.
Print Assumptions original_execute_frame.
Print Assumptions original_token_frame.
'''


def run(output,instruction_scope='rv32i38'):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    original=(synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text()
    selected=synthesis.instruction_scopes.select(synthesis.isa_demands(original),instruction_scope)
    source=render(original);path=out/'ISADestinations.v';path.write_text(source)
    flags=list(synthesis.origin.pending.rtl.framework.FLAGS)
    flags+=['-R',str(out.resolve()),'GeneratedISADestinations']
    c,t=run_stage([str(synthesis.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,
        instruction_scope=instruction_scope,selected_instruction_count=len(selected['instructions']),
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        isa_source_sha256=hashlib.sha256(original.encode()).hexdigest(),
        old_inv_read=False,actual_destination_binding_proved=False,complete_R_generated=False)
    if c.returncode==0:
        import cpu_operand_reference_requirements as refs
        report['original_assumptions_only']=refs.audit('\nSOURCE_REFERENCE_AUDIT\n'+c.stdout,2,closed=3)
        k,t=run_stage([str(synthesis.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedISADestinations.ISADestinations'],out/'coqchk.log',1200)
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                      accepted=k.returncode==0 and report['original_assumptions_only'])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',required=True);p.add_argument('--scope',default='rv32i38')
    a=p.parse_args();r=run(a.output,a.scope);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
