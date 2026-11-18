"""Generate actual-bank result obligations against computed original ISA states.
These obligations are not claimed established on reachable CPU states.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_r_synthesis as synthesis
from cpu_certificate_acceptance import run_stage


def render(root, program, instruction_scope='rv32i38'):
    demands=synthesis.isa_demands((synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text())
    selected=synthesis.instruction_scopes.select(demands,instruction_scope)['instructions']
    arms='\n'.join(' | Decode.'+row['instruction']+' '+' '.join(row['operands'])+' => true'
                   for row in selected)
    return synthesis.relation_source(root, program)+rf'''
Require Import Ex.External.CPUComputedResultCut Ex.External.CPUOriginalISAReference
 Ex.External.CPUComputedReferenceCut Ex.External.CPUReferenceCuts
 Ex.External.CPURegisterEffectCheck
 coqutil.Word.Bitwidth riscv.Utility.MkMachineWidth riscv.Utility.Utility.
Import CPUComputedResultCut CPUOriginalISAReference CPUComputedReferenceCut CPUReferenceCuts.
Import CPURegisterEffectCheck.
Section ComputedRegisterResult.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{MW:MachineWidth word}}
 {{Registers:map.map Z word}}{{Mem:map.map word byte}}{{Token:Type}}.
Variable token_pc token_word:Token->Z.
Variable same:forall x y:Token,{{x=y}}+{{x<>y}}.

Definition result_instruction_in_scope instruction :=
 match Decode.decode Decode.RV32I instruction with
 |Decode.IInstruction i=>match i with
{arms}
 | _=>false end
 | _=>false end.

Definition R_register_computed_result ev pre initial pending token : Prop :=
 if result_instruction_in_scope(token_word token) then
 computed_result_R (instruction_effect token_pc token_word) same
 (fun before after => R_register pre before /\
   register_effect_check (ISAView before) (ISAView after)
     (actual_register_updates ev pre)=true)
 token initial pending else False.

Theorem R_register_computed_result_sound ev pre initial pending token:
 changed_signal ev<>{root}%nat ->
 R_register_computed_result ev pre initial pending token ->
 exists index before after,
 BeforeToken(instruction_effect token_pc token_word)initial pending index token before /\
 FormalSpec.run1 before=(Some tt,after) /\
 R_register(PhaseSemantics {program} ev pre)after.
Proof.
 intros HE HR;unfold R_register_computed_result,computed_result_R in HR.
 destruct(result_instruction_in_scope(token_word token));[|contradiction].
 destruct(lookup_after(instruction_effect token_pc token_word)same
 token initial pending)as[[[index before]after]|]eqn:HC;[|contradiction].
 destruct HR as[HB HW].
 pose proof(proj1(register_effect_check_exact (ISAView before) (ISAView after)
   (actual_register_updates ev pre)) HW)as HWprop.
 destruct(computed_result_is_original_run1 token_pc token_word same
 token initial pending index before after HC)as[HP [_ HS]].
 exists index,before,after;split;[exact HP|];split;[exact HS|].
 exact(R_register_transport ev pre before after HE HB HWprop).
Qed.
End ComputedRegisterResult.
Print Assumptions R_register_computed_result_sound.
'''


def check(ast_path, ast_module, output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=synthesis.origin.raw_binding(ast_path,ast_module)
    candidates=synthesis.roles.derive_candidates(ast)['register_file']
    if len(candidates)!=1:
        raise ValueError('unique physical bank candidate required; architectural role still unproved')
    root=candidates[0]['root'];profile['coq_load_paths']=paths
    provider=synthesis.bank.check_profile(profile,output/'bank')
    report=dict(accepted=False,bank_provider=provider,root=root,
        old_inv_read=False,complete_R_generated=False,
        architectural_role_proved=False,generated_conditions_established=False,
        actual_retirement_binding_proved=False)
    if provider.get('accepted') and root in {b['root'] for b in provider['generated_banks']}:
        scope=synthesis.instruction_scopes.for_input(ast_path,ast_module)
        report['instruction_scope']=scope
        source=f'Require Import {ast_module}.\n'+render(root,profile['ast']['program'],scope)
        path=output/'RegisterResultR.v';path.write_text(source)
        flags=list(synthesis.origin.pending.rtl.framework.FLAGS)
        for row in paths:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedRegisterResult',
                '-R',str((output/'bank').resolve()),'GeneratedBank']
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(synthesis.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
                      output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,
            source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0:
            import cpu_operand_reference_requirements as refs
            report['original_assumptions_only']=refs.audit(
                '\nSOURCE_REFERENCE_AUDIT\n'+c.stdout,1,closed=1)
            k,t=run_stage([str(synthesis.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
                '-norec','GeneratedRegisterResult.RegisterResultR'],output/'coqchk.log',
                max(.1,deadline-time.monotonic()))
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                accepted=k.returncode==0 and report['original_assumptions_only'])
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','output']:p.add_argument('--'+arg,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
