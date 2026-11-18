"""Queue movement preserves generated computed source R if the real field does.
Actual retirement and physical phase-field preservation remain obligations.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_operand_reference_requirements as sources
from cpu_certificate_acceptance import run_stage

def render(outputs):
    text='''From Coq Require Import List ZArith.
Require Import GeneratedSourceRequirements.SourceRequirements GeneratedISAInputs.ISAInputs
 Ex.External.CPUComputedReferenceTransfer Ex.External.CPUComputedReferenceCut
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference
 Ex.RvCore.FormalSpec Ex.RvCore.Machine Lang.ExtendedSV
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV CPUOriginalISAReference CPUComputedReferenceCut CPUComputedReferenceTransfer
 CPUGeneratedJointTemplate.
Section Transfer.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}
 {Token:Type}.
Variable token_pc token_word:Token->Z.

Theorem computed_source_R_cycle same width root observed post initial advanced
 retiring kept added index token reference position:
 NoDup(kept++added) ->
 EffectChain(instruction_effect token_pc token_word)initial retiring advanced ->
 (length retiring<=index)%nat ->
 lookup_before(instruction_effect token_pc token_word)same token initial(retiring++kept)=Some(index,reference) ->
 norm width(read_signal post root)=norm width(read_signal observed root) ->
 (computed_operand_R token_pc token_word same width root observed initial(retiring++kept)token position <->
  computed_operand_R token_pc token_word same width root post advanced(kept++added)token position).
Proof.
 intros HN HC HI HL HF.
 pose proof(lookup_cycle_subtract(instruction_effect token_pc token_word)same
 initial advanced retiring kept added index token reference HN HC HI HL)as Hnext.
 unfold computed_operand_R;rewrite HL,Hnext.
 destruct(Decode.decode Decode.RV32I(token_word token));try reflexivity.
 match goal with |-context[requested_instruction ?i]=>destruct(requested_instruction i) end;try reflexivity.
 match goal with |-context[nth_error ?xs ?n]=>destruct(nth_error xs n)as[address|] end;try reflexivity.
 match goal with |-context[match ?read with (_,_)=>_ end]=>
 destruct read as[result state] end.
 destruct result as[value|];try reflexivity.
 cbn;rewrite HF;reflexivity.
Qed.
'''
    transport=text[text.index('Theorem computed_source_R_cycle'):]
    transport=transport.replace('computed_source_R_cycle','computed_source_R_transport',1)
    transport=transport.replace('same width root observed post','same width source_root destination_root observed post',1)
    transport=transport.replace('read_signal post root','read_signal post destination_root')
    transport=transport.replace('read_signal observed root','read_signal observed source_root')
    transport=transport.replace('same width root observed','same width source_root observed')
    transport=transport.replace('same width root post','same width destination_root post')
    text+=transport
    for n,row in enumerate(outputs):
        text+=f'''Definition port_{n}_computed_R_cycle (same:forall x y:Token,{{x=y}}+{{x<>y}}) :=
 computed_source_R_cycle same {row['width']}%nat {row['output_root']}%nat.
'''
    return text+'''End Transfer.
Print Assumptions computed_source_R_cycle.
Print Assumptions computed_source_R_transport.
'''

def check(ast_path,ast_module,provider,output):
    root=sources.origin.ROOT;provider=Path(provider);output=Path(output)
    ast,binding,paths=sources.origin.raw_binding(ast_path,ast_module)
    analysis,_=sources.routes.analyze(ast)
    expected=f'Require Import {ast_module}.\n'+sources.render(binding['ast']['program'],analysis['ports'],True)
    prior=json.loads((provider/'report.json').read_text())
    if not(prior.get('accepted')is True and prior.get('coqc_exit')==prior.get('coqchk_exit')==0
           and prior.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
           and (provider/'SourceRequirements.v').read_text()==expected
           and (provider/'SourceRequirements.vo').exists()
           and sources.audit((provider/'coqc.log').read_text(),3*len(analysis['ports'])+6)):
        raise ValueError('checked unchanged generated source R provider required')
    output.mkdir(parents=True,exist_ok=False)
    source=render(analysis['ports']);path=output/'ComputedRTransfer.v';path.write_text(source)
    flags=list(sources.origin.pending.rtl.framework.FLAGS)
    for p in paths:flags+=['-R',p['directory'],p['namespace']]
    flags+=['-R',str(provider.resolve()),'GeneratedSourceRequirements',
            '-R',prior['provider'],'GeneratedOperandRoutes',
            '-R',prior['isa_provider'],'GeneratedISAInputs',
            '-R',str(output.resolve()),'GeneratedComputedRTransfer']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(root/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),provider=str(provider.resolve()),
        generated_ports=len(analysis['ports']),old_inv_read=False,complete_R_generated=False,
        actual_queue_transition_proved=False,phase_field_preservation_proved=False)
    if c.returncode==0:
        report['original_assumptions_only']=sources.audit('\nSOURCE_REFERENCE_AUDIT\n'+c.stdout,2)
        k,t=run_stage([str(root/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedComputedRTransfer.ComputedRTransfer'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                      accepted=k.returncode==0 and report['original_assumptions_only'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','provider','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
