"""Lift complete mixed RTL effect conditions to ISA-computed source R.
This generates exact preconditions, not proofs that reachable CPUs satisfy them.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_computed_r_transfer as transfer
import cpu_effect_requirements as effects
from cpu_certificate_acceptance import run_stage
origin=effects.origin

def render(program,rows):
    lines=['''From Coq Require Import List ZArith.
Require Import GeneratedEffectRequirements.EffectRequirements
 GeneratedSourceRequirements.SourceRequirements GeneratedISAInputs.ISAInputs
 Ex.External.CPUComputedReferenceCut Ex.External.CPUOriginalISAReference
 Ex.RvCore.FormalSpec Ex.RvCore.Machine Lang.ExtendedSV
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV CPUOriginalISAReference CPUComputedReferenceCut.
Section EffectR.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}{Token:Type}.
Variable token_pc token_word:Token->Z.
'''];audits=[]
    for row in rows:
        r,w=row['root'],row['width']
        lines += [f'''Definition root_{r}_computed_effect_R
 (same:forall x y:Token,{{x=y}}+{{x<>y}}) ev pre initial pending token position : Prop :=
 match lookup_before(instruction_effect token_pc token_word)same token initial pending with
 |None=>False
 |Some(_,reference)=>match Decode.decode Decode.RV32I(token_word token)with
 |Decode.IInstruction i=>if requested_instruction i then
   match nth_error(requested_registers i)position with
   |None=>True
   |Some address=>match Machine.getRegister address reference with
     |(Some value,_)=>root_{r}_effect_R ev pre(word.unsigned value)
     |_=>False end
   end else False
 |_=>False end
 end.
Theorem root_{r}_computed_effect_R_exact same ev pre initial pending token position:
 changed_signal ev<>{r}%nat ->
 (root_{r}_computed_effect_R same ev pre initial pending token position <->
 computed_operand_R token_pc token_word same {w}%nat {r}%nat
 (PhaseSemantics {program} ev pre)initial pending token position).
Proof.
 intro HE;unfold root_{r}_computed_effect_R,computed_operand_R.
 destruct(lookup_before(instruction_effect token_pc token_word)same token initial pending)
 as[[index reference]|];try reflexivity.
 destruct(Decode.decode Decode.RV32I(token_word token));try reflexivity.
 match goal with |-context[requested_instruction ?i]=>destruct(requested_instruction i)end;try reflexivity.
 match goal with |-context[nth_error ?xs ?n]=>destruct(nth_error xs n)end;try reflexivity.
 match goal with |-context[match ?read with (_,_)=>_ end]=>destruct read as[result state]end.
 destruct result;try reflexivity.
 exact(root_{r}_effect_R_exact ev pre _ HE).
Qed.''']
        audits.append(f'Print Assumptions root_{r}_computed_effect_R_exact.')
    return '\n'.join(lines)+'\nEnd EffectR.\n'+'\n'.join(audits)+'\n'

def check(ast_path,ast_module,effect_provider,source_provider,output):
    import cpu_operand_capture_proofs as captures
    ep=Path(effect_provider);sp=Path(source_provider);output=Path(output)
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    roots=sorted({r['root']for r in effects.routes.discover(ast)['routes']if r['crossed_sampling_boundary']})
    if not roots:raise ValueError('no mixed or scalar storage; not an empty success')
    analysis,bad,missing=captures.mixed_analysis(ast,roots)
    if bad or missing:raise ValueError('complete actual writers required')
    base=effects.rtl.render_adapter(profile['ast']['module'],profile['ast']['program'],ast,analysis)
    count=3*len(analysis['plans'])+2*len(analysis['effects'])+len(roots)+len(analysis['plan_roots'])
    expected,count,rows,_=effects.extend(ast,profile['ast'],analysis,base,count)
    er=json.loads((ep/'report.json').read_text())
    if not(er.get('accepted')is True and er.get('coqc_exit')==er.get('coqchk_exit')==0
        and er.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
        and (ep/'EffectRequirements.v').read_text()==expected and(ep/'EffectRequirements.vo').exists()
        and origin.captures.audit_output((ep/'coqc.log').read_text(),count)):
        raise ValueError('checked unchanged complete effect provider required')
    outputs,_=transfer.sources.routes.analyze(ast)
    expected=f'Require Import {ast_module}.\n'+transfer.sources.render(profile['ast']['program'],outputs['ports'],True)
    sr=json.loads((sp/'report.json').read_text())
    if not(sr.get('accepted')is True and sr.get('coqc_exit')==sr.get('coqchk_exit')==0
        and sr.get('instruction_scope')==transfer.sources.scopes.for_input(ast_path,ast_module)
        and sr.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
        and (sp/'SourceRequirements.v').read_text()==expected
        and transfer.sources.audit((sp/'coqc.log').read_text(),3*len(outputs['ports'])+6)):
        raise ValueError('checked unchanged ISA-computed source R required')
    output.mkdir(parents=True,exist_ok=False)
    source=f'Require Import {ast_module}.\n'+render(profile['ast']['program'],rows)
    path=output/'ComputedEffectR.v';path.write_text(source)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for p in paths:flags+=['-R',p['directory'],p['namespace']]
    flags+=['-R',str(ep.resolve()),'GeneratedEffectRequirements',
        '-R',str(sp.resolve()),'GeneratedSourceRequirements',
        '-R',sr['provider'],'GeneratedOperandRoutes','-R',sr['isa_provider'],'GeneratedISAInputs',
        '-R',str(output.resolve()),'GeneratedComputedEffectR']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,
        fields=len(rows),roots=roots,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        old_inv_read=False,complete_R_generated=False,generated_conditions_established=False,
        actual_queue_transition_proved=False,reference_token_binding_proved=False)
    if c.returncode==0:
        report['original_assumptions_only']=transfer.sources.audit('\nSOURCE_REFERENCE_AUDIT\n'+c.stdout,len(rows))
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedComputedEffectR.ComputedEffectR'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
            accepted=k.returncode==0 and report['original_assumptions_only'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','effect-provider','source-provider','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.effect_provider,a.source_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
