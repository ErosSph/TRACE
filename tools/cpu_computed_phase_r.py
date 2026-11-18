"""Connect raw scalar phase certificates to generated executable source R.
Never takes a caller-proved post-field equality; real trigger/copy rules derive it.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_computed_r_transfer as transfer
import cpu_operand_phase_requirements as phases
from cpu_certificate_acceptance import run_stage
origin=phases.origin

def render(program,module,rows):
    lines=['''From Coq Require Import List ZArith.
Require Import GeneratedScalarExpressions.ScalarExpressions
 GeneratedSourceRequirements.SourceRequirements GeneratedComputedRTransfer.ComputedRTransfer
 Ex.External.CPUComputedReferenceCut Ex.External.CPUGeneratedJointTemplate
 Ex.External.CPUOriginalISAReference Ex.External.CPUActualSourceCapture
 Ex.External.CPUActualCaptureReference Lang.ExtendedSV
 coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Import ExtendedSV CPUOriginalISAReference CPUComputedReferenceCut CPUGeneratedJointTemplate
 CPUActualSourceCapture CPUActualCaptureReference.
Section PhaseR.
Context {word:Interface.word 32}{BW:Bitwidth 32}
 {Registers:map.map Z word}{Mem:map.map word byte}{word_ok:word.ok word}{Token:Type}.
Variable token_pc token_word:Token->Z.
''']
    count=0;audits=[]
    for row in rows:
        r,w=row['root'],row['width'];proc=module+'.'+row['process']
        common=f''' NoDup(kept++added) ->
 EffectChain(instruction_effect token_pc token_word)initial retiring advanced ->
 (length retiring<=index)%nat ->
 lookup_before(instruction_effect token_pc token_word)same token initial(retiring++kept)=Some(index,reference) ->'''
        lines += [f'''Theorem root_{r}_computed_R_hold same ev pre initial advanced
 retiring kept added index token reference position:
 changed_signal ev<>{r}%nat ->
 process_matches_states pre(phase_driven_state {program} ev pre){proc}=false ->
{common}
 (computed_operand_R token_pc token_word same {w}%nat {r}%nat pre initial(retiring++kept)token position <->
 computed_operand_R token_pc token_word same {w}%nat {r}%nat
 (PhaseSemantics {program} ev pre)advanced(kept++added)token position).
Proof.
 intros HE HT HN HC HI HL.
 apply(computed_source_R_cycle token_pc token_word same {w}%nat {r}%nat pre
 (PhaseSemantics {program} ev pre)initial advanced retiring kept added index token reference position HN HC HI HL).
 rewrite(root_{r}_expression_phase ev pre HE),HT;reflexivity.
Qed.'''];count+=1
        audits.append(f'Print Assumptions root_{r}_computed_R_hold.')
        if w==32:
            lines += [f'''Theorem root_{r}_computed_R_capture same ev pre source initial advanced
 retiring kept added index token reference position:
 changed_signal ev<>{r}%nat ->
 capture_source {program} {proc} {r}%nat root_{r}_expression ev pre=Some source ->
{common}
 (computed_operand_R token_pc token_word same 32%nat source
 (phase_driven_state {program} ev pre)initial(retiring++kept)token position <->
 computed_operand_R token_pc token_word same 32%nat {r}%nat
 (PhaseSemantics {program} ev pre)advanced(kept++added)token position).
Proof.
 intros HE HS HN HC HI HL.
 apply(computed_source_R_transport token_pc token_word same 32%nat source {r}%nat
 (phase_driven_state {program} ev pre)(PhaseSemantics {program} ev pre)
 initial advanced retiring kept added index token reference position HN HC HI HL).
 exact(capture_value {program} {proc} {r}%nat root_{r}_expression ev pre source
 (root_{r}_expression_phase ev pre HE)HS).
Qed.'''];count+=1
            audits.append(f'Print Assumptions root_{r}_computed_R_capture.')
    return '\n'.join(lines)+'\nEnd PhaseR.\n'+'\n'.join(audits)+'\n',count

def check(ast_path,ast_module,phase_provider,transfer_provider,output):
    output=Path(output);phase_provider=Path(phase_provider);tp=Path(transfer_provider)
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    phase=json.loads((phase_provider/'report.json').read_text())
    rows=phase.get('outputs',[])
    if not rows:raise ValueError('no supported scalar phase certificates; not an empty success')
    roots=[r['root']for r in rows]
    _,residuals,actual,base,_=origin.expressions.proposal(profile,roots)
    stored=(phase_provider/'ScalarExpressions.v').read_text()
    if not(phase.get('phase_value_relations_checked')is True and not residuals
        and phase.get('coqc_exit')==phase.get('coqchk_exit')==0
        and phase.get('ast_sha256')==ast['source_sha256']
        and phase.get('generated_source_sha256')==hashlib.sha256(stored.encode()).hexdigest()
        and stored.startswith(base) and (phase_provider/'ScalarExpressions.vo').exists()
        and origin.captures.audit_output((phase_provider/'coqc.log').read_text(),phase['audited_exports'])):
        raise ValueError('checked exact raw scalar certificate prefix required')
    tr=json.loads((tp/'report.json').read_text())
    analysis,_=transfer.sources.routes.analyze(ast)
    expected=transfer.render(analysis['ports'])
    if not(tr.get('accepted')is True and tr.get('coqc_exit')==tr.get('coqchk_exit')==0
        and (tp/'ComputedRTransfer.v').read_text()==expected
        and tr.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
        and transfer.sources.audit('\nSOURCE_REFERENCE_AUDIT\n'+(tp/'coqc.log').read_text(),2)):
        raise ValueError('checked exact source R transport provider required')
    sp=Path(tr['provider']);sr=json.loads((sp/'report.json').read_text())
    output.mkdir(parents=True,exist_ok=False)
    source,count=render(profile['ast']['program'],ast['module'],actual)
    source=f'Require Import {ast_module}.\n'+source
    path=output/'ComputedPhaseR.v';path.write_text(source)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for p in paths:flags+=['-R',p['directory'],p['namespace']]
    flags+=['-R',str(phase_provider.resolve()),'GeneratedScalarExpressions',
        '-R',str(tp.resolve()),'GeneratedComputedRTransfer',
        '-R',str(sp.resolve()),'GeneratedSourceRequirements',
        '-R',sr['provider'],'GeneratedOperandRoutes','-R',sr['isa_provider'],'GeneratedISAInputs',
        '-R',str(output.resolve()),'GeneratedComputedPhaseR']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,
        fields=len(actual),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        omitted_route_roots=sorted({r['root']for r in phases.routes.discover(ast)['routes']
            if r['crossed_sampling_boundary']}-set(roots)),
        residuals=phase.get('residuals',[]),old_inv_read=False,complete_R_generated=False,
        actual_queue_transition_proved=False,reachable_control_conditions_proved=False)
    if c.returncode==0:
        report['original_assumptions_only']=transfer.sources.audit('\nSOURCE_REFERENCE_AUDIT\n'+c.stdout,count)
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedComputedPhaseR.ComputedPhaseR'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
            accepted=k.returncode==0 and report['original_assumptions_only'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','phase-provider','transfer-provider','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.phase_provider,a.transfer_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
