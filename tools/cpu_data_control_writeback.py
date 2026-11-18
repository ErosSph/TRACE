"""Actual four-class RF writeback; pure 21-op values do not widen RTL scope."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_joint as family
import cpu_control_family_writeback as original
import cpu_control_family_sources as sources
import cpu_control_family_no_write as checked

NS='GeneratedDataControlWriteback'
STEM='DataControlWriteback'
J='GeneratedDataControlJoint.DataControlJoint'
F='GeneratedDataControlFrontier.DataControlFrontier'
S='GeneratedDataControlSources.DataControlSources'
SUB='GeneratedSubProducerControls.SubProducerControls'
PROV='GeneratedCaptureProvenance.CaptureProvenance'
H='GeneratedCapturedHistoryBoot.CapturedHistoryBoot'
CONTEXT='''Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.
'''


def render(c,raw,profile,plan,selector):
    text,exports=original.render(c,raw,profile,plan,selector)
    text=text.replace(original.J,J).replace('CPUISAControlFamilyReferenceValues','CPUISADataControlReferenceValues')
    text=text.replace('Local Opaque',f'Require Import {F} {S} {SUB} {PROV} Lang.ExtendedSVCaptureContent.\nLocal Opaque',1)
    pk='(H.boot_history image events)'
    helper=f'''Lemma actual_wb_class image events token:
 C.C.chain_tag2(snd{pk})=Some token ->{F}.ClassifiedControl {pk} ->{F}.FourFamilyToken token.
Proof. intros HT HC;pose proof({PROV}.boot_recorded image events)as[_[_[_ HW]]].
 exact(ExtendedSVCaptureContent.recorded_content {F}.FourFamilyToken _ _ HC(HW token HT)). Qed.
'''
    text=text.replace('Lemma addi_load_zero',helper+'Lemma addi_load_zero',1)
    block=re.search(r'Theorem jal_selects_alu\b[\s\S]*?Qed\.',text).group(0)
    sub=block.replace('jal_selects_alu','sub_selects_alu').replace('token rd imm','token rd rs1 rs2').replace('Decode.Jal rd imm','Decode.Sub rd rs1 rs2')
    sub=sub.replace(original.P+'.actual_jal_producer_controls_2',SUB+'.actual_sub_producer_controls_2')
    data=re.search(r'Theorem actual_jal_write_data\b[\s\S]*?Qed\.',text).group(0)
    data=data.replace('actual_jal_write_data','actual_sub_write_data').replace('jal_selects_alu','sub_selects_alu').replace('token rd imm','token rd rs1 rs2').replace('Decode.Jal rd imm','Decode.Sub rd rs1 rs2')
    text=text.replace('Section ISA.',sub+'\n'+data+'\nSection ISA.',1)
    start=text.index('Theorem operand_clause_idle');stop=text.index('\nQed.',start)
    proof=text.index('\nProof.',start)
    text=text[:proof]+f'\nProof. exact({S}.operand_clause_idle initial ledger image events ev).'+text[stop:]
    start=text.index('Theorem actual_family_writeback_restores_RF');stop=text.index('\nQed.',start)
    segment=text[start:stop]
    segment=segment.replace('instruction_effect reference_pc token_word token before=Some after ->',
        F+'.FourFamilyToken token ->\n instruction_effect reference_pc token_word token before=Some after ->')
    segment=segment.replace('HE HEv HT HSTEP','HE HEv HT HFamily HSTEP')
    segment=re.sub(r'destruct\(F\.computed_value_implies_family[\s\S]*?as\[\[rd\[rs1\[rs2 HD\]\]\]\|\[\[rd\[rs\[imm HD\]\]\]\|\[rd\[imm HD\]\]\]\]\.',
        'destruct HFamily as[[[rd[rs1[rs2 HD]]]|[[rd[rs[imm HD]]]|[rd[imm HD]]]]|[rd[rs1[rs2 HD]]]].',segment,count=1)
    if 'computed_value_implies_family'in segment:raise ValueError('wide reference family cannot stand in for four-class hardware history')
    segment=segment.replace('unfold F.computed_value,CPUISAAddFamilyReferenceValues.computed_value in HValue;rewrite HD,HX,HY in HValue;',
        'rewrite(F.computed_add token_word token before rd rs1 rs2 x y HD HX HY)in HValue;')
    segment=segment.replace('unfold F.computed_value,CPUISAAddFamilyReferenceValues.computed_value in HValue;rewrite HD,HX in HValue;',
        'rewrite(F.computed_addi token_word token before rd rs imm x HD HX)in HValue;')
    first=segment[segment.index('\n - destruct(Destination.'):segment.index('\n - destruct(Destination.',segment.index('\n - destruct(Destination.')+1)]
    subbranch=first.replace('Decode.Add rd rs1 rs2','Decode.Sub rd rs1 rs2').replace('S.actual_add_write_data image events ev token rd rs1 rs2 HE HEv HT HD',
        'actual_sub_write_data image events ev token rd rs1 rs2 HE HEv (V.actual_write_is_valid image events ev HE HEv HG1) HT HD')
    subbranch=subbranch.replace('original_add_effect','original_sub_effect').replace('F.computed_add ','F.computed_sub ').replace('Utility.add x y','Utility.sub x y')
    text=text[:start]+segment+subbranch+text[stop:]
    start=text.index('Theorem actual_family_write_preserves_Current')
    text=text[:start]+text[start:].replace('CPUISAJalEffects.NextPCAligned initial ->',
        'CPUISAJalEffects.NextPCAligned initial ->\n '+F+'.ClassifiedControl '+pk+' ->',1)
    text=text.replace('HG1 HInitial HCurrent.','HG1 HInitial HCapturedClass HCurrent.')
    marker=' destruct HCurrent as[HN HC HR HResults HOp [frontier HChain]].'
    text=original.once(text,marker,' pose proof(actual_wb_class image events token HT HCapturedClass)as HFamily.\n'+marker)
    text=text.replace('HE HEv HT HSTEP HP','HE HEv HT HFamily HSTEP HP')
    text=text.replace('CONTROL_FAMILY_WRITEBACK_AUDIT','DATA_CONTROL_WRITEBACK_AUDIT')
    exports+=['actual_wb_class','sub_selects_alu','actual_sub_write_data']
    text+=''.join('Print Assumptions '+n+'.\n'for n in exports[-3:])
    return sources.qualify(text),exports


def prepare(c,current,source_provider,frontier,sub):
    raw,profile,_=family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    paths=[]
    for folder,stem,ns in [(current,'DataControlJoint','GeneratedDataControlJoint'),
        (source_provider,'DataControlSources','GeneratedDataControlSources'),
        (frontier,'DataControlFrontier','GeneratedDataControlFrontier'),
        (sub,'SubProducerControls','GeneratedSubProducerControls')]:
        paths+=checked.accepted_paths(folder,stem,ns,raw)
    bindings={r['namespace']:r['directory']for r in paths}
    plan=family.discover(c,raw)
    selector=json.loads((Path(bindings['GeneratedWritebackSelector'])/'plan.json').read_text())
    pending=json.loads((Path(plan['queue_context'])/'plan.json').read_text())
    indexes=[i for i,n in enumerate(pending['nodes'][:-1])if n['index']==plan['head']['index']and n['process']==plan['head']['process']]
    if len(indexes)!=1:raise ValueError('ambiguous real EX capture idle rule')
    plan['capture_idle_index']=indexes[0];plan['writeback_valid']=pending['nodes'][-1]['valid']
    return raw,profile,plan,selector,pending,paths


def native(output,stem,namespace,text,exports,paths,raw,plan,prior_attempts=(),marker=None):
    elapsed=0.0
    for folder in prior_attempts:
        folder=Path(folder);r=json.loads((folder/'report.json').read_text());old=(folder/(stem+'.v')).read_text()
        if hashlib.sha256(old.encode()).hexdigest()!=r['source_sha256']:raise ValueError('changed prior evidence')
        if any(checked.fetch.declaration(old,n)!=checked.fetch.declaration(text,n)for n in exports):raise ValueError('public declaration changed')
        elapsed+=r['seconds']
    known={p.parent.resolve()for p in Path('results').glob('r-'+re.sub(r'(?<!^)(?=[A-Z])','-',stem).lower()+'-*/report.json')}
    if known!={Path(p).resolve()for p in prior_attempts}:raise ValueError('all earlier attempts must be charged')
    if elapsed>=1200:raise ValueError('point exhausted; actual-timeout same-statement review required')
    out=Path(output).resolve();out.mkdir(parents=True,exist_ok=False)
    binding={}
    for row in paths:
        if row['namespace']in binding and binding[row['namespace']]!=row['directory']:raise ValueError('conflicting provider')
        binding[row['namespace']]=row['directory']
    paths=[dict(namespace=n,directory=d)for n,d in binding.items()]
    env=family.derived.controls.history.admission.verify_environment_paths(paths)
    (out/(stem+'.v')).write_text(text)
    for name,value in [('providers',paths),('plan',plan),('exports',exports)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(family.derived.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out),namespace]
    start=time.monotonic();remaining=lambda:max(.1,1200-elapsed-(time.monotonic()-start))
    cc,ct=checked.run_stage(['_opam/bin/coqc','-time',*flags,str(out/(stem+'.v'))],out/'coqc.log',remaining())
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=ct,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],old_inv_read=False,original_environment_input_hashes=env,
        hardware_classes=['ADD','ADDI','JAL','SUB'],scope=plan.get('scope','real write/no-write restores Current4; not 21 RTL classes'))
    if cc.returncode==0:
        axioms=checked.audit_all_exports(cc.stdout.split(marker or 'DATA_CONTROL_'+('WRITEBACK'if stem==STEM else 'ZERO')+'_AUDIT')[-1],len(exports))
        baseline=out/'Baseline.v';baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\nGoal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\nPrint Assumptions CPUISAInstructionExecution.token_execute.\n')
        bc,bt=checked.run_stage(['_opam/bin/coqc',*flags,str(baseline)],out/'baseline.log',remaining())
        allowed=checked.old.parse_assumptions(bc.stdout)if bc.returncode==0 else set()
        header=text[:text.index('Local Opaque')]
        audit=header+'Require Import '+namespace+'.'+stem+'.\nImport '+stem+'.\nSection ExactTypes.\n'+CONTEXT
        for n in exports:audit+='Definition exact_'+n+' : '+checked.fetch.declaration(text,n).removeprefix('forall ,\n')+' := '+stem+'.'+n+'.\n'
        audit+='End ExactTypes.\nGoal True. idtac "EXACT_TYPES". exact I. Qed.\n'+''.join('Print Assumptions exact_'+n+'.\n'for n in exports)
        af=out/'ExactTypes.v';af.write_text(audit)
        ac,at=checked.run_stage(['_opam/bin/coqc','-time',*flags,str(af)],out/'exact-types.coqc.log',remaining())
        aa=checked.audit_all_exports(ac.stdout.split('EXACT_TYPES')[-1],len(exports))if ac.returncode==0 else set()
        kk,kt=checked.run_stage(['_opam/bin/coqchk','-silent',*flags,'-norec',namespace+'.'+stem,'-norec',namespace+'.ExactTypes'],out/'coqchk.log',remaining())if ac.returncode==0 else(None,False)
        good=bc.returncode==ac.returncode==0 and kk is not None and kk.returncode==0 and not(axioms-allowed)and not(aa-allowed)and not(allowed-checked.ALLOWED_AXIOMS)
        report.update(accepted=good,baseline_exit=bc.returncode,baseline_timed_out=bt,baseline_assumptions=sorted(allowed),assumptions=sorted(axioms),
            target_types_exit=ac.returncode,target_types_timed_out=at,expected_target_types=len(exports),coqchk_exit=kk.returncode if kk else None,
            coqchk_timed_out=kt,assumptions_audit_passed=good)
    report.update(seconds=time.monotonic()-start,prior_seconds=elapsed)
    report['cumulative_seconds']=elapsed+report['seconds']
    if report['accepted']:report['object_sha256']=hashlib.sha256((out/(stem+'.vo')).read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def check(c,current,sources_provider,frontier,sub,output,prior_attempts=()):
    raw,profile,plan,selector,pending,paths=prepare(c,current,sources_provider,frontier,sub)
    text,exports=render(c,raw,profile,plan,selector)
    return native(output,STEM,NS,text,exports,paths,raw,dict(operands=plan,selector=selector),prior_attempts)


if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__)
    for n in ['current','sources','frontier','sub','output']:a.add_argument('--'+n,required=True)
    a.add_argument('--prior-attempt',action='append',default=[]);args=a.parse_args()
    r=check(family.inputs(),args.current,args.sources,args.frontier,args.sub,args.output,args.prior_attempt)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
