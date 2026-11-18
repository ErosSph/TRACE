"""Separate ADD/ADDI/JAL x0 retirement into the same Current3 relation."""
import argparse
import json
from pathlib import Path
import re
import time
import cpu_add_family_no_write as old
import cpu_control_family_joint as joint
import cpu_addi_fetch_reference as fetch
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

NS='GeneratedControlFamilyNoWrite'
J='GeneratedControlFamilyJoint.ControlFamilyJoint'
W='GeneratedControlFamilyWriteback.ControlFamilyWriteback'
S='GeneratedControlFamilySources.ControlFamilySources'
F='CPUISAControlFamilyReferenceValues'
P='GeneratedJalProducerControls.JalProducerControls'
once=joint.replace_once

def bind_current3_physical(source):
    source=source.replace(J+'.A.H.G.sample_evidence','GeneratedCapturedReads.CapturedReadAddresses.sample_evidence')
    for short,target in [('H','GeneratedCapturedHistoryBoot.CapturedHistoryBoot'),
      ('C','GeneratedCapturedHistoryBoot.CapturedHistoryBoot.C'),
      ('Q','GeneratedPhasePendingCommit.PhasePendingCommit'),('V','GeneratedValidResult.ValidResult'),
      ('O','GeneratedOperandResultJoint.OperandResultJoint')]:
        source=source.replace(J+'.'+short+'.',target+'.')
    return source

def render(c,raw,profile,plan,selector,pending):
    source,exports=old.render(c,raw,profile,plan,selector,pending)
    source=source.replace('GeneratedAddFamilyJoint.AddFamilyJoint',J).replace('GeneratedAddFamilyWriteback.AddFamilyWriteback',W)
    source=source.replace('CPUISAAddFamilyReferenceValues',F)
    source=once(source,' GeneratedWritebackRF.WritebackRF.',' GeneratedWritebackRF.WritebackRF\n Ex.External.CPUISAJalSuccessEffects Ex.External.CPUISAJalEffects\n GeneratedFetchReference.FetchReference GeneratedJalLinkPhase.JalLinkPhase.')
    source=once(source,'Local Opaque','Local Notation reference_pc := GeneratedFetchReference.FetchReference.recorded_pc.\nLocal Opaque')
    source=once(source,'{word_ok:word.ok word}{registers_ok:map.ok Registers}.','{word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.')
    source=source.replace('(reference_pc:Token->Z)',' ')
    for name in [J+'.Current',J+'.OperandClause',J+'.ResultJoint',J+'.actual_result_phase',W+'.operand_clause_idle','original_family_x0_RF_frame']:
        source=source.replace(name+' reference_pc ',name+' ')
    # x0 frame is a statement about successful original execution, not a
    # promised aligned target or an assumed run1 result.
    x0add='(exists rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi 0%Z rs imm)))'
    x0three='(exists rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi 0%Z rs imm)) \\/\n (exists imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal 0%Z imm)))'
    if source.count(x0add)!=2:raise ValueError('both x0 classification declarations must be original')
    source=source.replace(x0add,x0three)
    source=once(source,'destruct HD as[[rs1[rs2 HD]]|[rs[imm HD]]].','destruct HD as[[rs1[rs2 HD]]|[[rs[imm HD]]|[imm HD]]].')
    marker='exact(HR i HI). }'
    source=once(source,marker,'''exact(HR i HI).
   - pose proof(CPUISAJalSuccessEffects.original_token_jal_effect reference_pc token_word token before after 0%Z imm HS HD)as HR.
     change(ISAProjectedRegisterEffects before after [])in HR;exact HR. }''')
    source=source.replace('CPUReferenceAddFamilyProducers.computed_value_implies_family',F+'.computed_value_implies_family')
    source=once(source,'as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].','as[[rd[rs1[rs2 HD]]]|[[rd[rs[imm HD]]]|[rd[imm HD]]]].')
    source=once(source,'right;exists rs,imm;exact HD. }',f'''right;left;exists rs,imm;exact HD.
   - pose proof(actual_valid_WB_destination image events ev token(Decode.Jal rd imm)rd [] HE HEv HV HT HD eq_refl)as HDest.
     change(norm 5(read_signal(phase_driven_state {profile['ast']['program']} ev pre){selector['write']['index_root']})=rd)in HDest.
     assert(Hrd:rd=0%Z)by congruence;rewrite Hrd in HD;right;right;exists imm;exact HD. }}''')
    context=J+'.Current initial retired current pre'
    source=once(source,context,'CPUISAJalEffects.NextPCAligned initial ->\n '+context)
    source=once(source,'HE HEv HF HR HV HZero HCurrent.','HE HEv HF HR HV HZero HInitial HCurrent.')
    source=source.replace('image events ev HE HEv HN HOp HResults','image events ev HE HEv HN HInitial HOp HResults')
    source=source.replace('FAMILY_ZERO_AUDIT','CONTROL_FAMILY_ZERO_AUDIT')
    return bind_current3_physical(source.replace(W,S)),exports

def accepted_paths(folder,stem,namespace,raw):
    folder=Path(folder);r=old.verified(folder,stem)
    if r['ast_sha256']!=raw['source_sha256']or r.get('old_inv_read')is not False:raise ValueError('same original AST and no old whole invariant required')
    if joint.digest((folder/(stem+'.vo')).read_bytes())!=r['object_sha256']:raise ValueError('changed accepted object')
    return json.loads((folder/'providers.json').read_text())+[dict(namespace=namespace,directory=str(folder.resolve()))]

def native(out,stem,namespace,source,exports,paths,plan,raw,context='',native_budget_seconds=1200,
           aggregate_audit=False,collect_resources=False):
    out=Path(out).resolve();out.mkdir(parents=True,exist_ok=False)
    bindings={}
    for row in paths:
        if row['namespace']in bindings and bindings[row['namespace']]!=row['directory']:raise ValueError('conflicting original provider')
        bindings[row['namespace']]=row['directory']
    paths=[dict(namespace=k,directory=v)for k,v in bindings.items()]
    env=old.family.derived.controls.history.admission.verify_environment_paths(paths)
    audit_metadata=None
    if aggregate_audit:
        from cpu_shared_assumption_audit import aggregate
        source,audit_metadata=aggregate(source,exports)
    audit_count=1 if aggregate_audit else len(exports)
    target=out/(stem+'.v');target.write_text(source)
    for name,value in [('providers',paths),('plan',plan),('exports',exports)]: (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(old.family.derived.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out),namespace]
    if native_budget_seconds<=0:raise ValueError('native point budget exhausted; additional user approval required')
    start=time.monotonic();remaining=lambda:max(.1,native_budget_seconds-(time.monotonic()-start))
    def run(command,log,timeout):
        if collect_resources:
            command=['/usr/bin/time','-v','-o',str(log.with_suffix('.resources')),*command]
        return run_stage(command,log,timeout)
    cc,ct=run(['_opam/bin/coqc','-time',*flags,str(target)],out/'coqc.log',remaining())
    marker={'ControlFamilyNoWrite':'CONTROL_FAMILY_ZERO_AUDIT','ControlFamilyFalling':'CONTROL_FAMILY_FALLING_AUDIT',
      'ControlFamilyMemoryFalling':'CONTROL_FAMILY_MEMORY_FALL_AUDIT',
      'ControlFamilyObserver':'CONTROL_FAMILY_OBSERVER_AUDIT','ControlFamilyMemoryCycle':'CONTROL_FAMILY_CYCLE_AUDIT',
      'ControlFamilyJalWait':'CONTROL_FAMILY_JAL_WAIT_AUDIT','ControlFamilyCredit':'CONTROL_FAMILY_CREDIT_AUDIT',
      'ControlFamilyITree':'CONTROL_FAMILY_ITREE_AUDIT',
      'DataControlITree':'DATA_CONTROL_ITREE_AUDIT',
      'DataOpITree':'DATAOP_ITREE_AUDIT',
      'BeqITree':'BEQ_ITREE_AUDIT',
      'BranchITree':'BRANCH_ITREE_AUDIT',
      'JumpITree':'JUMP_ITREE_AUDIT',
      'DataControlITreeExamples':'DATA_CONTROL_ITREE_EXAMPLES_AUDIT',
      'ControlFamilyITreeExamples':'CONTROL_FAMILY_ITREE_EXAMPLES_AUDIT',
      'DataControlJoint':'DATA_CONTROL_JOINT_AUDIT'}[stem]
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=ct,ast_sha256=raw['source_sha256'],source_sha256=joint.digest(source.encode()),old_inv_read=False,Current2_changed=False,original_environment_input_hashes=env,baseline_assumptions=sorted(ALLOWED_AXIOMS))
    report['native_budget_seconds']=native_budget_seconds
    if cc.returncode==0:
        ax=audit_all_exports(cc.stdout.split(marker)[-1],audit_count);report['assumptions']=sorted(ax)
        baseline=out/'Baseline.v'
        baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\nGoal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\nPrint Assumptions CPUISAInstructionExecution.token_execute.\n')
        bc,bt=run(['_opam/bin/coqc',*flags,str(baseline)],out/'baseline.log',remaining())
        allowed=old.parse_assumptions(bc.stdout)if bc.returncode==0 else set()
        report.update(baseline_exit=bc.returncode,baseline_timed_out=bt,baseline_assumptions=sorted(allowed))
        kk,kt=run(['_opam/bin/coqchk','-silent',*flags,'-norec',namespace+'.'+stem],out/'coqchk.log',remaining());report.update(coqchk_exit=kk.returncode,coqchk_timed_out=kt)
        if bc.returncode==kk.returncode==0 and not(ax-allowed)and not(allowed-ALLOWED_AXIOMS):
            header=source[:source.index('Local Opaque')]
            audit=header+'Require Import '+namespace+'.'+stem+'.\nImport '+stem+'.\nSection ExactTypes.\n'+context
            for n in exports:
                audit+='Definition exact_'+n+' : '+fetch.declaration(source,n).removeprefix('forall ,\n')+' := '+stem+'.'+n+'.\n'
            audit+='End ExactTypes.\nGoal True. idtac "CONTROL_FAMILY_EXACT". exact I. Qed.\n'+''.join('Print Assumptions exact_'+n+'.\n'for n in exports)
            exact_audit_metadata=None
            if aggregate_audit:
                audit,exact_audit_metadata=aggregate(audit,['exact_'+n for n in exports])
            af=out/'ExactTypes.v';af.write_text(audit)
            ac,at=run(['_opam/bin/coqc','-time',*flags,str(af)],out/'exact-types.coqc.log',remaining())
            report.update(target_types_exit=ac.returncode,target_types_timed_out=at,expected_target_types=len(exports))
            if ac.returncode==0:
                aa=audit_all_exports(ac.stdout.split('CONTROL_FAMILY_EXACT')[-1],audit_count)
                ak,akt=run(['_opam/bin/coqchk','-silent',*flags,'-norec',namespace+'.ExactTypes'],out/'exact-types.coqchk.log',remaining())
                report.update(target_types_coqchk_exit=ak.returncode,target_types_coqchk_timed_out=akt)
                report['accepted']=ak.returncode==0 and not(aa-allowed)and not(allowed-ALLOWED_AXIOMS)
                report['assumptions_audit_passed']=not(ax-allowed)and not(aa-allowed)and not(allowed-ALLOWED_AXIOMS)
                report['assumptions_closed']=not ax and not aa
            if aggregate_audit:report['exact_audit_aggregation']=exact_audit_metadata
    report['seconds']=time.monotonic()-start
    if aggregate_audit:report['audit_aggregation']=audit_metadata
    if report['accepted']:report['object_sha256']=joint.digest(target.with_suffix('.vo').read_bytes())
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

def check(c,current,sources,output):
    raw,profile,_=old.family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    paths=accepted_paths(current,'ControlFamilyJoint','GeneratedControlFamilyJoint',raw)
    paths+=accepted_paths(sources,'ControlFamilySources','GeneratedControlFamilySources',raw)
    bindings={row['namespace']:row['directory']for row in paths}
    plan=old.family.discover(c,raw)
    selector=json.loads((Path(bindings['GeneratedWritebackSelector'])/'plan.json').read_text())
    pending=json.loads((Path(plan['queue_context'])/'plan.json').read_text())
    indices=[i for i,node in enumerate(pending['nodes'][:-1])if node['index']==plan['head']['index']and node['process']==plan['head']['process']]
    if len(indices)!=1:raise ValueError('ambiguous actual capture-idle rule')
    plan['capture_idle_index']=indices[0]
    wbplan=dict(operands=plan,selector=selector)
    source,exports=render(c,raw,profile,plan,selector,pending)
    ctx='''Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}
 {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.
'''
    return native(output,'ControlFamilyNoWrite',NS,source,exports,paths,wbplan,raw,ctx)

if __name__=='__main__':
    a=argparse.ArgumentParser(description=__doc__);a.add_argument('--inputs',required=True);a.add_argument('--current',required=True);a.add_argument('--sources',required=True);a.add_argument('--output',required=True);args=a.parse_args()
    c=json.loads(Path('framework/bzeeno-cdfg-add-inputs.json').read_text());c.update(json.loads(Path(args.inputs).read_text()))
    r=check(c,args.current,args.sources,args.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
