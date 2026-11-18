"""Build the ADD/ADDI RAM-inclusive current R and its real seeded boot.

Class/frontier clauses describe the current state; no future preservation is
assumed. RAM zero comes only from the unchanged original seed/bootstrap.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_joint as family
import cpu_cdfg_ram_initial as ram
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def digest(data):
    return hashlib.sha256(data).hexdigest()


def providers(c, initial, raw):
    bindings={};receipts=[]
    for folder,stem,ns in [(initial,'AddFamilyInitial','GeneratedAddFamilyInitial'),
        (c['ledger_initial'],'LedgerInitial','GeneratedLedgerInitial'),
        (c['frontier_initial'],'FrontierInitial','GeneratedFrontierInitial'),
        (c['ram_initial'],'RAMInitial','GeneratedRAMInitial')]:
        folder=Path(folder);r=json.loads((folder/'report.json').read_text());source=folder/(stem+'.v')
        if not(r.get('accepted')and r['coqc_exit']==r['coqchk_exit']==0 and r['old_inv_read']is False
            and r['ast_sha256']==raw['source_sha256']and digest(source.read_bytes())==r['source_sha256']
            and digest(source.with_suffix('.vo').read_bytes())==r['object_sha256']):
            raise ValueError('same-original checked boot provider required: '+stem)
        for row in json.loads((folder/'providers.json').read_text())+[dict(namespace=ns,directory=str(folder.resolve()))]:
            if row['namespace']in bindings and bindings[row['namespace']]!=row['directory']:
                raise ValueError('incompatible boot physical namespace')
            bindings[row['namespace']]=row['directory']
        receipts.append(dict(namespace=ns,directory=str(folder.resolve()),source_sha256=r['source_sha256'],object_sha256=r['object_sha256']))
    return [dict(namespace=k,directory=v)for k,v in bindings.items()],receipts


def render(c,profile,plan):
    p=profile['ast']['program'];bank=plan['byte_bank'];width,root=bank['width'],bank['root']
    if width<=0 or width%8:raise ValueError('byte-bank physical width is not byte aligned')
    h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';f=h+'.F'
    j='GeneratedAddFamilyJoint.AddFamilyJoint';ni='GeneratedAddFamilyInitial.AddFamilyInitial'
    li='GeneratedLedgerInitial.LedgerInitial';fi='GeneratedFrontierInitial.FrontierInitial';ri='GeneratedRAMInitial.RAMInitial'
    q='GeneratedPhasePendingCommit.PhasePendingCommit';led='GeneratedAdmissionLedger.AdmissionLedger'
    ref='GeneratedFetchReference.FetchReference';af='GeneratedAdmissionFrontier.AdmissionFrontier'
    ar='GeneratedAdmissionReference.AdmissionReference';rq='GeneratedRAMJoint.RAMJoint'
    cl='GeneratedClockCycleJoint.CycleJoint';pc=ref+'.recorded_pc'
    source=f'''From Coq Require Import List ZArith Bool.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVCaptureContent Lang.ExtendedSVPackedROM
 Ex.External.CPUGeneratedJointTemplate Ex.External.CPUOriginalISAReference Ex.External.CPUByteBankRelation
 Ex.External.CPUProgramROM Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedAddFamilyJoint.AddFamilyJoint GeneratedAddFamilyInitial.AddFamilyInitial
 GeneratedLedgerInitial.LedgerInitial GeneratedFrontierInitial.FrontierInitial GeneratedRAMInitial.RAMInitial
 GeneratedAdmissionLedger.AdmissionLedger GeneratedAdmissionFrontier.AdmissionFrontier
 GeneratedAdmissionReference.AdmissionReference GeneratedFetchReference.FetchReference
 GeneratedRAMJoint.RAMJoint GeneratedClockCycleJoint.CycleJoint.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVCaptureBirth CPUGeneratedJointTemplate CPUOriginalISAReference.
Local Opaque {p} PhaseSemantics phase_run {f}.boot {h}.boot_history.
Definition FamilyToken token:Prop:=
 (exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
 (exists rd rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm)).
Definition ClassifiedFamily(packed:{h}.C.Packed):Prop:=ExtendedSVCaptureContent.Related FamilyToken(fst packed).
Theorem actual_boot_classified_family image:ClassifiedFamily({h}.boot_history image []).
Proof. unfold ClassifiedFamily;rewrite {li}.actual_boot_history_empty;apply ExtendedSVCaptureContent.empty_related. Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Definition FamilyMemoryJoint words i initial retired committed pre packed:Prop:=
 {j}.Current {pc} initial retired committed pre packed /\\
 {led}.LedgerRange pre packed retired /\\
 ClassifiedFamily packed /\\
 {rq}.StoreQuiet pre /\\
 CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat pre(getDataMem committed) /\\
 exists frontier,EffectChain(instruction_effect {pc} token_word)committed({q}.actual_pending pre packed)frontier /\\
 {ar}.FrontierAt pre frontier i words /\\{af}.NextPCAligned frontier.
'''
    fields=[
        ('current',f'{j}.Current {pc} initial retired committed pre packed','HJ'),
        ('ledger',f'{led}.LedgerRange pre packed retired','HL'),
        ('classified','ClassifiedFamily packed','HC'),
        ('quiet',f'{rq}.StoreQuiet pre','HQ'),
        ('memory',f'CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat pre(getDataMem committed)','HM'),
        ('frontier',f'exists frontier,EffectChain(instruction_effect {pc} token_word)committed({q}.actual_pending pre packed)frontier /\\ {ar}.FrontierAt pre frontier i words /\\ {af}.NextPCAligned frontier','HF')]
    exports=['actual_boot_classified_family']
    for name,statement,proof in fields:
        source+=f'''Theorem family_{name} words i initial retired committed pre packed:
 FamilyMemoryJoint words i initial retired committed pre packed ->{statement}.
Proof. intros[HJ[HL[HC[HQ[HM HF]]]]];exact {proof}. Qed.
'''
        exports.append('family_'+name)
    source+=f'''Theorem actual_boot_family_memory_joint words:
 FamilyMemoryJoint words 0%nat({fi}.original_initial words)[]({fi}.original_initial words)
 ({f}.boot(ExtendedSVPackedROM.pack words))({h}.boot_history(ExtendedSVPackedROM.pack words)[]).
Proof.
 pose proof({ni}.actual_boot_current {pc}(ExtendedSVPackedROM.pack words)
  (FormalSpec.formal_initial_imem(CPUProgramROM.entries words)))as HJ.
 pose proof({li}.actual_boot_ledger_range(ExtendedSVPackedROM.pack words))as HL.
 pose proof(actual_boot_classified_family(ExtendedSVPackedROM.pack words))as HC.
 destruct({ri}.actual_boot_original_memory(ExtendedSVPackedROM.pack words)
  (FormalSpec.formal_initial_imem(CPUProgramROM.entries words)))as[HQ HM].
 destruct({fi}.actual_boot_original_frontier words)as[HF HNext].
 refine(conj HJ(conj HL(conj HC(conj HQ(conj HM _))))).
 exists({fi}.original_initial words);split.
 - rewrite {li}.actual_boot_pending_empty;constructor.
 - exact(conj HF HNext).
Qed.
Theorem actual_boot_boundary_and_family_joint words:
 {cl}.ClockBoundary({f}.boot(ExtendedSVPackedROM.pack words)) /\\
 FamilyMemoryJoint words 0%nat({fi}.original_initial words)[]({fi}.original_initial words)
 ({f}.boot(ExtendedSVPackedROM.pack words))({h}.boot_history(ExtendedSVPackedROM.pack words)[]).
Proof. exact(conj({fi}.actual_boot_clock_boundary(ExtendedSVPackedROM.pack words))(actual_boot_family_memory_joint words)). Qed.
End OriginalISA.
Goal True. idtac "FAMILY_MEMORY_AUDIT". exact I. Qed.
'''
    exports+=['actual_boot_family_memory_joint','actual_boot_boundary_and_family_joint']
    source+=''.join(f'Print Assumptions {name}.\n'for name in exports)
    return source,exports


def check(c,initial,output,norec_each_from=None):
    raw,profile,_=family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    paths,receipts=providers(c,initial,raw)
    graph=ram.pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    plan=ram.discover(c,raw,profile,graph)
    oldplan=json.loads((Path(c['ram_initial'])/'plan.json').read_text())
    if json.loads(json.dumps(plan['byte_bank']))!=oldplan['byte_bank']:
        raise ValueError('same seeded original RAM physical plan required')
    source,exports=render(c,profile,plan);file=out/'AddFamilyMemoryJoint.v';file.write_text(source)
    if norec_each_from:
        prior=Path(norec_each_from);previous=json.loads((prior/'report.json').read_text())
        if not(previous['coqchk_exit']==124 and previous['coqchk_timed_out']and previous['seconds']>=1200
            and previous['coqc_exit']==previous['target_types_exit']==0
            and (prior/'AddFamilyMemoryJoint.v').read_text()==source
            and previous['source_sha256']==digest(source.encode())):
            raise ValueError('same checked native target and actual timeout required for the unique check-mode repair')
    for name,data in [('providers',paths),('receipts',receipts),('plan',plan),('exports',exports),('inputs',c)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(family.derived.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedAddFamilyMemoryJoint']
    root=family.derived.controls.history.admission.observation.origin.ROOT
    start=time.monotonic()
    help_exit=None
    if norec_each_from:
        help_result,_=run_stage([str(root/'_opam/bin/coqchk'),'--help'],out/'coqchk-help.log',30)
        help_exit=help_result.returncode
    baseline=out/'Baseline.v';baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\nGoal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\nPrint Assumptions CPUISAInstructionExecution.token_execute.\n')
    bc,bt=run_stage([str(root/'_opam/bin/coqc'),*flags,str(baseline.resolve())],out/'baseline.log',1200)
    allowed=parse_assumptions(bc.stdout)
    cc,ct=run_stage([str(root/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',max(.1,1200-(time.monotonic()-start)))
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=ct,baseline_exit=bc.returncode,
        source_sha256=digest(source.encode()),ast_sha256=raw['source_sha256'],graph_sha256=digest(Path(c['graph']).read_bytes()),
        exports=exports,old_inv_read=False,old_manual_CPU_initialization_used=False,
        family_RAM_inclusive_R_candidate_defined=True,actual_boot_family_memory_joint_proved=False,
        actual_cycle_preservation_proved=False,full_R_generated=False,infinite_itree_refinement_proved=False,
        memory_zero_is_original_seeded_boot_not_arbitrary_reset=True)
    report.update(performance_attempt=1 if norec_each_from else 0,optimization_baseline=norec_each_from,
        coqchk_help_exit=help_exit,independent_roots=['GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint','GeneratedAddFamilyMemoryJoint.TargetTypes'],
        dependency_policy='previously checked dependencies loaded, each named root independently kernel checked')
    if cc.returncode==0:
        axioms=audit_all_exports(cc.stdout.split('FAMILY_MEMORY_AUDIT')[-1],len(exports))
        audit=bc.returncode==0 and not(axioms-allowed)and not(axioms-ALLOWED_AXIOMS)
        types=source[:source.index('Definition FamilyToken')]
        types+='\nRequire Import GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint.\nImport GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint.\nSection OriginalISA.\n'
        types+=source.split('Section OriginalISA.\n',1)[1].split('Definition FamilyMemoryJoint',1)[0]
        headers={}
        for name in exports:
            m=re.search(r'Theorem '+name+r' ([A-Za-z0-9_ \n]+):(.*?)\nProof\.',source,re.S)
            if not m:raise ValueError('original public declaration type not found')
            binders,statement=m.groups();headers[name]=digest(m.group(0).removesuffix('\nProof.').encode())
            types+=f'Definition checked_{name} {binders}:{statement}\nProof. exact({name} {binders}). Qed.\n'
        types+='End OriginalISA.\n'
        typefile=out/'TargetTypes.v';typefile.write_text(types)
        if norec_each_from and types!=(Path(norec_each_from)/'TargetTypes.v').read_text():
            raise ValueError('check-mode repair must not change any original type audit source')
        (out/'original-header-sha256.json').write_text(json.dumps(headers,indent=2)+'\n')
        tc,tt=run_stage([str(root/'_opam/bin/coqc'),*flags,str(typefile.resolve())],out/'target-types.log',max(.1,1200-(time.monotonic()-start)))
        audit=audit and tc.returncode==0
        kk,kt=run_stage([str(root/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint','-norec','GeneratedAddFamilyMemoryJoint.TargetTypes'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(coqchk_exit=kk.returncode,coqchk_timed_out=kt,target_types_exit=tc.returncode,
            assumptions=sorted(axioms),baseline_assumptions=sorted(allowed),assumptions_audit_passed=audit,
            accepted=audit and kk.returncode==0,actual_boot_family_memory_joint_proved=audit and kk.returncode==0)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=digest(file.with_suffix('.vo').read_bytes())
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--initial',required=True);p.add_argument('--output',required=True)
    p.add_argument('--norec-each-from')
    a=p.parse_args();r=check(family.inputs(),a.initial,a.output,a.norec_each_from)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
