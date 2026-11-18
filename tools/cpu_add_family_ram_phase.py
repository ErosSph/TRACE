"""Derive ADD/ADDI non-store controls and actual RAM/quiet preservation."""
import argparse
import json
from pathlib import Path
import re
import time

import cpu_add_family_memory_joint as memory
from cpu_certificate_acceptance import run_stage,parse_assumptions,ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def render(c,profile,plan):
    p=profile['ast']['program'];h='GeneratedCapturedHistoryBoot.CapturedHistoryBoot';f=h+'.F'
    m='GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint';q='GeneratedCurrentControlFields.CurrentControlFields'
    r='GeneratedRAMJoint.RAMJoint';s='GeneratedStoreControl.StoreControl'
    reads='GeneratedCapturedReads.CapturedReadAddresses';invalid='GeneratedInvalidFetch.InvalidFetch'
    valid=plan['pair']['valid_root'];controller=plan['store_controller'];opcode=controller['opcode'];store=controller['root']
    root,width=plan['byte_bank']['root'],plan['byte_bank']['width']
    sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)';packed=f'({h}.boot_history image events)'
    common=f'''let pre:=phase_run {p} events({f}.boot image)in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 {m}.ClassifiedFamily {packed} ->'''
    source=f'''From Coq Require Import List ZArith Bool.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVStallFlush Lang.ExtendedSVCaptureContent
 Ex.External.CPUISAAddControlFields Ex.External.CPUISAAddiFields Ex.External.CPUOriginalISAReference
 Ex.External.CPUByteBankRelation Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties
 coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint GeneratedCurrentControlFields.CurrentControlFields
 GeneratedRAMJoint.RAMJoint GeneratedStoreControl.StoreControl GeneratedCapturedReads.CapturedReadAddresses
 GeneratedInvalidFetch.InvalidFetch.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVStallFlush.
Local Opaque {p} PhaseSemantics phase_run.
Theorem actual_family_store_controls_zero image events ev:
 {common}norm 1(read_signal {sample}{store}%nat)=0%Z.
Proof. intros pre HE HEv HClass.
 destruct({reads}.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 destruct(one_bit_cases pre {valid}%nat)as[HV|HV].
 - pose proof({invalid}.actual_sampled_invalid_word image events ev HE HEv HV)as HW;fold pre in HW.
   exact({s}.actual_bubble_nonstore seed _ HL HW).
 - assert(HValid:norm 1(read_signal pre {valid}%nat)<>0%Z)by congruence.
   pose proof(proj1({h}.boot_and_runtime_related image events HE))as HCov;fold pre in HCov.
   destruct(proj1(proj1(proj1 HCov)))as[HCurrent HW].
   destruct(HCurrent HValid)as[token HT].
   unfold {m}.ClassifiedFamily,ExtendedSVCaptureContent.Related in HClass.
   pose proof(proj2 HClass token HT)as HD;unfold {m}.FamilyToken in HD.
   pose proof({q}.field_{opcode}_current_token image events ev token HE HEv HT)as HOpcode;fold pre in HOpcode.
   destruct HD as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].
   + destruct(CPUISAAddControlFields.original_decode_add_fields _ _ _ _ HD)as[HOP _].
     exact({s}.actual_opcode_51_nonstore seed _ HL(eq_trans HOpcode HOP)).
   + destruct(CPUISAAddiFields.original_decode_addi_fields _ _ _ _ HD)as[HOP _].
     exact({s}.actual_opcode_19_nonstore seed _ HL(eq_trans HOpcode HOP)).
Qed.
Theorem actual_family_quiet_RAM_phase image events ev:
 {common}{r}.StoreQuiet pre ->
 {r}.StoreQuiet {post} /\\read_signal {post}{root}%nat=read_signal pre {root}%nat.
Proof. intros pre HE HEv HClass HQ.
 destruct({reads}.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(actual_family_store_controls_zero image events ev HE HEv HClass)as HC;fold pre in HC.
 exact(conj({r}.actual_quiet_phase ev pre seed HEv HL HQ HC)
  ({r}.actual_quiet_RAM_phase ev pre seed HEv HL HQ)).
Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}{{mem_ok:map.ok Mem}}.
Theorem actual_family_memory_relation_phase image events ev committed:
 {common}{r}.StoreQuiet pre ->
 CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat pre(getDataMem committed) ->
 {r}.StoreQuiet {post} /\\
 CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat {post}(getDataMem committed).
Proof. intros pre HE HEv HClass HQ HM.
 destruct(actual_family_quiet_RAM_phase image events ev HE HEv HClass HQ)as[HQuiet HRAM];fold pre in HQuiet,HRAM.
 split;[exact HQuiet|].
 exact(CPUByteBankRelation.same_bank_and_memory {width} {root}%nat {width//8}%nat pre {post}
  (getDataMem committed)(getDataMem committed)HRAM eq_refl HM).
Qed.
Theorem actual_family_joint_RAM_phase words i initial retired committed image events ev:
 let pre:=phase_run {p} events({f}.boot image)in
 Forall {h}.W.Environment events ->{h}.W.Environment ev ->
 {m}.FamilyMemoryJoint words i initial retired committed pre {packed} ->
 {r}.StoreQuiet {post} /\\
 CPUByteBankRelation.Related {width} {root}%nat {width//8}%nat {post}(getDataMem committed).
Proof. intros pre HE HEv HJ.
 exact(actual_family_memory_relation_phase image events ev committed HE HEv
  ({m}.family_classified words i initial retired committed pre {packed} HJ)
  ({m}.family_quiet words i initial retired committed pre {packed} HJ)
  ({m}.family_memory words i initial retired committed pre {packed} HJ)).
Qed.
End OriginalISA.
Goal True. idtac "FAMILY_RAM_PHASE_AUDIT". exact I. Qed.
'''
    exports=['actual_family_store_controls_zero','actual_family_quiet_RAM_phase','actual_family_memory_relation_phase','actual_family_joint_RAM_phase']
    source+=''.join(f'Print Assumptions {name}.\n'for name in exports)
    return source,exports


def check(c,provider,output):
    provider=Path(provider);receipt=json.loads((provider/'report.json').read_text())
    original=provider/'AddFamilyMemoryJoint.v'
    if not(receipt.get('accepted')and receipt['coqc_exit']==receipt['coqchk_exit']==receipt['target_types_exit']==0
        and memory.digest(original.read_bytes())==receipt['source_sha256']
        and memory.digest(original.with_suffix('.vo').read_bytes())==receipt['object_sha256']):
        raise ValueError('same accepted family memory joint required')
    raw,profile,_=memory.family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    if raw['source_sha256']!=receipt['ast_sha256']:raise ValueError('original RAM-phase AST mismatch')
    plan=json.loads((provider/'plan.json').read_text())
    fields=json.loads((Path(c['current_fields'])/'plan.json').read_text())['rows']
    if not any(row['root']==plan['store_controller']['opcode']and row['field']=='Opcode'and row['width']==7 for row in fields):
        raise ValueError('store opcode must have an accepted original-token field binding')
    paths=json.loads((provider/'providers.json').read_text())+[dict(namespace='GeneratedAddFamilyMemoryJoint',directory=str(provider.resolve()))]
    bindings={row['namespace']:row['directory']for row in paths}
    if bindings.get('GeneratedCurrentControlFields')!=str(Path(c['current_fields']).resolve()):
        raise ValueError('same original controller-field provider required')
    source,exports=render(c,profile,plan)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);file=out/'AddFamilyRAMPhase.v';file.write_text(source)
    for name,data in [('providers',paths),('exports',exports),('plan',plan)]:
        (out/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
    flags=list(memory.family.derived.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedAddFamilyRAMPhase']
    root=memory.family.derived.controls.history.admission.observation.origin.ROOT
    start=time.monotonic()
    baseline=out/'Baseline.v';baseline.write_text((provider/'Baseline.v').read_text())
    bc,_=run_stage([str(root/'_opam/bin/coqc'),*flags,str(baseline.resolve())],out/'baseline.log',1200)
    allowed=parse_assumptions(bc.stdout)
    cc,ct=run_stage([str(root/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',max(.1,1200-(time.monotonic()-start)))
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=ct,baseline_exit=bc.returncode,exports=exports,
        source_sha256=memory.digest(source.encode()),ast_sha256=raw['source_sha256'],old_inv_read=False,
        post_quiet_assumed=False,actual_family_RAM_phase_proved=False,full_cycle_preservation_proved=False,infinite_itree_refinement_proved=False)
    if cc.returncode==0:
        axioms=audit_all_exports(cc.stdout.split('FAMILY_RAM_PHASE_AUDIT')[-1],len(exports))
        audit=bc.returncode==0 and not(axioms-allowed)and not(axioms-ALLOWED_AXIOMS)
        types=source[:source.index('Theorem actual_family_store_controls_zero')]
        types+='Require Import GeneratedAddFamilyRAMPhase.AddFamilyRAMPhase.\nImport GeneratedAddFamilyRAMPhase.AddFamilyRAMPhase.\nSection OriginalISA.\n'
        types+=source.split('Section OriginalISA.\n',1)[1].split('Theorem actual_family_memory_relation_phase',1)[0]
        headers={}
        for name in exports:
            match=re.search(r'Theorem '+name+r' ([A-Za-z0-9_ \n]+):(.*?)\nProof\.',source,re.S)
            if not match:raise ValueError('missing original phase type')
            args,statement=match.groups();headers[name]=memory.digest(match.group(0).removesuffix('\nProof.').encode())
            types+=f'Definition checked_{name} {args}:{statement}\nProof. exact({name} {args}). Qed.\n'
        types+='End OriginalISA.\n'
        typefile=out/'TargetTypes.v';typefile.write_text(types)
        (out/'original-header-sha256.json').write_text(json.dumps(headers,indent=2)+'\n')
        tc,_=run_stage([str(root/'_opam/bin/coqc'),*flags,str(typefile.resolve())],out/'target-types.log',max(.1,1200-(time.monotonic()-start)))
        audit=audit and tc.returncode==0
        kk,kt=run_stage([str(root/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAddFamilyRAMPhase.AddFamilyRAMPhase','-norec','GeneratedAddFamilyRAMPhase.TargetTypes'],out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(accepted=audit and kk.returncode==0,coqchk_exit=kk.returncode,coqchk_timed_out=kt,target_types_exit=tc.returncode,
            assumptions=sorted(axioms),baseline_assumptions=sorted(allowed),assumptions_audit_passed=audit,actual_family_RAM_phase_proved=audit and kk.returncode==0)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=memory.digest(file.with_suffix('.vo').read_bytes())
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--memory-joint',required=True);p.add_argument('--output',required=True)
    a=p.parse_args();r=check(memory.family.inputs(),a.memory_joint,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
