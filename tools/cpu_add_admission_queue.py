"""Connect real rising pending conservation to the newly derived operand R.

Reuse raw-generated physical queue certificates, never a manual CPU invariant.
The real post queue equation is proved, not supplied as a correctness input.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_add_derived_sources as sources
import cpu_pending_rising as normal
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

LIBRARIES=[('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),
 ('value','GeneratedConnectedProjections'),('copies','GeneratedMetadataCopies'),
 ('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),
 ('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),
 ('source-transfer','GeneratedSourceTransfer'),('pipeline-transfer','GeneratedPipelineTransfer'),
 ('retirement-cut','GeneratedRetirementCandidate'),('retirement-phase','GeneratedRetirementPhase'),
 ('clock-frame','GeneratedClockFrame'),('normal-phase','GeneratedRisingQueue')]


def checked_sources(directory,ast_sha):
    folder=Path(directory);report=json.loads((folder/'report.json').read_text())
    plan=json.loads((folder/'plan.json').read_text())
    if not(report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
      and report.get('assumptions_audit_passed')is True and report.get('old_inv_read')is False
      and plan['ast_sha256']==ast_sha and report['ast_sha256']==ast_sha
      and set(report['isa_assumptions'])<=set(report['baseline_assumptions'])<=ALLOWED_AXIOMS
      and hashlib.sha256((folder/'DerivedSources.v').read_bytes()).hexdigest()==report['source_sha256']
      and(folder/'DerivedSources.vo').is_file()):
        raise ValueError('unchanged native-checked original-ISA source provider required')
    return plan


def checked_physical(directory,raw):
    """Reuse unchanged low-level proofs, not their historical INV wrappers.

    Generator metadata may have grown since their acceptance. Pin every actual
    source/object/config and re-infer the same physical path instead of claiming
    that historical generated text is the output of today's generator.
    """
    folder=Path(directory);plan=json.loads((folder/'normal-phase/plan.json').read_text())
    fresh=normal.discover(raw)
    if fresh['rising_paths']!=plan['rising_paths']:
        raise ValueError('physical path/control/phase differs from the current raw AST')
    receipts=[]
    for name,_ in LIBRARIES:
        sub=folder/name;report=json.loads((sub/'report.json').read_text());data=json.loads((sub/'plan.json').read_text())
        files=[f for f in sub.glob('*.v')if hashlib.sha256(f.read_bytes()).hexdigest()==report.get('source_sha256')]
        if not(report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
          and report.get('assumptions_closed')is True and report.get('old_inv_read')is False
          and report.get('old_pending_read')is False and report.get('old_cpu_proofs_used',False)is False
          and not report.get('global_inv_proved')and not report.get('itree_refinement_proved')
          and data.get('ast_sha256')==raw['source_sha256']and len(files)==1
          and files[0].with_suffix('.vo').is_file()
          and hashlib.sha256(files[0].with_suffix('.vo').read_bytes()).hexdigest()==report.get('object_sha256')):
            raise ValueError('unchanged native-checked physical provider required: '+name)
        receipts.append(dict(folder=name,source_sha256=report['source_sha256'],object_sha256=report['object_sha256']))
    return receipts


def render(c,raw,profile,plan):
    p,am=profile['ast']['program'],raw['module']
    birth,head=plan['birth'],plan['head']
    sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
    packed='(D.Runtime.boot_history image events)'
    after=f'(D.Captured.advance_capture_fields ev pre {packed} tt)'
    source=f'''From Coq Require Import List ZArith Bool Lia.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant Lang.ExtendedSVCaptureBirth
 Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVBootstrap
 GeneratedRisingQueue.RisingQueue GeneratedDerivedSources.DerivedSources.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant ExtendedSVCaptureBirth
 ExtendedSVBoundedCatalogPhase ExtendedSVDependencyCatalog ExtendedSVProjectionOrigin ExtendedSVBootstrap.
Module N:=GeneratedRisingQueue.RisingQueue.
Module D:=GeneratedDerivedSources.DerivedSources.
Local Opaque {p} PhaseSemantics.
Definition repack(packed:D.Captured.Packed):N.J.JointGhost:=
 N.J.Build_JointGhost(fst packed)(D.Captured.C.chain_tag0(snd packed))
 (D.Captured.C.chain_tag1(snd packed))(D.Captured.C.chain_tag2(snd packed)).
Lemma repack_step ev pre packed:
 repack(D.Captured.advance_capture_fields ev pre packed tt)=N.J.joint_step ev pre(repack packed).
Proof. destruct packed as[g tags];destruct tags;reflexivity. Qed.
Lemma slot_view pre valid tag:
 GeneratedPhasePendingCommit.PhasePendingCommit.slot pre valid tag=N.Q.slot_tokens pre valid tag.
Proof. unfold GeneratedPhasePendingCommit.PhasePendingCommit.slot,N.Q.slot_tokens;
 destruct tag as[token|];[reflexivity|].
 change((if Z.eqb(norm 1(read_signal pre valid))0%Z then @nil Token else [])=[]).
 destruct(Z.eqb(norm 1(read_signal pre valid))0%Z);reflexivity. Qed.
Lemma view_agreement seed pre packed:
 CatalogShape {p} Catalog.actual_catalog pre ->CombLFP {p} seed pre ->
 GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending pre packed=N.Q.waiting_view pre(repack packed).
Proof. intros HS HL.
 unfold GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending,N.Q.waiting_view.
 rewrite(GeneratedPhasePendingCommit.PhasePendingCommit.stage_0_clock_raw seed pre HS HL).
 unfold GeneratedPhasePendingCommit.PhasePendingCommit.lower_pending,N.Q.lower_view,N.Q.retire_view,repack;
 cbn[N.J.joint_birth N.J.joint_tag_0 N.J.joint_tag_1 N.J.joint_tag_2].
 rewrite !slot_view;reflexivity. Qed.
Lemma external_avoids ev root:D.Runtime.W.Environment ev ->~In root D.Runtime.W.external_roots ->changed_signal ev<>root.
Proof. intros[_ HE]HN HX;unfold D.Runtime.W.ExternalEvent in HE;apply existsb_exists in HE;
 destruct HE as[x[HI HE]];apply Nat.eqb_eq in HE;apply HN;replace root with x by congruence;exact HI. Qed.
Lemma internal_event ev root:D.Runtime.W.Environment ev ->(2<=root)%nat ->changed_signal ev<>root.
Proof. intros HE HN;apply(external_avoids ev root HE);unfold D.Runtime.W.external_roots;
 cbn;intros[HZ|[HO|HF]];[subst;lia|subst;lia|contradiction]. Qed.
Lemma actual_events ev:D.Runtime.W.Environment ev ->N.J.EventAllowed ev /\\N.Q.ClockAllowed ev.
Proof. intro HE;split.
 - apply Forall_forall;intros root HI;unfold N.J.EventAllowed in *.
   cbn in HI;repeat destruct HI as[<-|HI];try contradiction;
   apply(internal_event ev _ HE);lia.
 - intros root HI;unfold N.Q.clock_roots in HI;cbn in HI;
   repeat destruct HI as[<-|HI];try contradiction;
   apply(internal_event ev _ HE);lia. Qed.
Lemma clock_members root:In root N.Q.clock_roots ->In(1%nat,root)(catalog_outputs Catalog.actual_catalog).
Proof. intro HI;unfold N.Q.clock_roots in HI;cbn in HI;
 repeat destruct HI as[<-|HI];try contradiction;vm_compute;tauto. Qed.
Lemma actual_clock_words pre:CatalogShape {p} Catalog.actual_catalog pre ->N.Q.ClockWords pre.
Proof. intros[_ HW]root HI;exact(HW 1%nat root(clock_members root HI)). Qed.
Definition admitted ev pre packed:=N.J.pending_admitted ev pre(repack packed).
Theorem actual_admission_pending_transfer image events ev:
 let pre:=phase_run {p} events(D.Runtime.F.boot image)in
 Forall D.Runtime.W.Environment events ->D.Runtime.W.Environment ev ->
 process_matches_states pre {sample}{am}.{head['process']}=true ->
 norm 1(read_signal {post}{head['valid']})<>0%Z ->
 GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending {post}{after}=
 GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending pre {packed}++admitted ev pre {packed}.
Proof. intros pre HE HEv HM HV.
 destruct(GeneratedPhasePendingCommit.PhasePendingCommit.E.runtime_evidence image events HE)as[HS[seed0 HL0]];
 fold pre in HS,HL0.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 destruct(actual_events ev HEv)as[HJ HA];pose proof(actual_clock_words pre HS)as HW.
 pose proof(GeneratedAdmissionWrite.AdmissionWrite.actual_capture_reset ev pre
 (D.protect ev {head['valid']} HEv ltac:(simpl;tauto))HM HV)as HR.
 assert(HRone:norm 1(read_signal {sample}{birth['event']['reset']})=1%Z).
 {{ exact(eq_trans(N.Q.base_reset_alias seed _ HL)(eq_trans(eq_sym(N.T.target_reset_alias seed _ HL))HR)). }}
 assert(HNormal:norm 1(read_signal {sample}{birth['event']['reset']})<>0%Z)by(congruence).
 assert(HRising:N.Q.Rising ev pre=true).
 {{ rewrite <-(N.Q.source_matches_rising ev pre HA HW HNormal),<-(N.Q.node_1_clocks seed0 seed ev pre HA HW HL0 HL);exact HM. }}
 pose proof(N.rising_waiting_conserved seed0 seed ev pre(repack {packed})HJ HA HW HL0 HL HNormal HRising)as HQ.
 destruct(catalog_phase_evidence {p} Catalog.actual_catalog Phase.actual_certificate ev pre(proj1 HEv)HS)
 as[HLsample[[seed1 HLpost]HSpost]].
 rewrite <-(repack_step ev pre {packed})in HQ.
 rewrite <-(view_agreement seed1 _ _ HSpost HLpost),<-(view_agreement seed0 _ _ HS HL0)in HQ.
 exact HQ. Qed.
Require Import Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth
 coqutil.Map.Interface coqutil.Byte.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.
Theorem actual_admission_restores_operand_clause token_pc initial retired current_state image events ev:
 let pre:=phase_run {p} events(D.Runtime.F.boot image)in
 Forall D.Runtime.W.Environment events ->D.Runtime.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
  Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 D.Current token_pc initial retired current_state pre {packed} ->
 process_matches_states pre {sample}{am}.{head['process']}=true ->
 norm 1(read_signal {post}{head['valid']})<>0%Z ->
 GeneratedOperandResultJoint.OperandResultJoint.OperandClause token_pc initial
 (retired++GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending {post}{after}){post}{after}.
Proof. intros pre HE HEv HClass HCurrent HM HV.
 pose proof(actual_admission_pending_transfer image events ev HE HEv HM HV)as HQ;fold pre in HQ.
 pose proof(D.actual_add_operand_clause_with_new_tokens token_pc initial retired current_state image events ev
 (admitted ev pre {packed})HE HEv HClass HCurrent)as HO;fold pre in HO.
 assert(HLedger:retired++GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending {post}{after}=
 (retired++GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending pre {packed})++admitted ev pre {packed}).
 {{ exact(eq_trans(f_equal(fun tokens=>retired++tokens)HQ)
   (app_assoc retired(GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending pre {packed})(admitted ev pre {packed}))). }}
 exact(eq_rect _ (fun tokens=>GeneratedOperandResultJoint.OperandResultJoint.OperandClause token_pc initial tokens {post}{after})
 HO _ (eq_sym HLedger)).
Qed.
End OriginalISA.
Goal True. idtac "ADMISSION_QUEUE_LOCAL_AUDIT". exact I. Qed.
Print Assumptions repack_step. Print Assumptions slot_view. Print Assumptions view_agreement.
Print Assumptions actual_events. Print Assumptions actual_clock_words. Print Assumptions actual_admission_pending_transfer.
Goal True. idtac "ADMISSION_QUEUE_ISA_AUDIT". exact I. Qed.
Print Assumptions actual_admission_restores_operand_clause.
'''
    return source


def check(c,context,physical,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=sources.controls.history.admission.observation.origin.raw_binding(c['ast'],c['ast_module'])
    plan=checked_sources(c['derived_sources'],raw['source_sha256'])
    receipts=checked_physical(physical,raw)
    paths=json.loads((Path(c['derived_sources'])/'providers.json').read_text())
    if {str(Path(r['directory']).resolve())for r in paths if r['namespace']=='GeneratedPhasePendingCommit'}!={str(Path(context).resolve())}:
        raise ValueError('source and queue consumers must share the same current R provider')
    paths.append(dict(directory=str(Path(c['derived_sources']).resolve()),namespace='GeneratedDerivedSources'))
    paths += [dict(directory=str((Path(physical)/folder).resolve()),namespace=namespace)for folder,namespace in LIBRARIES]
    bindings={}
    for row in paths:
        old=bindings.get(row['namespace'])
        if old is not None and old!=row['directory']:raise ValueError('ambiguous proof provider namespace')
        bindings[row['namespace']]=row['directory']
    paths=[dict(namespace=k,directory=v)for k,v in bindings.items()]
    (out/'physical-provider-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
    sources.controls.history.admission.verify_environment_paths(paths)
    sources.controls.history.admission.checked_graph(c['graph'],c['ast'],out/'replayed')
    text=render(c,raw,profile,plan);file=out/'AdmissionQueue.v';file.write_text(text)
    (out/'providers.json').write_text(json.dumps(paths,indent=2)+'\n')
    (out/'plan.json').write_text(json.dumps(dict(ast_sha256=raw['source_sha256'],physical=str(physical),sources=c['derived_sources']),indent=2)+'\n')
    flags=list(sources.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedAdmissionQueue'];start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(normal.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
        ast_sha256=raw['source_sha256'],old_inv_read=False,complete_R_generated=False,
        actual_post_ledger_queue_equation_proved=False,actual_post_operand_clause_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        local=cc.stdout.split('ADMISSION_QUEUE_LOCAL_AUDIT')[-1].split('ADMISSION_QUEUE_ISA_AUDIT')[0]
        axioms=audit_all_exports(cc.stdout.split('ADMISSION_QUEUE_ISA_AUDIT')[-1],1)
        baseline=set(json.loads((Path(c['derived_sources'])/'report.json').read_text())['baseline_assumptions'])
        closed=local.count('Closed under the global context')==6 and 'Axioms:'not in local
        audit=closed and not(axioms-baseline)and not(axioms-ALLOWED_AXIOMS)
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(normal.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAdmissionQueue.AdmissionQueue'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=audit and kk.returncode==0
        report.update(accepted=ok,coqchk_exit=kk.returncode,coqchk_timed_out=timed,local_assumptions_closed=closed,
            isa_assumptions=sorted(axioms),baseline_assumptions=sorted(baseline),assumptions_audit_passed=audit,
            actual_post_ledger_queue_equation_proved=ok,actual_post_operand_clause_proved=ok)
    report['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['inputs','context','physical','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.context,a.physical,a.output)
    except Exception as e:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(e),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
