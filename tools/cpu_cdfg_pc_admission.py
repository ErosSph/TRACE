"""Connect PC control/projection certificates to the actual admission phase.

No PC enable, selector, reset or PC-process-match premise is supplied by the
caller. These are derived from the actual EX capture and raw checked history.
The current captured instruction's ADD classification remains explicit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_cdfg_pc_step as pc
import cpu_hazard_capture_connection as hazard
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage


def discover(c, raw, profile, graph):
    plan=pc.discover(c,raw,profile,graph)
    # The existing raw-generated validity gate must belong to the same AST.
    paths=json.loads((Path(c['admission_queue'])/'providers.json').read_text())
    gate=next(x['directory']for x in paths if x['namespace']=='GeneratedValidGate')
    v=hazard.checked(gate,'ValidGate',raw['source_sha256'])
    if v['control']['terminal']!=plan['chains']['enable']['terminal']:
        raise ValueError('PC and actual EX admission have different enables')
    pairs={}
    for name,process in [('pc',plan['process']),('head',v['process'])]:
        proc=next(p for p in raw['processes']if p['name']==process)
        events=re.findall(r'event_edge := (Posedge|Negedge); event_signal := (\d+)',proc['events'])
        if len(events)!=2 or[edge for edge,_ in events]!=['Posedge','Negedge']:
            raise ValueError('unsupported PC/admission event phases')
        for kind,(_,root)in zip(['clock','reset'],events):
            pairs[name+'_'+kind]=pc.alias_chain(raw,int(root),1)
    if any(pairs['pc_'+kind]['terminal']!=pairs['head_'+kind]['terminal']for kind in ['clock','reset']):
        raise ValueError('PC/admission do not share an actual clock/reset source')
    roots={e['root']for chain in pairs.values()for e in chain['edges']}
    _,wires,_=pc.comb.proposal(profile,roots)
    if wires['residuals']:raise ValueError('unresolved PC/admission timing aliases')
    carrier=pc.admission.discover(c,raw,profile,graph)['pair']['carrier']
    plan.update(gate=gate,valid=v['valid'],head_process=v['process'],timing=pairs,timing_roots=sorted(roots),word_root=carrier)
    return plan


def render(c,raw,profile,plan):
    _,wires,prefix=pc.comb.proposal(profile,plan['timing_roots'])
    ports={x['output_root']:i for i,x in enumerate(wires['ports'])}
    p,am=profile['ast']['program'],raw['module'];valid=plan['valid'];root=plan['pc']
    runtime='GeneratedCapturedHistoryBoot.CapturedHistoryBoot'
    derived='GeneratedDerivedSources.DerivedSources'
    catalog='GeneratedDependencyCatalog.Catalog.actual_catalog'
    cert='GeneratedBoundedPhase.Phase.actual_certificate'
    packed=f'({runtime}.boot_history image events)'
    pre=f'(phase_run {p} events({runtime}.F.boot image))'
    sample=f'(phase_driven_state {p} ev pre)';post=f'(PhaseSemantics {p} ev pre)'
    source=f'Require Import {c["ast_module"]}.\nModule Timing.\n'+prefix+'\nEnd Timing.\n'
    source+=f'''From Coq Require Import List ZArith Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBootstrap
 Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVStallFlush Lang.ExtendedSVConstrainedRuntime
 GeneratedPCStep.PCStep GeneratedPCControl.PCControl GeneratedAdmissionQueue.AdmissionQueue
 GeneratedControlCones.ControlCones GeneratedValidGate.ValidGate GeneratedAdmissionWrite.AdmissionWrite.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVCaptureBirth
 ExtendedSVBoundedCatalogPhase ExtendedSVBootstrap ExtendedSVEmptyPipeline ExtendedSVDependencyCatalog.
Local Opaque {p} PhaseSemantics.
'''
    for name,chain in plan['timing'].items():
        term='eq_refl'
        for edge in reversed(chain['edges']):
            term=f'(eq_trans(eq_trans(Timing.port_{ports[edge["root"]]}_lfp seed fixed HL)(norm_idempotent 1(read_signal fixed {edge["parent"]}%nat))){term})'
        source+=f'''Lemma {name}_normalized seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {chain['source']}%nat)=norm 1(read_signal fixed {chain['terminal']}%nat).
Proof. intro HL;exact {term}. Qed.
Lemma {name}_catalog:In(1%nat,{chain['source']}%nat)(catalog_outputs {catalog}).
Proof. vm_compute;tauto. Qed.
'''
    for kind in ['clock','reset']:
        a=plan['timing']['pc_'+kind]['source'];b=plan['timing']['head_'+kind]['source']
        source+=f'''Lemma same_{kind}_raw seed fixed:CombLFP {p} seed fixed ->
 CatalogShape {p} {catalog} fixed ->read_signal fixed {a}%nat=read_signal fixed {b}%nat.
Proof. intros HL[HLength HWords].
 exact(eq_trans(HWords 1%nat {a}%nat pc_{kind}_catalog)
 (eq_trans(pc_{kind}_normalized seed fixed HL)
 (eq_trans(eq_sym(head_{kind}_normalized seed fixed HL))(eq_sym(HWords 1%nat {b}%nat head_{kind}_catalog))))). Qed.
'''
    source+=f'''Local Opaque {catalog} {cert}.
Lemma same_process_match seed0 seed1 pre sampled:
 CombLFP {p} seed0 pre ->CatalogShape {p} {catalog} pre ->
 CombLFP {p} seed1 sampled ->CatalogShape {p} {catalog} sampled ->
 process_matches_states pre sampled {am}.{plan['process']}=
 process_matches_states pre sampled {am}.{plan['head_process']}.
Proof. intros H0 S0 H1 S1.
 change((edge_fires Posedge(read_signal pre {plan['timing']['pc_clock']['source']}%nat)(read_signal sampled {plan['timing']['pc_clock']['source']}%nat)||
 (edge_fires Negedge(read_signal pre {plan['timing']['pc_reset']['source']}%nat)(read_signal sampled {plan['timing']['pc_reset']['source']}%nat)||false))%bool=
 (edge_fires Posedge(read_signal pre {plan['timing']['head_clock']['source']}%nat)(read_signal sampled {plan['timing']['head_clock']['source']}%nat)||
 (edge_fires Negedge(read_signal pre {plan['timing']['head_reset']['source']}%nat)(read_signal sampled {plan['timing']['head_reset']['source']}%nat)||false))%bool).
 rewrite(same_clock_raw seed0 pre H0 S0),(same_clock_raw seed1 sampled H1 S1),
 (same_reset_raw seed0 pre H0 S0),(same_reset_raw seed1 sampled H1 S1);reflexivity. Qed.
Lemma runtime_shape_lfp events:Forall {runtime}.W.Environment events ->forall before,
 CatalogShape {p} {catalog} before /\\(exists seed,CombLFP {p} seed before) ->
 CatalogShape {p} {catalog}(phase_run {p} events before) /\\
 (exists seed,CombLFP {p} seed(phase_run {p} events before)).
Proof. intros HE before HS.
 assert(HA:Forall(CatalogEvent {p} {catalog})events).
 {{ eapply Forall_impl;[|exact HE];intros ev HH;exact(proj1 HH). }}
 exact(ExtendedSVConstrainedRuntime.history_runtime {p}(CatalogShape {p} {catalog})
 (fun ev _=>CatalogEvent {p} {catalog} ev)(catalog_phase_evidence {p} {catalog} {cert})
 events before(catalog_ready {p} {catalog} events HA before)HS). Qed.
Theorem actual_admission_PC_plus_four image events ev:
 let pre:={pre}in
 Forall {runtime}.W.Environment events ->{runtime}.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 process_matches_states pre {sample}{am}.{plan['head_process']}=true ->
 norm 1(read_signal {post}{valid}%nat)<>0%Z ->
 norm 32(read_signal {post}{root}%nat)=norm 32(norm 32(read_signal pre {root}%nat)+4).
Proof. intros pre HE HEv HClass HM HV.
 destruct(runtime_shape_lfp events HE({runtime}.F.boot image)({runtime}.B.boot_runtime image))as[HShape[seed0 HPre]];fold pre in HShape,HPre.
 pose proof(input_shape {p} {catalog} ev pre(proj1 HEv)HShape)as HDShape.
 pose proof(candidate_shape {p} {catalog} {cert} _ HDShape)as HSampleShape.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof({derived}.protect ev {valid}%nat HEv ltac:(simpl;tauto))as HProtect.
 pose proof(GeneratedAdmissionWrite.AdmissionWrite.actual_capture_reset ev pre HProtect HM HV)as HR.
 assert(HReset:norm 1(read_signal {sample}{plan['reset']}%nat)=1%Z).
 {{ exact(eq_trans(pc_reset_normalized seed _ HL)(eq_trans(eq_sym(head_reset_normalized seed _ HL))HR)). }}
 assert(HEnable:norm 1(read_signal {sample}{plan['chains']['enable']['terminal']}%nat)=1%Z).
 {{ destruct(ExtendedSVStallFlush.one_bit_cases {sample}{plan['chains']['enable']['terminal']}%nat)as[HZ|HZ];[|exact HZ].
    exfalso;apply HV;exact(GeneratedValidGate.ValidGate.blocked_actual_capture seed ev pre HL HProtect HM HZ). }}
 pose proof({derived}.admitted_source_valid seed ev pre HEv HL HM HV)as HSource.
 destruct({runtime}.boot_and_runtime_related image events HE)as[[[HI HC]HCov]HW].
 destruct HI as[[HCover HValue]HRest];destruct(HCover HSource)as[token HT].
 destruct(HClass token HT)as[rd[rs1[rs2 HD]]].
 pose proof(GeneratedControlCones.ControlCones.sampled_word_{plan['word_root']} image events ev token HE HEv HT)as HWord;fold pre in HWord.
 pose proof(GeneratedPCControl.PCControl.actual_original_ADD_pcsource seed {sample}(token_word token)rd rs1 rs2 HL HWord HD)as HSelect.
 assert(HMpc:process_matches_states pre {sample}{am}.{plan['process']}=true).
 {{ exact(eq_trans(same_process_match seed0 seed pre {sample} HPre HShape HL HSampleShape)HM). }}
 exact(GeneratedPCStep.PCStep.actual_sequential_pc_phase seed ev pre
 (GeneratedAdmissionQueue.AdmissionQueue.internal_event ev {root}%nat HEv ltac:(lia))HL HMpc HReset HEnable HSelect). Qed.
Goal True. idtac "PC_ADMISSION_AUDIT". exact I. Qed.
Print Assumptions same_clock_raw.
Print Assumptions same_reset_raw.
Print Assumptions same_process_match.
Print Assumptions runtime_shape_lfp.
Print Assumptions actual_admission_PC_plus_four.
'''
    return source


def checked(directory,filename,raw):
    d=Path(directory);r=json.loads((d/'report.json').read_text());file=d/filename
    if not(r.get('accepted')and r['coqc_exit']==r['coqchk_exit']==0 and r.get('assumptions_closed')
        and r['ast_sha256']==raw['source_sha256']and r['source_sha256']==hashlib.sha256(file.read_bytes()).hexdigest()
        and r['object_sha256']==hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()):
        raise ValueError('same-source accepted PC certificate required: '+str(d))
    return json.loads((d/'providers.json').read_text())


def check(c,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    graph=pc.admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,_=pc.admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module'])
    plan=discover(c,raw,profile,graph);source=render(c,raw,profile,plan);file=out/'PCAdmission.v';file.write_text(source)
    paths=checked(c['pc_step'],'PCStep.v',raw)+checked(c['pc_control'],'PCControl.v',raw)
    paths+=checked_provider(c['admission_queue'],'AdmissionQueue.v',raw['source_sha256'],
        ['actual_post_ledger_queue_equation_proved','actual_post_operand_clause_proved'])
    paths += [dict(directory=str(Path(c[k]).resolve()),namespace=ns)for k,ns in
        [('pc_step','GeneratedPCStep'),('pc_control','GeneratedPCControl'),('admission_queue','GeneratedAdmissionQueue')]]
    bindings={}
    for row in paths:
        if row['namespace']in bindings and bindings[row['namespace']]!=row['directory']:
            raise ValueError('different configured provider at '+row['namespace'])
        bindings[row['namespace']]=row['directory']
    paths=[dict(namespace=k,directory=v)for k,v in bindings.items()]
    paths.sort(key=lambda row:len(Path(row['directory']).parts))
    for name,value in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(pc.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedPCAdmission']
    start=time.monotonic();cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(pc.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    r=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),old_inv_read=False,
        actual_ADD_admission_pc_step_proved=False,frontier_relation_restored=False,
        full_R_generated=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('PC_ADMISSION_AUDIT')[-1];closed=audit.count('Closed under the global context')==5 and 'Axioms:'not in cc.stdout
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(pc.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedPCAdmission.PCAdmission'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        ok=closed and kk.returncode==0;r.update(accepted=ok,assumptions_closed=closed,
            coqchk_exit=kk.returncode,coqchk_timed_out=timed,actual_ADD_admission_pc_step_proved=ok)
    r['seconds']=time.monotonic()-start
    if r['accepted']:r['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(r,indent=2)+'\n');return r


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['inputs','output']:parser.add_argument('--'+name,required=True)
    a=parser.parse_args()
    try:r=check(json.loads(Path(a.inputs).read_text()),a.output)
    except Exception as exc:
        out=Path(a.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
