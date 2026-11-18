"""Connect newly synthesized pending to a fresh bounded-catalog phase proof.

Only raw AST and exactly reconstructed local certificates are accepted. The
new environment contract retains event/reset conditions and initial shape;
it does not assume an old invariant or per-step LFP witnesses.
"""
import argparse,hashlib,json,os,sys,time
from pathlib import Path
import cpu_pending_age as age
import cpu_pending_runtime_catalog as runtime
from cpu_certificate_acceptance import run_stage
origin=age.origin;ROOT=origin.ROOT


def native_accepted(report):
    if not(report.get('accepted')is True and report.get('coqc_exit')==0
        and report.get('coqchk_exit')==0 and report.get('assumptions_closed')is True):
        raise ValueError('native compilation, closed assumptions and independent check required')


def verify_phase(profile,data,catalog_provider,phase_provider):
    catalog_provider=Path(catalog_provider);phase_provider=Path(phase_provider)
    catalog_report=json.loads((catalog_provider/'report.json').read_text())
    phase_report=json.loads((phase_provider/'report.json').read_text())
    for report in[catalog_report,phase_report]:
        native_accepted(report)
        if report.get('actual_program')!=data['actual_program']or report.get('ast_sha256')!=data['ast_sha256']:
            raise ValueError('provider differs from actual raw AST/program')
    if not(phase_report.get('original_full_phase_under_catalog_shape_proved')is True
        and phase_report.get('itree_refinement_proved')is False
        and catalog_report.get('metadata',{}).get('converges')is True
        and catalog_report.get('metadata',{}).get('covers_writers')is True):
        raise ValueError('full original-budget bounded phase, not a partial catalog, required')
    cache=catalog_report.get('cache_rows',False);share=phase_report.get('share_static_catalog',False)
    if type(cache)is not bool or type(share)is not bool:raise ValueError('typed generation modes required')
    _,_,catalog_source=runtime.proposal(profile['ast']['file'],profile['ast']['module'],cache)
    phase_source=runtime.phase.phase_source(profile,share)
    for folder,name,source,report in[(catalog_provider,'Catalog.v',catalog_source,catalog_report),
        (phase_provider,'Phase.v',phase_source,phase_report)]:
        if(folder/name).read_text()!=source or report.get('source_sha256')!=hashlib.sha256(source.encode()).hexdigest():
            raise ValueError('provider source was not generated from this raw input: '+name)
    if phase_report.get('provider_source_sha256')!=hashlib.sha256(catalog_source.encode()).hexdigest():
        raise ValueError('phase refers to a different catalog')
    return dict(catalog_source_sha256=hashlib.sha256(catalog_source.encode()).hexdigest(),
        catalog_object_sha256=hashlib.sha256((catalog_provider/'Catalog.vo').read_bytes()).hexdigest(),
        phase_source_sha256=hashlib.sha256(phase_source.encode()).hexdigest(),
        phase_object_sha256=hashlib.sha256((phase_provider/'Phase.vo').read_bytes()).hexdigest())


def emit(program,ast_module,reset):
    if not runtime.origin.pending.rtl.SYMBOL.fullmatch(program)or not runtime.origin.pending.rtl.SYMBOL.fullmatch(ast_module):
        raise ValueError('closed actual program/module symbols required')
    if type(reset)is not int or reset<0:raise ValueError('raw reset root required')
    p=program;sample=f'(phase_driven_state {p} ev pre)'
    lines=['From Coq Require Import List ZArith.',f'Require Import {ast_module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVBoundedCatalogPhase',
        ' Lang.ExtendedSVConstrainedRuntime GeneratedDependencyCatalog.Catalog GeneratedBoundedPhase.Phase GeneratedCaptureAge.CaptureAge.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVBoundedCatalogPhase.',
        'Module Phase:=GeneratedBoundedPhase.Phase. Module Age:=GeneratedCaptureAge.CaptureAge.',
        'Module G:=ExtendedSVConstrainedRuntime. Module Shadow:=ExtendedSVCheckedPhaseReplay.',
        f'Local Opaque {p}.',
        f'Definition Shape:=CatalogShape {p} Catalog.actual_catalog.',
        'Definition Environment ev pre:=',
        f' CatalogEvent {p} Catalog.actual_catalog ev /\\Age.J.EventAllowed ev /\\Age.Q.ClockAllowed ev /\\',
        f' norm 1(read_signal{sample}{reset})<>0%Z.',
        f'Definition EnvironmentReady:=Shadow.Ready {p} Environment.',
        'Theorem actual_runtime_phase ev pre:Environment ev pre->Shape pre->',
        f' CombLFP {p}(write_signal pre(changed_signal ev)(new_value ev)){sample} /\\',
        f' (exists seed,CombLFP {p} seed(PhaseSemantics {p} ev pre)) /\\Shape(PhaseSemantics {p} ev pre).',
        'Proof. intros[HE _]HS;destruct(Phase.original_phase ev pre HE HS)as[HL[HP _]];',
        f' split;[exact HL|]. split;[exists(execute_process_order {p}{sample}(selected_on_transition {p} pre{sample}));exact HP|',
        ' exact(Phase.original_phase_shape ev pre HE HS)]. Qed.',
        'Lemma ready_condition ev pre:G.WithLFP '+p+' Environment ev pre->Age.Allowed ev pre.',
        'Proof. intros[[HC[HJ[HE HR]]][HL0 HL]].',
        ' exact(conj HJ(conj HE(conj HL0(conj(ex_intro _ _ HL)HR)))). Qed.',
        'Theorem pending_ready_from_environment events pre:Shape pre->',
        f' (exists seed,CombLFP {p} seed pre)->EnvironmentReady events pre->Age.Ready events pre.',
        'Proof. intros HS HL HE;',
        f' exact(G.ready_map {p}(G.WithLFP {p} Environment)Age.Allowed ready_condition events pre',
        f' (G.history_ready_with_lfp {p} Shape Environment actual_runtime_phase events pre HE(conj HS HL))). Qed.',
        'Theorem actual_nonempty_history_runtime events pre:events<>[]->EnvironmentReady events pre->Shape pre->',
        f' Shape(phase_run {p} events pre) /\\exists seed,CombLFP {p} seed(phase_run {p} events pre).',
        f'Proof. exact(G.nonempty_history_runtime {p} Shape Environment actual_runtime_phase events pre). Qed.',
        'Theorem pending_history_from_environment events pre g accounts:Shape pre->',
        f' (exists seed,CombLFP {p} seed pre)->EnvironmentReady events pre->Age.OrderedCandidate pre g accounts->',
        ' exists result,Age.replay events pre g accounts=Some result /\\',
        f' Age.result_rtl result=phase_run {p} events pre /\\',
        ' Age.OrderedCandidate(Age.result_rtl result)(Age.result_ghost result)(Age.result_accounts result).',
        'Proof. intros HS HL HE HI;pose proof(pending_ready_from_environment events pre HS HL HE)as HR;',
        ' destruct(Age.replay_restores events pre g accounts HR HI)as[result[HA Hpost]];',
        ' exists result;split;[exact HA|]. split;[exact(Age.replay_erases events pre g accounts result HA)|exact Hpost]. Qed.']
    exports=['actual_runtime_phase','pending_ready_from_environment','actual_nonempty_history_runtime','pending_history_from_environment']
    lines+=['Print Assumptions '+name+'.'for name in exports]
    return '\n'.join(lines)+'\n'


def proposal(ast_path,ast_module,pending_provider,catalog_provider,phase_provider):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);profile['coq_load_paths']=paths
    ad,source=age.render(ast_path,ast_module,pending_provider,Path(pending_provider)/'normal-phase')
    ar=age.fields.verify(Path(pending_provider)/'capture-age','CaptureAge.v',ad,source)
    reset=ad['paths'][0]['frame']['phase']['base']['hold']['reset']
    data=dict(ast_sha256=ast['source_sha256'],actual_program=profile['ast']['program'],coq_load_paths=paths,
        pending_object_sha256=ar['object_sha256'],reset_root=reset,old_inv_read=False,old_pending_read=False,
        old_cpu_proofs_used=False,per_step_lfp_is_external_premise=False,
        initial_shape_and_stability_still_required=True,normal_reset_and_event_conditions_retained=True,
        startup_proved=False,original_runtime_ready_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    data.update(verify_phase(profile,data,catalog_provider,phase_provider))
    return data,emit(data['actual_program'],ast_module,reset)


def check(ast_path,ast_module,pending_provider,catalog_provider,phase_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=proposal(ast_path,ast_module,pending_provider,catalog_provider,phase_provider)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,old_pending_read=False,
            old_cpu_proofs_used=False,original_runtime_ready_proved=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n');path=output/'ConstrainedHistory.v';path.write_text(source)
    flags=list(age.rtl.framework.FLAGS)
    for binding in data['coq_load_paths']:flags+=['-R',binding['directory'],binding['namespace']]
    bindings=[('capture-birth','GeneratedCaptureBirth'),('coverage','GeneratedRecipeCoverage'),('value','GeneratedConnectedProjections'),
        ('copies','GeneratedMetadataCopies'),('joint','GeneratedCoveredFields'),('joint-history','GeneratedJointHistory'),
        ('stall-flush','GeneratedStallFlush'),('source-hold','GeneratedSourceHold'),('source-transfer','GeneratedSourceTransfer'),
        ('pipeline-transfer','GeneratedPipelineTransfer'),('retirement-cut','GeneratedRetirementCandidate'),
        ('retirement-phase','GeneratedRetirementPhase'),('clock-frame','GeneratedClockFrame'),('normal-phase','GeneratedRisingQueue'),
        ('capture-age','GeneratedCaptureAge')]
    for folder,namespace in bindings:flags+=['-R',str((Path(pending_provider)/folder).resolve()),namespace]
    for folder,namespace in[(catalog_provider,'GeneratedDependencyCatalog'),(phase_provider,'GeneratedBoundedPhase'),(output,'GeneratedConstrainedHistory')]:
        flags+=['-R',str(Path(folder).resolve()),namespace]
    start=time.monotonic();deadline=start+timeout
    report=dict(accepted=False,native_started=True,scope='pending capture-age history from explicit initial shape/stability and real environment; no per-step LFP assumption',
        execution_environment=dict(conda_environment=os.environ.get('CONDA_DEFAULT_ENV'),python=sys.executable,
            coqc=str(ROOT/'_opam/bin/coqc'),coqchk=str(ROOT/'_opam/bin/coqchk')),
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        per_step_lfp_is_external_premise=False,initial_shape_and_stability_still_required=True,
        normal_reset_and_event_conditions_retained=True,startup_proved=False,original_runtime_ready_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    # The previous phase checker did not record its object digest. Validate
    # that object here, then pin its bytes in this connection's plan.
    k,t=run_stage([str(ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedBoundedPhase.Phase'],output/'provider.coqchk.log',deadline-time.monotonic())
    report.update(provider_coqchk_exit=k.returncode,provider_coqchk_timed_out=t)
    if k.returncode==0 and time.monotonic()<deadline:
        c,t=run_stage([str(ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
        report.update(coqc_exit=c.returncode,coqc_timed_out=t)
        if c.returncode==0:
            closed=c.stdout.count('Closed under the global context')==4 and'Axioms:'not in c.stdout
            report['assumptions_closed']=closed
            if closed and time.monotonic()<deadline:
                k,t=run_stage([str(ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedConstrainedHistory.ConstrainedHistory'],output/'coqchk.log',deadline-time.monotonic())
                report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','pending-provider','catalog-provider','phase-provider','output']:p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--ast-module',required=True);a=p.parse_args()
    r=check(a.ast,a.ast_module,a.pending_provider,a.catalog_provider,a.phase_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
