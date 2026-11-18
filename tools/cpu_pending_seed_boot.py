"""Generate boot shape/stability from raw environment DATA, not old INV.

A closed seed/event/phase fragment is frozen, compared to the actual named
definitions, and composed with a freshly checked original-program catalog.
Reset queue/ISA correspondence and progress are not claimed here.
"""
import argparse,hashlib,json,re,time,os,sys
from pathlib import Path
import cpu_environment_data as env
import cpu_pending_constrained_history as history
import cpu_pending_configured_input as config
from cpu_certificate_acceptance import run_stage
ROOT=history.ROOT


def binding_imports(source):
    imports=re.search(r'^Require Import\s+([^\n]+)\.(?:\n|$)',source,re.M)
    if imports is None or not all(re.fullmatch(env.SYMBOL,name)for name in imports[1].split()):
        raise ValueError('closed data-binding imports required')
    return imports[1].split()


def environment(seed_file,seed_module,seed_name,event_file,event_module,boot_file,boot_module,boot_name,program):
    inputs=[(seed_file,seed_module),(event_file,event_module),(boot_file,boot_module)]
    if not all(re.fullmatch(env.SYMBOL,module)for _,module in inputs):raise ValueError('closed environment module names required')
    texts=[Path(path).read_text()for path,_ in inputs];modules=[env.module_name(text)for text in texts]
    seed=env.seed_data(texts[0],seed_name);boot=env.boot_data(texts[2],boot_name,seed_name,program)
    events={name:env.event_data(texts[1],name)for name in dict.fromkeys(boot['events'])}
    function=seed['image_function'];encoders=[]
    for (_,outer),text,inner in zip(inputs,texts,modules):
        if re.search(r'^(?:Fixpoint|Definition)\s+'+re.escape(function)+r'\b',text,re.M):encoders.append(outer+'.'+inner+'.'+function)
    if len(set(encoders))!=1:raise ValueError('one named image function in supplied DATA modules required')
    return dict(seed=seed,boot=boot,events=events,encoder=encoders[0],
        actual_seed=seed_module+'.'+modules[0]+'.'+seed_name,
        actual_boot=boot_module+'.'+modules[2]+'.'+boot_name,
        actual_events={name:event_module+'.'+modules[1]+'.'+name for name in events},
        imports=list(dict.fromkeys(module for _,module in inputs)),
        input_hashes={str(Path(path).resolve()):hashlib.sha256(text.encode()).hexdigest()for(path,_),text in zip(inputs,texts)})


def frozen_source(program,ast_module,data):
    seed=data['seed'];lines=['From Coq Require Import ZArith List.',f'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVBootstrap {ast_module}.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory.',
        f'Definition seed_count:nat:={seed["length"]}.',
        'Definition writes(image:Z):list(nat*Z):=['+';'.join('('+str(w['root'])+'%nat,'+
            ('image'if w['value']['kind']=='image'else str(w['value']['value'])+'%Z')+')'for w in seed['writes'])+'].',
        'Definition seed(image:Z):State:=ExtendedSVBootstrap.seed_writes(repeat 0%Z seed_count)(writes image).']
    for name,event in data['events'].items():lines.append(f'Definition {name}:Event:={{|changed_signal:={event["changed_signal"]}%nat;old_value:={event["old_value"]}%Z;new_value:={event["new_value"]}%Z|}}.')
    lines+=['Definition boot_events:list Event:=['+';'.join(data['boot']['events'])+'].',
        f'Definition boot(image:Z):State:=phase_run {program} boot_events(seed image).']
    return '\n'.join(lines)+'\n'


def binding_source(data):
    lines=['From Coq Require Import ZArith List.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory GeneratedSeedBoot.FrozenEnvironment GeneratedRuntimeInput.ConfigBinding '+
        ' '.join(data['imports'])+'.',
        'Import ExtendedSV ExtendedSVScalarHistory.',
        'Module F:=GeneratedSeedBoot.FrozenEnvironment. Module P:=GeneratedRuntimeInput.ConfigBinding.',
        'Local Opaque PhaseSemantics write_signal.',
        f'Theorem actual_seed_data words:F.seed({data["encoder"]} words)={data["actual_seed"]} words.',
        'Proof. reflexivity. Qed.']
    exports=['actual_seed_data']
    for i,(name,original)in enumerate(data['actual_events'].items()):
        lines += [f'Theorem actual_event_{i}:F.{name}={original}.','Proof. reflexivity. Qed.'];exports.append('actual_event_'+str(i))
    lines += [f'Theorem actual_boot_data words:F.boot({data["encoder"]} words)={data["actual_boot"]} words.',
        'Proof. unfold F.boot;',
        f' refine(eq_trans(f_equal(fun program=>phase_run program F.boot_events(F.seed({data["encoder"]} words)))P.configured_eq_original_target)_).',
        ' reflexivity. Qed.'];exports.append('actual_boot_data')
    lines+=['Print Assumptions '+name+'.'for name in exports]
    return '\n'.join(lines)+'\n',len(exports)


def proof_source(program,ast_module,data):
    roots=sorted({w['root']for w in data['seed']['writes']}|{e['changed_signal']for e in data['events'].values()})
    lines=['From Coq Require Import ZArith List Bool.',f'Require Import {ast_module} Lang.ExtendedSV Lang.ExtendedSVScalarHistory',
        ' Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVBootstrap',
        ' GeneratedDependencyCatalog.Catalog GeneratedBoundedPhase.Phase GeneratedSeedBoot.FrozenEnvironment.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.',
        'Module F:=GeneratedSeedBoot.FrozenEnvironment. Module B:=ExtendedSVBootstrap. Module Phase:=GeneratedBoundedPhase.Phase.',
        'Definition outputs:=Eval vm_compute in catalog_outputs Catalog.actual_catalog.',
        'Lemma outputs_correct:catalog_outputs Catalog.actual_catalog=outputs.',
        'Proof. vm_compute;reflexivity. Qed.',
        f'Lemma seed_count_checked:F.seed_count=signal_count {program}.','Proof. reflexivity. Qed.']
    for root in roots:lines += [f'Lemma root_{root}_safe:B.input_rootb {program} Catalog.actual_catalog {root}=true.',
        'Proof. unfold B.input_rootb;rewrite outputs_correct;vm_compute;reflexivity. Qed.']
    lines += [f'Local Opaque {program}.',
        f'Theorem seed_shape image:CatalogShape {program} Catalog.actual_catalog(F.seed image).',
        'Proof. unfold F.seed;rewrite seed_count_checked;apply B.checked_seed_shape;unfold F.writes.']
    for row in data['seed']['writes']:lines+=[' constructor;[exact root_'+str(row['root'])+'_safe|].']
    lines+=[' constructor. Qed.',f'Theorem boot_events_allowed:Forall(CatalogEvent {program} Catalog.actual_catalog)F.boot_events.',
        'Proof. unfold F.boot_events.']
    for name in data['boot']['events']:
        e=data['events'][name];lines+=[f' constructor;[exact(B.checked_input_root {program} Catalog.actual_catalog {e["changed_signal"]} {e["old_value"]}%Z {e["new_value"]}%Z root_{e["changed_signal"]}_safe)|].']
    lines+=[' constructor. Qed.',
        f'Theorem boot_runtime image:CatalogShape {program} Catalog.actual_catalog(F.boot image) /\\',
        f' exists seed,CombLFP {program} seed(F.boot image).',
        f'Proof. exact(B.checked_boot_runtime {program} Catalog.actual_catalog Phase.actual_certificate F.boot_events(F.seed image)',
        ' ltac:(discriminate)boot_events_allowed(seed_shape image)). Qed.',
        'Print Assumptions seed_shape.','Print Assumptions boot_events_allowed.','Print Assumptions boot_runtime.']
    return '\n'.join(lines)+'\n'


def actual_source(data):
    program=data['actual_program'];original=data['original_program'];environment=data['environment']
    boot=environment['actual_boot'];encoder=environment['encoder']
    state=f'({boot} words)';image=f'({encoder} words)'
    lines=['From Coq Require Import ZArith.',
        'Require Import '+' '.join([data['actual_ast_module'],*data['configuration_imports'],*environment['imports']])+'.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVBoundedCatalogPhase',
        ' GeneratedRuntimeInput.ConfigBinding GeneratedDependencyCatalog.Catalog GeneratedSeedBoot.FrozenEnvironment',
        ' GeneratedSeedBoot.EnvironmentBinding GeneratedSeedBoot.Bootstrap.',
        'Import ExtendedSV ExtendedSVScalarHistory ExtendedSVBoundedCatalogPhase.',
        'Module F:=GeneratedSeedBoot.FrozenEnvironment. Module E:=GeneratedSeedBoot.EnvironmentBinding.',
        'Module B:=GeneratedSeedBoot.Bootstrap. Module P:=GeneratedRuntimeInput.ConfigBinding.',
        f'Local Opaque PhaseSemantics write_signal {program} {original} {boot}.',
        f'Theorem actual_boot_runtime words:CatalogShape {program} Catalog.actual_catalog{state} /\\',
        f' exists seed,CombLFP {program} seed{state}.',
        f'Proof. exact(eq_ind(F.boot{image})(fun state=>CatalogShape {program} Catalog.actual_catalog state /\\',
        f' exists seed,CombLFP {program} seed state)(B.boot_runtime{image}){state}(E.actual_boot_data words)). Qed.',
        f'Theorem original_program_boot_runtime words:CatalogShape {original} Catalog.actual_catalog{state} /\\',
        f' exists seed,CombLFP {original} seed{state}.',
        f'Proof. exact(eq_ind {program}(fun program=>CatalogShape program Catalog.actual_catalog{state} /\\',
        f' exists seed,CombLFP program seed{state})(actual_boot_runtime words){original} P.configured_eq_original_target). Qed.',
        'Print Assumptions actual_boot_runtime.','Print Assumptions original_program_boot_runtime.']
    return '\n'.join(lines)+'\n'


def proposal(ast_path,ast_module,configuration_provider,catalog_provider,phase_provider,runtime_provider,**environment_args):
    ast,profile,paths=history.origin.raw_binding(ast_path,ast_module);profile['coq_load_paths']=paths
    configuration_provider=Path(configuration_provider);cp=json.loads((configuration_provider/'plan.json').read_text())
    cr=json.loads((configuration_provider/'report.json').read_text())
    if not re.fullmatch(env.SYMBOL,cp.get('target_program','')):raise ValueError('closed original Program symbol required')
    if not(cr.get('accepted')is True and cr.get('configuration_binding_proved')is True
        and cp.get('configured_program')==profile['ast']['program']and cp.get('configured_source_sha256')==ast['source_sha256']
        and cp.get('old_inv_read')is False and cp.get('old_cpu_theorems_used_as_premises')is False):
        raise ValueError('actual checked data-only configuration binding required')
    binding=configuration_provider/'ConfigBinding.v'
    if cr.get('binding_source_sha256')!=hashlib.sha256(binding.read_bytes()).hexdigest()or cr['ConfigBinding'].get('object_sha256')!=hashlib.sha256(binding.with_suffix('.vo').read_bytes()).hexdigest():
        raise ValueError('configuration binding fingerprint changed')
    # The generated data-binding header contains qualified module names; match
    # its terminating period, not a period inside one qualified name.
    data=dict(actual_program=profile['ast']['program'],original_program=cp['target_program'],actual_ast_module=ast_module,
        configuration_imports=binding_imports(binding.read_text()),ast_sha256=ast['source_sha256'],coq_load_paths=paths)
    phase_hashes=history.verify_phase(profile,data,catalog_provider,phase_provider)
    provider=Path(runtime_provider);rr=json.loads((provider/'report.json').read_text());rp=json.loads((provider/'plan.json').read_text())
    history.native_accepted(rr)
    expected=history.emit(data['actual_program'],ast_module,rp['reset_root'])
    if not(rp.get('actual_program')==data['actual_program']and rp.get('ast_sha256')==data['ast_sha256']
        and all(rp.get(k)==v for k,v in phase_hashes.items())and rr.get('old_inv_read')is False
        and rr.get('provider_coqchk_exit')==0 and(provider/'ConstrainedHistory.v').read_text()==expected
        and rr.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
        and rr.get('object_sha256')==hashlib.sha256((provider/'ConstrainedHistory.vo').read_bytes()).hexdigest()):
        raise ValueError('fresh exact-object phase recheck evidence required; not old boot/INV evidence')
    envdata=environment(program=cp['target_program'],**environment_args)
    data.update(environment=envdata,phase_hashes=phase_hashes,configuration_load_paths=cp['coq_load_paths'],
        old_inv_read=False,old_pending_read=False,old_cpu_theorems_used_as_premises=False,
        environment_proof_text_consumed=False,legacy_modules_imported_only_for_data_comparison=True,
        original_seed_changed=False,original_boot_changed=False,startup_pending_inv_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    source=frozen_source(data['actual_program'],ast_module,envdata);binding,count=binding_source(envdata)
    return data,source,binding,count,proof_source(data['actual_program'],ast_module,envdata),actual_source(data)


def check(ast_path,ast_module,configuration_provider,catalog_provider,phase_provider,runtime_provider,output,timeout=1200,isolate_core=False,**environment_args):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    if type(isolate_core)is not bool:raise ValueError('typed isolation mode required')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,frozen,binding,count,proof,actual=proposal(ast_path,ast_module,configuration_provider,catalog_provider,phase_provider,runtime_provider,**environment_args)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    stages=[('FrozenEnvironment',frozen,0),('EnvironmentBinding',binding,count),('Bootstrap',proof,3),('ActualBootstrap',actual,2)]
    if isolate_core:stages=[('FrozenEnvironment',frozen,0),('Bootstrap',proof,3)]
    flags=list(history.age.rtl.framework.FLAGS)
    for item in data['coq_load_paths']+([]if isolate_core else data['configuration_load_paths']):flags+=['-R',item['directory'],item['namespace']]
    provider_paths=[(catalog_provider,'GeneratedDependencyCatalog'),(phase_provider,'GeneratedBoundedPhase'),(output,'GeneratedSeedBoot')]
    if not isolate_core:provider_paths.append((configuration_provider,'GeneratedRuntimeInput'))
    for folder,namespace in provider_paths:
        flags+=['-R',str(Path(folder).resolve()),namespace]
    for name,text,_ in stages:(output/(name+'.v')).write_text(text)
    start=time.monotonic();deadline=start+timeout
    report=dict(accepted=False,native_started=True,scope='original environment seed/boot DATA equality and real boot shape/LFP only; not reset pending/ISA invariant',
        execution_environment=dict(conda_environment=os.environ.get('CONDA_DEFAULT_ENV'),python=sys.executable),
        old_inv_read=False,old_cpu_theorems_used_as_premises=False,environment_proof_text_consumed=False,
        legacy_modules_imported_only_for_data_comparison=not isolate_core,core_dependency_isolation_mode=isolate_core,
        legacy_cpu_load_paths_excluded=isolate_core,
        original_seed_changed=False,original_boot_changed=False,
        phase_object_recheck_reused_by_exact_fingerprint=True,startup_pending_inv_proved=False,
        original_seed_and_boot_data_equal_proved=False,seed_shape_and_boot_lfp_proved=False,actual_original_boot_lfp_proved=False,
        global_inv_proved=False,itree_refinement_proved=False,stages={})
    if isolate_core:report['scope']='isolated pure-data boot shape/LFP certificate only; original-target data comparison not run in this extra check'
    for name,text,count in stages:
        if time.monotonic()>=deadline:break
        path=output/(name+'.v');attempts=[];repairs=[]
        while True:
            label=name+(''if not attempts else'.retry'+str(len(attempts)))
            c,t=run_stage([str(ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/(label+'.coqc.log'),deadline-time.monotonic())
            attempts.append(dict(log=label+'.coqc.log',exit=c.returncode,timed_out=t))
            fix=config.missing_ast_path(c.stdout+'\n'+c.stderr)if c.returncode and not t else None
            if fix is None or fix in repairs or time.monotonic()>=deadline:break
            repairs.append(fix);flags+=['-R',fix['directory'],fix['namespace']]
        item=dict(coqc_exit=c.returncode,coqc_timed_out=t,attempts=attempts,data_load_path_repairs=repairs,
            source_sha256=hashlib.sha256(text.encode()).hexdigest());report['stages'][name]=item
        if c.returncode:break
        closed=count==0 or(c.stdout.count('Closed under the global context')==count and'Axioms:'not in c.stdout)
        item['assumptions_closed']=closed
        if not closed or time.monotonic()>=deadline:break
        k,t=run_stage([str(ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedSeedBoot.'+name],output/(name+'.coqchk.log'),deadline-time.monotonic())
        item.update(coqchk_exit=k.returncode,coqchk_timed_out=t)
        if k.returncode:break
        item['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
        if name=='EnvironmentBinding':report['original_seed_and_boot_data_equal_proved']=True
        if name=='Bootstrap':
            report['seed_shape_and_boot_lfp_proved']=True
            if isolate_core:report['accepted']=True
        if name=='ActualBootstrap':report.update(accepted=True,actual_original_boot_lfp_proved=True)
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in['ast','configuration-provider','catalog-provider','phase-provider','runtime-provider','output','seed-file','event-file','boot-file']:p.add_argument('--'+name,type=Path,required=True)
    for name in['ast-module','seed-module','seed-name','event-module','boot-module','boot-name']:p.add_argument('--'+name,required=True)
    p.add_argument('--isolate-core',action='store_true',help='additional dependency-isolation test; not a replacement for original-target data comparison')
    a=vars(p.parse_args());a['ast_path']=a.pop('ast');report=check(**a);print(json.dumps(report,indent=2));raise SystemExit(0 if report['accepted']else 1)
