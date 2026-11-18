"""Initialize generated write validity from unchanged environment DATA.

Use the checked full-program catalog to derive every sampling LFP. No CPU
initialization/INV theorem is mined, and no initial memory image is computed.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_write_validity_chain as chain
import cpu_pending_seed_boot as boot
from cpu_certificate_acceptance import run_stage

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def checked_file(folder,name,source,stage):
    folder=Path(folder)
    if not(stage.get('coqc_exit')==stage.get('coqchk_exit')==0 and stage.get('assumptions_closed')is True
        and (folder/(name+'.v')).read_text()==source
        and stage.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
        and stage.get('object_sha256')==digest(folder/(name+'.vo'))):
        raise ValueError('changed or unchecked generated provider: '+name)

def seed_zero_supported(seed,root):
    value=0
    for write in seed['writes']:
        if write['root']==root:
            value=write['value'].get('value') if write['value']['kind']=='literal' else None
    return value==0

def render(program,module,data,environment):
    rows=data['rows'];capture=data['entry']['capture'];word,valid=capture['carrier'],capture['valid_root']
    widths={word:32,valid:1}
    for row in rows:widths.update({row['rd']:5,row['write']:1,row['valid']:1})
    zeros=sorted({word}|{r['write']for r in rows})
    seed=environment['seed']
    input_roots=sorted({event['changed_signal']for event in environment['events'].values()})
    if set(input_roots)&set(widths):raise ValueError('declared environment drives an invariant register')
    if not all(seed_zero_supported(seed,r)for r in zeros):
        raise ValueError('initial values do not match zero-write/zero-field rule; need another initialization rule')
    lines=['From Coq Require Import List ZArith Bool.',f'Require Import {module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVBootstrap Lang.ExtendedSVInvariantBootstrap',
        ' Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVEmptyPipeline',
        ' Lang.ExtendedSVInvalidProjection Lang.ExtendedSVWriteValidity Ex.External.CPUInstructionFields',
        ' GeneratedWriteValidity.WriteValidity GeneratedDependencyCatalog.Catalog GeneratedBoundedPhase.Phase',
        ' GeneratedSeedBoot.FrozenEnvironment GeneratedSeedBoot.Bootstrap GeneratedSeedBoot.EnvironmentBinding.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase ExtendedSVInvariantBootstrap.',
        'Module W:=GeneratedWriteValidity.WriteValidity. Module F:=GeneratedSeedBoot.FrozenEnvironment.',
        'Module B:=GeneratedSeedBoot.Bootstrap. Module Phi:=GeneratedBoundedPhase.Phase.',
        f'Local Opaque {program} PhaseSemantics.',
        'Definition external_roots:list nat:=['+';'.join(str(r)+'%nat'for r in input_roots)+'].',
        'Definition ExternalEvent ev:=existsb(Nat.eqb(changed_signal ev))external_roots=true.',
        f'Definition Environment ev:=CatalogEvent {program} Catalog.actual_catalog ev /\\ExternalEvent ev.',
        'Lemma environment_protects_fields ev:',f'Environment ev ->CatalogEvent {program} Catalog.actual_catalog ev /\\ W.Boundary ev.',
        'Proof. intros[HC HE];split;[exact HC|];unfold ExternalEvent in HE.',
        'apply existsb_exists in HE;destruct HE as[root[HI HR]];apply Nat.eqb_eq in HR.',
        'unfold W.Boundary;rewrite HR;unfold external_roots in HI;cbn in HI.',
        'repeat destruct HI as[<-|HI];try contradiction;repeat split;discriminate. Qed.',
        'Lemma boot_environment:Forall Environment F.boot_events.',
        'Proof. unfold F.boot_events.']
    for i,event in enumerate(environment['boot']['events']):
        member='or_introl eq_refl'
        for _ in range(i):member=f'or_intror({member})'
        lines += [f'constructor;[split;[exact(proj1(Forall_forall _ _)B.boot_events_allowed F.{event} ({member}))|unfold ExternalEvent,external_roots;vm_compute;reflexivity]|].']
    lines+=['constructor. Qed.']
    for root in zeros:
        lines += [f'Lemma seed_zero_{root} image:read_signal(F.seed image){root}=0%Z.',
            'Proof. unfold F.seed,F.writes,ExtendedSVBootstrap.seed_writes;cbn[fold_left fst snd].']
        for write in reversed(seed['writes']):
            if write['root']==root:
                lines += ['rewrite read_signal_write_same;reflexivity. Qed.'];break
            lines += ['rewrite read_signal_write_other by discriminate.']
        else:lines += ['apply ExtendedSVEmptyPipeline.read_zero_seed. Qed.']
    lines += ['Theorem seed_write_validity image:W.WriteValidityInvariant(F.seed image).',
        'Proof. split.',
        f'- unfold W.CaptureSafe,ExtendedSVInvalidProjection.Related;rewrite seed_zero_{word};intro H;vm_compute;reflexivity.',
        '- unfold W.PipelineEligible.']
    for i,row in enumerate(rows):
        proof=f'unfold ExtendedSVWriteValidity.Eligible;rewrite seed_zero_{row["write"]};intros H;contradiction H;reflexivity'
        lines += [proof+'.' if i==len(rows)-1 else 'split;['+proof+'|].']
    lines += ['Qed.',
        f'Theorem runtime_write_validity events pre:Forall Environment events ->',
        f'CatalogShape {program} Catalog.actual_catalog pre ->W.WriteValidityInvariant pre ->',
        f'W.WriteValidityInvariant(phase_run {program} events pre).',
        f'Proof. intros HE HS HI;exact(checked_history {program} Catalog.actual_catalog Phi.actual_certificate W.WriteValidityInvariant W.Boundary Environment environment_protects_fields W.actual_write_validity_phase events HE pre HS HI). Qed.',
        'Theorem boot_write_validity image:W.WriteValidityInvariant(F.boot image).',
        'Proof. exact(runtime_write_validity F.boot_events(F.seed image)boot_environment(B.seed_shape image)(seed_write_validity image)). Qed.',
        f'Theorem boot_and_history_write_validity image events:Forall Environment events ->',
        f'W.WriteValidityInvariant(phase_run {program} events(F.boot image)).',
        'Proof. intro HE;exact(runtime_write_validity events(F.boot image)HE(proj1(B.boot_runtime image))(boot_write_validity image)). Qed.',
        f'Theorem original_boot_write_validity words:W.WriteValidityInvariant({environment["actual_boot"]} words).',
        f'Proof. rewrite <-(GeneratedSeedBoot.EnvironmentBinding.actual_boot_data words);exact(boot_write_validity({environment["encoder"]} words)). Qed.',
        'Print Assumptions environment_protects_fields. Print Assumptions seed_write_validity.',
        'Print Assumptions runtime_write_validity. Print Assumptions boot_write_validity.',
        'Print Assumptions boot_and_history_write_validity. Print Assumptions original_boot_write_validity.']
    return '\n'.join(lines)+'\n'

def check(ast_path,module,validity_provider,boot_provider,catalog_provider,phase_provider,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);generation=time.monotonic()
    ast,profile,paths=chain.origin.raw_binding(ast_path,module);profile['coq_load_paths']=paths
    program=profile['ast']['program'];vp=Path(validity_provider);bp=Path(boot_provider)
    vs,data=chain.render(ast_path,module);vr=json.loads((vp/'report.json').read_text())
    if not(vr.get('accepted')is True and vr.get('entry_relation_proved')is True
        and vr.get('coqc_exit')==vr.get('coqchk_exit')==0 and vr.get('assumptions_closed')is True
        and (vp/'WriteValidity.v').read_text()==vs and vr.get('source_sha256')==hashlib.sha256(vs.encode()).hexdigest()
        and (vp/'WriteValidity.vo').is_file()):raise ValueError('write-validity source differs from raw reconstruction')
    bd=json.loads((bp/'plan.json').read_text());br=json.loads((bp/'report.json').read_text());env=bd['environment']
    if not(br.get('accepted')is True and br.get('old_inv_read')is False
        and br.get('original_seed_changed')is False and br.get('original_boot_changed')is False
        and bd['actual_program']==program and bd['ast_sha256']==ast['source_sha256']):
        raise ValueError('boot provider differs from the checked actual configuration')
    for file,sha in env['input_hashes'].items():
        if digest(file)!=sha:raise ValueError('original environment DATA source changed')
    phase_hashes=boot.history.verify_phase(profile,bd,catalog_provider,phase_provider)
    if phase_hashes!=bd['phase_hashes']:raise ValueError('bootstrap refers to different phase objects')
    for name,source in [('FrozenEnvironment',boot.frozen_source(program,module,env)),
        ('Bootstrap',boot.proof_source(program,module,env)),('EnvironmentBinding',boot.binding_source(env)[0])]:
        checked_file(bp,name,source,br['stages'][name])
    source=render(program,module,data,env);file=out/'WriteValidityBoot.v';file.write_text(source)
    flags=list(chain.rtl.framework.FLAGS);bindings=list(paths)+bd['configuration_load_paths']
    for stage in br['stages'].values():bindings.extend(stage.get('data_load_path_repairs',[]))
    for folder,ns in [(vp,'GeneratedWriteValidity'),(bp,'GeneratedSeedBoot'),(Path(catalog_provider),'GeneratedDependencyCatalog'),
        (Path(phase_provider),'GeneratedBoundedPhase'),(out,'GeneratedWriteValidityBoot')]:
        bindings.append(dict(directory=str(folder.resolve()),namespace=ns))
    seen=set()
    for b in bindings:
        key=(b['directory'],b['namespace'])
        if key not in seen:flags+=['-R',*key];seen.add(key)
    (out/'plan.json').write_text(json.dumps(dict(program=program,ast_sha256=ast['source_sha256'],paths=bindings,
        phase_hashes=phase_hashes,seed=env['seed'],boot=env['boot'],original_boot=env['actual_boot']),indent=2)+'\n')
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(chain.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,
        old_inv_read=False,original_environment_changed=False,write_validity_initialization_proved=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),generation_seconds=start-generation)
    if c.returncode==0 and time.monotonic()<deadline:
        closed=c.stdout.count('Closed under the global context')==6 and 'Axioms:'not in c.stdout
        k,t=run_stage([str(chain.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedWriteValidityBoot.WriteValidityBoot'],out/'coqchk.log',deadline-time.monotonic())
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
        result['write_validity_initialization_proved']=result['accepted']
    result['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','validity-provider','boot-provider','catalog-provider','phase-provider','output']:parser.add_argument('--'+key,required=True)
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.validity_provider,a.boot_provider,a.catalog_provider,a.phase_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
