"""Generate captured-field histories from the unchanged seed and real phases.

This rule proves capture identity, not ISA retirement order or full R.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_capture_chain_coverage as coverage
import cpu_write_validity_boot as boot
from cpu_certificate_acceptance import run_stage


def render(program, module, data, environment):
    rows = data['rows']
    capture = data['entry']['capture']
    valid = capture['valid_root']
    zeros = sorted({valid} | {r['valid'] for r in rows})
    protected = {capture['carrier'], valid} | {r[k] for r in rows for k in ['rd', 'valid']}
    if any(e['changed_signal'] in protected for e in environment['events'].values()):
        raise ValueError('environment drives a history field')
    if not all(boot.seed_zero_supported(environment['seed'], r) for r in zeros):
        raise ValueError('history seed is not empty; need a nonempty initialization rule')
    lines = ['From Coq Require Import List ZArith Bool.', f'Require Import {module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVCaptureBirth',
        ' Lang.ExtendedSVRuntimeHistory Lang.ExtendedSVDependencyCatalog Lang.ExtendedSVBoundedCatalogPhase Lang.ExtendedSVEmptyPipeline',
        ' GeneratedCoveredCapture.CoveredCapture GeneratedWriteValidityBoot.WriteValidityBoot',
        ' GeneratedSeedBoot.FrozenEnvironment GeneratedSeedBoot.Bootstrap GeneratedBoundedPhase.Phase',
        ' GeneratedDependencyCatalog.Catalog.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVRuntimeHistory ExtendedSVDependencyCatalog ExtendedSVBoundedCatalogPhase.',
        'Module C:=GeneratedCoveredCapture.CoveredCapture. Module W:=GeneratedWriteValidityBoot.WriteValidityBoot.',
        'Module F:=GeneratedSeedBoot.FrozenEnvironment. Module B:=GeneratedSeedBoot.Bootstrap.',
        f'Local Opaque {program} PhaseSemantics.',
        'Definition empty:C.Packed:=(Build_Ghost 0 None [],@C.C.Build_ChainTags Token '+ ' '.join('None' for _ in rows)+').']
    for root in zeros:
        lines += [f'Lemma seed_zero_{root} image:read_signal(F.seed image){root}=0%Z.',
            'Proof. unfold F.seed,F.writes,Lang.ExtendedSVBootstrap.ExtendedSVBootstrap.seed_writes;cbn[fold_left fst snd].']
        for write in reversed(environment['seed']['writes']):
            if write['root'] == root:
                lines += ['rewrite read_signal_write_same;reflexivity. Qed.'];break
            lines += ['rewrite read_signal_write_other by discriminate.']
        else:lines += ['apply ExtendedSVEmptyPipeline.read_zero_seed. Qed.']
    lines += ['Theorem seed_covered image:C.CoveredCapturedFields(F.seed image)empty.',
        'Proof. split;[split|].',
        f'- apply empty_initial_invariant;rewrite seed_zero_{valid};reflexivity.',
        '- unfold C.C.ChainRelated,empty;cbn;repeat split;intros;discriminate.',
        '- unfold C.SlotCoverage;cbn[snd].']
    for root in zeros:
        lines += [f'rewrite seed_zero_{root}.' ] if root != valid else []
    lines += ['repeat split;intros H;contradiction H;reflexivity. Qed.',
        f'Lemma boundary seed ev pre:W.Environment ev ->CombLFP {program} seed(phase_driven_state {program} ev pre) ->C.CoveredBoundary ev pre tt.',
        'Proof. intros HE HL;destruct(W.environment_protects_fields ev HE)as[HC HB].',
        'unfold W.W.Boundary in HB;repeat match type of HB with _ /\\ _ => destruct HB as [? HB] end.',
        'split;[exists seed;repeat split;assumption|repeat split;assumption]. Qed.',
        f'Definition history events pre packed:=replay {program} C.Packed C.advance_capture_fields events pre packed.',
        'Theorem runtime_history events pre packed:Forall W.Environment events ->',
        f'CatalogShape {program} Catalog.actual_catalog pre ->',
        f'C.CoveredExecution pre packed events(phase_run {program} events pre)(history events pre packed).',
        f'Proof. intros HE HS;exact(checked_execution {program} Catalog.actual_catalog Phase.actual_certificate C.Packed C.advance_capture_fields C.CoveredBoundary W.Environment (fun ev H=>proj1 H) boundary events HE pre packed HS). Qed.',
        'Definition boot_history image events:=history(F.boot_events++events)(F.seed image)empty.',
        'Theorem boot_and_runtime_related image events:Forall W.Environment events ->',
        f'C.CoveredCapturedFields(phase_run {program} events(F.boot image))(boot_history image events) /\\',
        f'W.W.WriteValidityInvariant(phase_run {program} events(F.boot image)).',
        'Proof. intro HE;split;[|exact(W.boot_and_history_write_validity image events HE)].',
        'assert(HA:Forall W.Environment(F.boot_events++events))by(apply Forall_app;split;[exact W.boot_environment|exact HE]).',
        f'pose proof(C.covered_capture_history (F.seed image)empty(F.boot_events++events) (phase_run {program}(F.boot_events++events)(F.seed image)) (boot_history image events)',
        ' (runtime_history _ _ _ HA(B.seed_shape image))(seed_covered image))as HR.',
        'rewrite phase_run_append in HR;exact HR. Qed.',
        'Print Assumptions seed_covered. Print Assumptions runtime_history. Print Assumptions boot_and_runtime_related.']
    return '\n'.join(lines)+'\n'


def check(ast, module, coverage_provider, validity_boot_provider, output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    cp=Path(coverage_provider);wp=Path(validity_boot_provider)
    plan=json.loads((wp/'plan.json').read_text());wr=json.loads((wp/'report.json').read_text())
    paths=plan['paths'];by_ns={b['namespace']:Path(b['directory']) for b in paths}
    bp=by_ns['GeneratedSeedBoot'];vp=by_ns['GeneratedWriteValidity']
    env=json.loads((bp/'plan.json').read_text())['environment']
    raw,profile,_=boot.chain.origin.raw_binding(ast,module)
    if raw['source_sha256']!=plan['ast_sha256'] or profile['ast']['program']!=plan['program']:
        raise ValueError('different runtime AST')
    vs,data=boot.chain.render(ast,module)
    vr=json.loads((vp/'report.json').read_text())
    if not(vr.get('accepted') is True and (vp/'WriteValidity.v').read_text()==vs):
        raise ValueError('unchecked or changed validity provider')
    expected=boot.render(plan['program'],module,data,env)
    if not(wr.get('accepted') is True and wr.get('assumptions_closed') is True
        and wr.get('coqc_exit')==wr.get('coqchk_exit')==0 and (wp/'WriteValidityBoot.v').read_text()==expected
        and wr.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()):
        raise ValueError('unchecked or changed bootstrap provider')
    for file,sha in env['input_hashes'].items():
        if boot.digest(file)!=sha:raise ValueError('original environment data changed')
    bd=json.loads((bp/'plan.json').read_text());br=json.loads((bp/'report.json').read_text())
    phase_hashes=boot.boot.history.verify_phase(profile,bd,by_ns['GeneratedDependencyCatalog'],by_ns['GeneratedBoundedPhase'])
    if phase_hashes!=plan['phase_hashes'] or phase_hashes!=bd['phase_hashes']:
        raise ValueError('phase certificate objects changed')
    for name,source in [('FrozenEnvironment',boot.boot.frozen_source(plan['program'],module,env)),
        ('Bootstrap',boot.boot.proof_source(plan['program'],module,env)),
        ('EnvironmentBinding',boot.boot.binding_source(env)[0])]:
        boot.checked_file(bp,name,source,br['stages'][name])
    cr=json.loads((cp/'report.json').read_text())
    cs,cd=coverage.render(ast,module,{r['rd'] for r in data['rows']})
    if not(cr.get('accepted') is True and cr.get('export_assumptions_closed') is True
        and cr.get('coqc_exit')==cr.get('coqchk_exit')==0 and (cp/'CoveredCapture.v').read_text()==cs
        and cr.get('source_sha256')==hashlib.sha256(cs.encode()).hexdigest()):
        raise ValueError('unchecked or changed coverage provider')
    source=render(plan['program'],module,data,env);file=out/'CapturedHistoryBoot.v';file.write_text(source)
    flags=list(boot.chain.rtl.framework.FLAGS);seen=set()
    paths=paths+[dict(directory=str(cp.resolve()),namespace='GeneratedCoveredCapture'),
                 dict(directory=str(out.resolve()),namespace='GeneratedCapturedHistoryBoot')]
    for b in paths:
        key=(b['directory'],b['namespace'])
        if key not in seen:flags+=['-R',*key];seen.add(key)
    (out/'plan.json').write_text(json.dumps(dict(paths=paths,program=plan['program'],ast_sha256=raw['source_sha256']),indent=2)+'\n')
    start=time.monotonic();c,t=run_stage([str(boot.chain.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,
        old_inv_read=False,retirement_order_proved=False,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()-start<1200:
        closed=c.stdout.count('Closed under the global context')==3 and 'Axioms:' not in c.stdout
        k,t=run_stage([str(boot.chain.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCapturedHistoryBoot.CapturedHistoryBoot'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','coverage-provider','validity-boot-provider','output']:parser.add_argument('--'+key,required=True)
    a=parser.parse_args();r=check(a.ast,a.ast_module,a.coverage_provider,a.validity_boot_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
