"""Instantiate the original-budget full phase under explicit catalog shape.

No new CPU invariant is claimed. Before replacing an existing consumer its
original shape/event predicates must be proved to imply these generated ones.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_dependency_catalog as catalogs
import cpu_known_producers as known
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def phase_source(profile,share_static_catalog=False,catalog_module='GeneratedDependencyCatalog.Catalog',fast_converge=False):
    if type(share_static_catalog)is not bool:raise ValueError('catalog sharing mode must be boolean')
    if not isinstance(catalog_module,str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*',catalog_module):
        raise ValueError('catalog module must be a qualified Coq identifier')
    known.completion_source(profile)
    b=profile['ast'];p=b['program'];imports=[b['module'],*b.get('program_imports',[])]
    lines=['From Coq Require Import List Bool.',
      'Require Import Lang.ExtendedSV Lang.ExtendedSVBoundedCatalogPhase',
      ' Lang.ExtendedSVDependencyCatalog '+catalog_module+' '+' '.join(imports)+'.',
      'Import ExtendedSV ExtendedSVBoundedCatalogPhase ExtendedSVDependencyCatalog.']
    if fast_converge:
        lines[1]+=' Lang.ExtendedSVFastConvergence';lines.append('Import ExtendedSVFastConvergence.')
    if catalog_module!='GeneratedDependencyCatalog.Catalog':
        lines += ['Module Catalog := '+catalog_module+'.']
    extra=[]
    if share_static_catalog:
        lines += ['Definition cached_catalog := Eval vm_compute in Catalog.actual_catalog.',
          'Lemma cached_catalog_correct : Catalog.actual_catalog=cached_catalog.',
          'Proof. vm_compute. reflexivity. Qed.',
          'Definition cached_outputs := Eval vm_compute in catalog_outputs cached_catalog.',
          'Lemma cached_outputs_correct : catalog_outputs cached_catalog=cached_outputs.',
          'Proof. vm_compute. reflexivity. Qed.',
          f'Lemma cached_catalog_bounded_checks : bounded_catalog_checksb {p} cached_catalog=true.',
          'Proof. unfold bounded_catalog_checksb,catalog_convergesb,catalog_word_checksb,catalog_covers_writersb.',
          ' rewrite cached_outputs_correct. vm_compute. reflexivity. Qed.']
        extra=['cached_catalog_correct','cached_outputs_correct','cached_catalog_bounded_checks']
    lines += [f'Lemma actual_bounded_checks : bounded_catalog_checksb {p} Catalog.actual_catalog=true.',
      (f'Proof. exact(eq_trans(f_equal(bounded_catalog_checksb {p})cached_catalog_correct)cached_catalog_bounded_checks). Qed.'
       if share_static_catalog else ('Proof. assert(HC:catalog_convergesb '+p+' Catalog.actual_catalog=true) by (apply(fast2_convergesb_sound '+p+' Catalog.actual_catalog); vm_compute; reflexivity).'
        ' assert(HV:catalog_covers_writersb '+p+' Catalog.actual_catalog=true) by (apply(covers_fast_sound '+p+' Catalog.actual_catalog); vm_compute; reflexivity).'
        ' unfold bounded_catalog_checksb. rewrite HC,HV. vm_compute. reflexivity. Qed.' if fast_converge else 'Proof. vm_compute. reflexivity. Qed.')),
      f'Definition actual_certificate : BoundedCatalogCertificate {p} Catalog.actual_catalog :=',
      f' checked_bounded_catalog {p} Catalog.actual_catalog Catalog.actual_order Catalog.actual_catalog_sound actual_bounded_checks.',
      f'Local Opaque {p} Catalog.actual_catalog actual_certificate.',
      'Theorem original_candidate_lfp s :',
      f' CatalogShape {p} Catalog.actual_catalog s ->CombLFP {p} s(lfp_candidate {p} s).',
      f'Proof. exact(original_catalog_candidate_lfp {p} Catalog.actual_catalog actual_certificate s). Qed.',
      'Theorem original_phase ev pre :',
      f' CatalogEvent {p} Catalog.actual_catalog ev->CatalogShape {p} Catalog.actual_catalog pre->',
      f' let driven:=phase_driven_state {p} ev pre in',
      f' CombLFP {p}(write_signal pre(changed_signal ev)(new_value ev))driven /\\',
      f' CombLFP {p}(execute_process_order {p} driven(selected_on_transition {p} pre driven))',
      f' (PhaseSemantics {p} ev pre) /\\ PhaseIndependentAt {p} ev pre.',
      f'Proof. exact(original_catalog_phase {p} Catalog.actual_catalog actual_certificate ev pre). Qed.',
      'Theorem original_phase_shape ev pre :',
      f' CatalogEvent {p} Catalog.actual_catalog ev->CatalogShape {p} Catalog.actual_catalog pre->',
      f' CatalogShape {p} Catalog.actual_catalog(PhaseSemantics {p} ev pre).',
      f'Proof. exact(original_catalog_phase_shape {p} Catalog.actual_catalog actual_certificate ev pre). Qed.']
    for i,name in enumerate((*extra,'actual_certificate','original_candidate_lfp','original_phase','original_phase_shape')):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.',
            'Print Assumptions '+name+'.']
    return '\n'.join(lines)+'\n'


def check(profile,provider,output,timeout=1200,share_static_catalog=False):
    provider=Path(provider).resolve();output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    previous=json.loads((provider/'report.json').read_text())
    if not (previous.get('accepted') and previous.get('metadata',{}).get('converges')
            and previous.get('metadata',{}).get('covers_writers')):
        raise ValueError('checked original-order catalog with convergence and writer coverage required')
    ast,_,_,original=catalogs.proposal(profile,previous.get('cache_rows',False),previous.get('shard_size',0),previous.get('whole_node_cap',0),previous.get('fast_converge',False))
    if (original!=(provider/'Catalog.v').read_text() or ast['source_sha256']!=previous['ast_sha256']
        or previous['source_sha256']!=hashlib.sha256(original.encode()).hexdigest()
        or previous['actual_program']!=profile['ast']['program']):
        raise ValueError('provider differs from actual profile/source')
    source=phase_source(profile,share_static_catalog,fast_converge=previous.get('fast_converge',False));output.mkdir(parents=True);path=output/'Phase.v';path.write_text(source)
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    flags+=['-R',str(provider),'GeneratedDependencyCatalog','-R',str(output.resolve()),'GeneratedBoundedPhase']
    report=dict(accepted=False,actual_program=profile['ast']['program'],ast_sha256=ast['source_sha256'],
      source_sha256=hashlib.sha256(source.encode()).hexdigest(),provider_source_sha256=previous['source_sha256'],
      original_iteration_budget=previous['metadata']['budget'],original_full_phase_under_catalog_shape_proved=False,
      existing_shape_compatibility_proved=False,actual_consumer_reconnected=False,
      new_global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0,
      share_static_catalog=share_static_catalog)
    start=time.monotonic();deadline=start+timeout
    k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
      'GeneratedDependencyCatalog.Catalog'],output/'provider.coqchk.log',timeout)
    report.update(provider_coqchk_exit=k.returncode,provider_coqchk_timed_out=t)
    remaining=deadline-time.monotonic()
    if k.returncode==0 and remaining>0:
        cs=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',remaining)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-cs)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,7 if share_static_catalog else 4)
            remaining=deadline-time.monotonic()
            if report['assumptions_closed'] and remaining>0:
                ks=time.monotonic()
                k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                  'GeneratedBoundedPhase.Phase'],output/'coqchk.log',remaining)
                report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,
                  accepted=k.returncode==0,original_full_phase_under_catalog_shape_proved=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--provider',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--share-static-catalog',action='store_true')
    a=p.parse_args();result=check(json.loads(a.profile.read_text()),a.provider,a.output,
                                share_static_catalog=a.share_static_catalog)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
