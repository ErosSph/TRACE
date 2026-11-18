#!/usr/bin/env python3
"""Reproducible four-design adapter generation and checked ITree assembly.

New semantic adapters are compiled from actual imported syntax.  Existing
design-specific global proofs are separately reused through common contract
schemas.  Neither success flag claims discovery of a new global invariant.
"""
from __future__ import annotations
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

import cpu_auto_adapter as adapter
import cpu_auto_roles as roles
import cpu_bank_adapter as bank_adapter
import cpu_bank_reads as bank_reads
import cpu_rf_read_ports as rf_ports
import cpu_rf_process_ports as rf_process_ports
import cpu_rf_view_expression as rf_view_expression
import cpu_scalar_captures as scalar_captures
import cpu_scalar_rhs as scalar_rhs
import cpu_plan_slices as plan_slices
import cpu_scalar_expressions as scalar_expressions
import cpu_scalar_expression_paths as scalar_paths
import cpu_scalar_guard_bindings as guard_bindings
import cpu_guard_partitions as guard_partitions
import cpu_instruction_fields as instruction_fields
import cpu_instruction_word_aliases as instruction_aliases
import cpu_tagged_instruction_fields as instruction_tags
import cpu_contract_synthesis as contract
import cpu_joint_obligations as joint_obligations
import cpu_joint_synthesis as joint_synthesis
import cpu_joint_search as joint_search
import cpu_comb_rule_registry as comb_registry
import cpu_two_stage_producers as two_stage_producers
import cpu_comb_phase_certificate as comb_phase
import cpu_comb_residual_diagnostics as comb_residuals
import cpu_known_producers as known_producers
import cpu_phase_from_known as known_phase
import cpu_known_phase_library as known_phase_library
import cpu_root_free_producers as root_free_producers
import cpu_output_dependency_slices as output_dependency_slices
import cpu_dependency_catalog as dependency_catalog
import cpu_bounded_catalog_phase as bounded_catalog_phase
import cpu_bounded_catalog_library as bounded_catalog_library
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS

SHARED_MODULES = ['Lib/ExplicitEqualityTransport',
    'Lang/ExtendedSVAutoAdapterSemantics','Lang/ExtendedSVAutoAdapterPlan',
    'Lang/ExtendedSVAutoAdapterPhase','Lang/ExtendedSVAutoAdapterEffects',
    'Lang/ExtendedSVBlockingSnapshot',
    'Lang/ExtendedSVInferredCombPartition',
    'Lang/ExtendedSVCombRuleRegistry',
    'Lang/ExtendedSVCombRuleAssembly',
    'Lang/ExtendedSVCombPositiveFuel',
    'Lang/ExtendedSVTwoStageProducer',
    'Ex/External/CPUCombRuleCatalog',
    'Lang/ExtendedSVNBAOutputsFreeProducer',
    'Lang/ExtendedSVNBAOutputsFreeProducerTest',
    'Lang/ExtendedSVKnownCapture',
    'Lang/ExtendedSVKnownCaptureTest',
    'Lang/ExtendedSVKnownProducer',
    'Lang/ExtendedSVKnownProducerTest',
    'Lang/ExtendedSVTransportRuleAssembly',
    'Lang/ExtendedSVArbitraryMaskedReplay',
    'Lang/ExtendedSVArbitraryMaskedReplayTest',
    'Lang/ExtendedSVRootFreeProducer',
    'Lang/ExtendedSVRootFreeProducerTest',
    'Lang/ExtendedSVRootFreeAssembly',
    'Lang/ExtendedSVOutputDependencySlice',
    'Lang/ExtendedSVOutputDependencySliceTest',
    'Lang/ExtendedSVDependencyCatalog',
    'Lang/ExtendedSVDependencyCatalogTest',
    'Lang/ExtendedSVBoundedCatalogPhase',
    'Lang/ExtendedSVBoundedCatalogPhaseTest',
    'Ex/External/CPUCombNBAExtendedCatalog',
    'Lang/ExtendedSVPlanRootSlice','Lang/ExtendedSVPlanEmpty','Lang/ExtendedSVScalarExpression',
    'Lang/ExtendedSVExpressionPath',
    'Lang/ExtendedSVScalarHistory','Lang/ExtendedSVHistoryComposition',
    'Lang/ExtendedSVTokenCoherence',
    'Lang/ExtendedSVRegisterBank','Lang/ExtendedSVBankAlignment','Lang/ExtendedSVBankPlan',
    'Lang/ExtendedSVBankRead',
    'Lang/ExtendedSVCombConfiguration','Lang/ExtendedSVScalarBlockBinding',
    'Lang/ExtendedSVBankReadExpression',
    'Ex/External/CPURegisterEffectRelation',
    'Ex/External/CPURegisterReadRelation',
    'Ex/External/CPURegisterReadExpression',
    'Ex/External/CPUInstructionFields',
    'Ex/External/CPUInstructionFieldAlias',
    'Ex/External/CPUInstructionFieldSnapshot',
    'Ex/External/CPUSampledInstructionFields',
    'Lang/ExtendedSVConstantOutputBinding',
    'Lang/ExtendedSVSlicedProcessBinding',
    'Lang/ExtendedSVIndexedConstantBinding',
    'Lang/ExtendedSVFiniteInvariant',
    'Lang/ExtendedSVFiniteDriver',
    'Lang/ExtendedSVFiniteFrame',
    'Lang/ExtendedSVInstallerFrame',
    'Lang/ExtendedSVInstallerFrameTests',
    'Ex/External/CPUInstructionTaggedFields',
    'Ex/External/CPUISAMemoryAvailability',
    'Ex/External/CPUGeneratedJointTemplate','Ex/External/CPUGeneratedProgress',
    'Ex/External/CPUGeneratedJointITree','Ex/External/CPUGeneratedBoundary']


def flags_for(profile, output):
    flags = list(adapter.framework.FLAGS)
    for binding in profile.get('coq_load_paths', []):
        flags += ['-R', binding['directory'], binding['namespace']]
    return flags + ['-R', str(output.resolve()), 'AutoGenerated']


def audit_contract_output(output):
    """Both generated artifacts must be audited; unknown output is rejection."""
    chunks = re.split(r'^AUTO_CONTRACT_(?:CERTIFICATE|INFINITE)_ASSUMPTIONS\s*$', output,flags=re.M)[1:]
    if len(chunks) != 2:
        return False, []
    axioms = set()
    for chunk in chunks:
        if 'Axioms:' in chunk:
            names = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', chunk, re.M))-{'Axioms'}
            if not names or not names <= ALLOWED_AXIOMS:
                return False, sorted(axioms|names)
            axioms |= names
        elif 'Closed under the global context' not in chunk:
            return False, sorted(axioms)
    return True, sorted(axioms)


def audit_shared_output(source, output):
    """Audit every explicit theorem audit, not only successful compilation."""
    expected = len(re.findall(r'^Print Assumptions\s+', source, re.M))
    chunks = re.split(r'Closed under the global context|Axioms:', output)
    if expected == 0 or len(chunks)-1 != expected:
        return False, []
    axioms = set()
    for match in re.finditer(r'Axioms:(.*?)(?=Axioms:|Closed under the global context|\Z)', output, re.S):
        names = set(re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', match.group(1), re.M))
        if not names or not names <= ALLOWED_AXIOMS:
            return False, sorted(axioms|names)
        axioms |= names
    return True, sorted(axioms)


def assemble_contract(profile, output, timeout):
    joint_binding = profile.get('joint_binding')
    if 'joint_binding' in profile and (not isinstance(joint_binding, dict) or not joint_binding):
        raise ValueError('present joint binding must be a nonempty object; no legacy fallback')
    # Add auditable boundaries to the trusted template's two audit commands.
    selection = joint_binding.get('proof_selection','explicit') if joint_binding else 'legacy'
    allowed = {'explicit','type_search'} if joint_binding else {'legacy'}
    if selection not in allowed:
        raise ValueError('unknown proof selection mode')
    output.mkdir()
    source = ((joint_search.render_search(joint_binding) if selection == 'type_search'
        else joint_synthesis.render(joint_binding)) if joint_binding else contract.render(profile)).replace(
        'Print Assumptions GeneratedContract.assembled.',
        'Goal True. idtac "AUTO_CONTRACT_CERTIFICATE_ASSUMPTIONS". exact I. Qed.\n'
        'Print Assumptions GeneratedContract.assembled.').replace(
        'Print Assumptions GeneratedContract.infinite_refinement.',
        'Goal True. idtac "AUTO_CONTRACT_INFINITE_ASSUMPTIONS". exact I. Qed.\n'
        'Print Assumptions GeneratedContract.infinite_refinement.')
    file = output/'AutoContract.v'; file.write_text(source)
    flags = flags_for(profile, output)
    report = {'accepted': False, 'global_evidence_origin':
        joint_binding['evidence_origin'] if joint_binding else profile['evidence_origin'],
        'new_joint_from_local_components': bool(joint_binding),
        'proof_selection':selection,
        'new_global_invariant_synthesized': False,
        'generated_source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'kernel_scope': 'own generated module with previously compiled dependencies'}
    if joint_binding:
        report['component_compilations'] = []
        for index, relative in enumerate(joint_binding.get('coq_sources', [])):
            component = (adapter.ROOT/relative).resolve()
            if not component.is_relative_to(adapter.ROOT/'src') or component.suffix != '.v':
                raise ValueError('local component source must be a versioned project Coq source')
            checked, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q',
                *flags, str(component)], output/f'component-{index}.coqc.log', timeout)
            report['component_compilations'].append({'source':relative,
                'sha256':hashlib.sha256(component.read_bytes()).hexdigest(),
                'coqc_exit':checked.returncode,'timed_out':timed})
            if checked.returncode != 0:
                report['status'] = 'local_component_compilation_failed'
                (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
                return report
    started = time.monotonic()
    result, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q', *flags,
                               str(file.resolve())], output/'coqc.log', timeout)
    report.update(coqc_exit=result.returncode, coqc_seconds=time.monotonic()-started,
                  coqc_timed_out=timed)
    if result.returncode == 0:
        audited, assumptions = audit_contract_output(result.stdout)
        report.update(assumptions_accepted=audited, assumptions=assumptions)
        started = time.monotonic()
        checked, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
            '-norec', 'AutoGenerated.AutoContract'], output/'coqchk.log', timeout)
        report.update(coqchk_exit=checked.returncode, coqchk_seconds=time.monotonic()-started,
                      coqchk_timed_out=timed)
        report['accepted'] = audited and checked.returncode == 0
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def check_shared(output, timeout):
    output.mkdir()
    results = []
    for module_path in SHARED_MODULES:
        stem=module_path.rsplit('/',1)[-1]
        started = time.monotonic()
        source = adapter.ROOT/'src'/f'{module_path}.v'
        compiled, _ = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q',
            *adapter.framework.FLAGS, str(source)], output/f'{stem}.coqc.log', timeout)
        item = {'module': stem, 'coqc_exit': compiled.returncode,
                'seconds': time.monotonic()-started}
        if compiled.returncode == 0:
            audited, assumptions = audit_shared_output(source.read_text(), compiled.stdout)
            item.update(assumptions_accepted=audited, assumptions=assumptions)
            checked, _ = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'), '-silent',
                *adapter.framework.FLAGS, '-norec', 'Pfv.'+module_path.replace('/','.')],
                output/f'{stem}.coqchk.log', timeout)
            item['coqchk_exit'] = checked.returncode
        results.append(item)
        if item.get('coqchk_exit') != 0 or not item.get('assumptions_accepted', False):
            break
    return results


def check_scalar_expression_components(profile, output, timeout):
    if 'scalar_expression_library' not in profile:
        return None
    roots=profile.get('scalar_expression_roots',profile.get('plan_slice_roots',
        profile.get('scalar_capture_roots')))
    if roots is None:
        raise ValueError('scalar expression library requires declared observation roots')
    component=scalar_expressions.check_profile(profile,output/'scalar-expressions',roots,timeout)
    persistent=dict(accepted=False,status='checked_expression_component_required')
    result=dict(component=component,persistent_library=persistent,accepted=False,
        discharges_token_identity=False)
    if component['accepted']:
        library=(adapter.ROOT/profile['scalar_expression_library']).resolve()
        try:
            relative=library.relative_to(adapter.ROOT/'src')
        except ValueError:
            raise ValueError('persistent expression library must be a project Coq source') from None
        if library.suffix!='.v':
            raise ValueError('persistent expression library must be a project Coq source')
        persistent=scalar_expressions.emit_library(profile,library,roots,check=True)
        flags=flags_for(profile,output)
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
            output/'persistent-scalar-expressions.coqc.log',timeout)
        persistent.update(accepted=False,coqc_exit=c.returncode,timed_out=t)
        if c.returncode==0:
            audited=scalar_captures.audit_output(c.stdout,component['audited_exports'])
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'Pfv.'+'.'.join(relative.with_suffix('').parts)],
                output/'persistent-scalar-expressions.coqchk.log',timeout)
            persistent.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                assumptions_accepted=audited,coq_checked=audited and k.returncode==0,
                accepted=audited and k.returncode==0)
        result.update(persistent_library=persistent,accepted=persistent['accepted'])
    (output/'persistent-scalar-expressions.json').write_text(json.dumps(persistent,indent=2)+'\n')
    return result


def check_scalar_path_components(profile, output, timeout):
    if 'scalar_path_library' not in profile:
        return None
    roots=profile.get('scalar_path_roots',profile.get('scalar_expression_roots',
        profile.get('plan_slice_roots',profile.get('scalar_capture_roots'))))
    if roots is None:raise ValueError('scalar path library requires observation roots')
    component=scalar_paths.check_profile(profile,output/'scalar-paths',roots,timeout)
    persistent=dict(accepted=False,status='checked_path_component_required')
    result=dict(component=component,persistent_library=persistent,accepted=False,
        discharges_reachable_guards=False,discharges_token_identity=False)
    if component['accepted']:
        library=(adapter.ROOT/profile['scalar_path_library']).resolve()
        try:relative=library.relative_to(adapter.ROOT/'src')
        except ValueError:
            raise ValueError('persistent scalar path library must be a project Coq source') from None
        if library.suffix!='.v':
            raise ValueError('persistent scalar path library must be a project Coq source')
        persistent=scalar_paths.emit_library(profile,library,roots,check=True)
        flags=flags_for(profile,output)
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
            output/'persistent-scalar-paths.coqc.log',timeout)
        persistent.update(accepted=False,coqc_exit=c.returncode,timed_out=t)
        if c.returncode==0:
            audited=scalar_captures.audit_output(c.stdout,component['audited_exports'])
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'Pfv.'+'.'.join(relative.with_suffix('').parts)],
                output/'persistent-scalar-paths.coqchk.log',timeout)
            persistent.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                assumptions_accepted=audited,coq_checked=audited and k.returncode==0,
                accepted=audited and k.returncode==0)
        result.update(persistent_library=persistent,accepted=persistent['accepted'])
    (output/'persistent-scalar-paths.json').write_text(json.dumps(persistent,indent=2)+'\n')
    return result


def check_guard_binding_components(profile, output, timeout):
    """Gate sampled-input adapters without claiming reachable input facts."""
    if 'scalar_guard_library' not in profile:return None
    roots=profile.get('scalar_guard_roots',profile.get('scalar_path_roots',
        profile.get('scalar_expression_roots',profile.get('plan_slice_roots',
        profile.get('scalar_capture_roots')))))
    if roots is None:raise ValueError('scalar guard library requires observation roots')
    component=guard_bindings.check_profile(profile,output/'scalar-guards',roots,timeout)
    persistent=dict(accepted=False,status='checked_guard_component_required')
    result=dict(component=component,persistent_library=persistent,accepted=False,
        discharges_reachable_guards=False,discharges_token_identity=False,
        discharges_joint_preservation=False)
    if component['accepted']:
        partition=guard_partitions.check_profile(profile,output/'guard-partitions',roots,timeout)
        result['partition']=partition
        if not partition['accepted']:
            persistent['status']='checked_exhaustive_partition_required'
            (output/'persistent-scalar-guards.json').write_text(json.dumps(persistent,indent=2)+'\n')
            return result
        library=(adapter.ROOT/profile['scalar_guard_library']).resolve()
        try:relative=library.relative_to(adapter.ROOT/'src')
        except ValueError:
            raise ValueError('persistent scalar guard library must be a project Coq source') from None
        if library.suffix!='.v':
            raise ValueError('persistent scalar guard library must be a project Coq source')
        persistent=guard_bindings.emit_library(profile,library,roots,check=True)
        flags=flags_for(profile,output)
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
            output/'persistent-scalar-guards.coqc.log',timeout)
        persistent.update(accepted=False,coqc_exit=c.returncode,timed_out=t)
        if c.returncode==0:
            audited=scalar_captures.audit_output(c.stdout,component['audited_exports'])
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'Pfv.'+'.'.join(relative.with_suffix('').parts)],
                output/'persistent-scalar-guards.coqchk.log',timeout)
            persistent.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                assumptions_accepted=audited,coq_checked=audited and k.returncode==0,
                accepted=audited and k.returncode==0)
        result.update(persistent_library=persistent,accepted=persistent['accepted'])
    (output/'persistent-scalar-guards.json').write_text(json.dumps(persistent,indent=2)+'\n')
    return result


def check_instruction_components(profile,output,timeout,*,check_tagged=True):
    """Discover actual layout/origin evidence; do not discharge ISA identity."""
    if 'ast' not in profile:return None
    fields=instruction_fields.check_profile(profile,output/'instruction-fields',timeout)
    aliases=dict(accepted=False,status='checked_field_component_required')
    tagged=dict(accepted=False,status='checked_field_and_alias_components_required' if check_tagged else 'not_requested')
    persistent=None
    persistent_aliases=None
    if fields['accepted']:
        aliases=instruction_aliases.check_profile(profile,output/'instruction-word-aliases',timeout)
    if check_tagged and fields['accepted'] and aliases['accepted']:
        tagged=instruction_tags.check_profile(profile,output/'instruction-tagged-fields',timeout)
    snapshots=None
    sampled_snapshots=None
    if fields['accepted'] and aliases['accepted']:
        import cpu_field_snapshots
        snapshots=cpu_field_snapshots.check(profile,output/'instruction-fields',
            output/'instruction-word-aliases',output/'instruction-field-snapshots')
        import cpu_sampled_field_snapshots
        sampled_snapshots=cpu_sampled_field_snapshots.check(profile,output/'instruction-fields',
            output/'instruction-sampled-fields')
    if 'instruction_field_library' in profile:
        persistent=dict(accepted=False,status='checked_field_and_alias_components_required')
        if fields['accepted'] and aliases['accepted']:
            library=(adapter.ROOT/profile['instruction_field_library']).resolve()
            try:relative=library.relative_to(adapter.ROOT/'src')
            except ValueError:
                raise ValueError('persistent instruction field library must be a project Coq source') from None
            if library.suffix!='.v':
                raise ValueError('persistent instruction field library must be a project Coq source')
            persistent=instruction_fields.emit_library(profile,library,check=True)
            flags=flags_for(profile,output)
            c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
                output/'persistent-instruction-fields.coqc.log',timeout)
            persistent.update(accepted=False,coqc_exit=c.returncode,timed_out=t)
            if c.returncode==0:
                audited=scalar_captures.audit_output(c.stdout,fields['audited_exports'])
                k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                    'Pfv.'+'.'.join(relative.with_suffix('').parts)],
                    output/'persistent-instruction-fields.coqchk.log',timeout)
                persistent.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                    assumptions_accepted=audited,coq_checked=audited and k.returncode==0,
                    accepted=audited and k.returncode==0)
    (output/'persistent-instruction-fields.json').write_text(json.dumps(persistent,indent=2)+'\n')
    if 'instruction_word_alias_library' in profile:
        persistent_aliases=dict(accepted=False,status='checked_field_and_alias_components_required')
        if fields['accepted'] and aliases['accepted']:
            library=(adapter.ROOT/profile['instruction_word_alias_library']).resolve()
            try:relative=library.relative_to(adapter.ROOT/'src')
            except ValueError:
                raise ValueError('persistent word alias library must be a project Coq source') from None
            if library.suffix!='.v':raise ValueError('persistent word alias library must be a project Coq source')
            persistent_aliases=instruction_aliases.emit_library(profile,library,check=True)
            flags=flags_for(profile,output)
            c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
                output/'persistent-instruction-word-aliases.coqc.log',timeout)
            persistent_aliases.update(accepted=False,coqc_exit=c.returncode,timed_out=t)
            if c.returncode==0:
                audited=scalar_captures.audit_output(c.stdout,aliases['audited_exports'])
                k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                    'Pfv.'+'.'.join(relative.with_suffix('').parts)],
                    output/'persistent-instruction-word-aliases.coqchk.log',timeout)
                persistent_aliases.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                    assumptions_accepted=audited,coq_checked=audited and k.returncode==0,
                    accepted=audited and k.returncode==0)
    (output/'persistent-instruction-word-aliases.json').write_text(json.dumps(persistent_aliases,indent=2)+'\n')
    snapshot_ok=snapshots is not None and (snapshots['accepted'] or
        snapshots.get('status')=='no_supported_comb_snapshot')
    sampled_ok=sampled_snapshots is not None and (sampled_snapshots['accepted'] or
        sampled_snapshots.get('status')=='no_supported_sampled_fields')
    return dict(accepted=fields['accepted'] and aliases['accepted'] and (not check_tagged or tagged['accepted']) and snapshot_ok and sampled_ok and
        (persistent is None or persistent['accepted']) and
        (persistent_aliases is None or persistent_aliases['accepted']),fields=fields,aliases=aliases,
        tagged_fields=tagged,field_snapshots=snapshots,sampled_field_snapshots=sampled_snapshots,
        tagged_fields_requested=check_tagged,
        complete_instruction_component_scope_requested=check_tagged,
        persistent_library=persistent,persistent_alias_library=persistent_aliases,discharges_current_isa_identity=False,
        discharges_operand_freshness=False,discharges_joint_preservation=False)


def check_plan_slice_components(profile, output, timeout):
    """Generated guarded slices are local evidence, not instruction identity."""
    if 'plan_slice_roots' not in profile:
        if 'plan_slice_library' in profile:
            raise ValueError('persistent plan slice library requires declared roots')
        return None
    roots=profile['plan_slice_roots']
    component=plan_slices.check_profile(profile,output/'plan-slices',roots,timeout)
    result=dict(component=component,persistent_library=None,accepted=component['accepted'],
        discharges_token_identity=False)
    if 'plan_slice_library' not in profile:
        return result
    persistent=dict(accepted=False,status='checked_plan_slice_component_required')
    result.update(persistent_library=persistent,accepted=False)
    if component['accepted']:
        library=(adapter.ROOT/profile['plan_slice_library']).resolve()
        try:
            relative=library.relative_to(adapter.ROOT/'src')
        except ValueError:
            raise ValueError('persistent slice library must be a project Coq source') from None
        if library.suffix!='.v':
            raise ValueError('persistent slice library must be a project Coq source')
        persistent=plan_slices.emit_library(profile,library,roots,check=True)
        flags=flags_for(profile,output)
        compiled,timed=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
            output/'persistent-plan-slices.coqc.log',timeout)
        persistent.update(accepted=False,coqc_exit=compiled.returncode,timed_out=timed)
        if compiled.returncode==0:
            audited=scalar_captures.audit_output(compiled.stdout,component['audited_exports'])
            checked,check_timed=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',
                *flags,'-norec','Pfv.'+'.'.join(relative.with_suffix('').parts)],
                output/'persistent-plan-slices.coqchk.log',timeout)
            persistent.update(coqchk_exit=checked.returncode,coqchk_timed_out=check_timed,
                assumptions_accepted=audited,coq_checked=audited and checked.returncode==0,
                accepted=audited and checked.returncode==0)
        result.update(persistent_library=persistent,accepted=persistent['accepted'])
    (output/'persistent-plan-slices.json').write_text(json.dumps(persistent,indent=2)+'\n')
    return result


def check_scalar_components(profile, output, timeout):
    """Check declared local captures; never infer instruction identity from them.

    Explicit roots are adapter input, not an automatically proved architectural
    role. An optional persistent library must match regeneration AND pass its
    own compilation, closed audit and kernel check.
    """
    if 'scalar_rhs_library' in profile and 'scalar_capture_library' not in profile:
        raise ValueError('scalar RHS library requires checked persistent capture library')
    if 'scalar_capture_roots' not in profile:
        if 'scalar_capture_library' in profile:
            raise ValueError('persistent scalar library requires explicit capture roots')
        return None
    component = scalar_captures.check_profile(profile, output/'scalar-captures',
        profile['scalar_capture_roots'], timeout)
    result = {'component':component,'persistent_library':None,
        'accepted':component['accepted'], 'discharges_token_identity':False}
    if 'scalar_capture_library' not in profile:
        return result
    persistent = {'accepted':False,'status':'checked_scalar_component_required'}
    result['persistent_library'] = persistent
    result['accepted'] = False
    if component['accepted']:
        library = (adapter.ROOT/profile['scalar_capture_library']).resolve()
        try:
            relative = library.relative_to(adapter.ROOT/'src')
        except ValueError:
            raise ValueError('persistent scalar library must be a project Coq source') from None
        if library.suffix != '.v':
            raise ValueError('persistent scalar library must be a project Coq source')
        persistent = scalar_captures.emit_library(profile,library,
            profile['scalar_capture_roots'],check=True)
        flags = flags_for(profile,output)
        compiled,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',
            *flags,str(library)],output/'persistent-scalar.coqc.log',timeout)
        persistent.update(accepted=False,coqc_exit=compiled.returncode,timed_out=timed)
        if compiled.returncode == 0:
            audited = scalar_captures.audit_output(compiled.stdout,component['audited_exports'])
            logical = 'Pfv.'+'.'.join(relative.with_suffix('').parts)
            checked,check_timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),
                '-silent',*flags,'-norec',logical],output/'persistent-scalar.coqchk.log',timeout)
            persistent.update(coqchk_exit=checked.returncode,coqchk_timed_out=check_timed,
                assumptions_accepted=audited,coq_checked=audited and checked.returncode==0,
                accepted=audited and checked.returncode==0)
        result['persistent_library'] = persistent
        result['accepted'] = persistent['accepted']
    (output/'persistent-scalar.json').write_text(json.dumps(persistent,indent=2)+'\n')
    if 'scalar_rhs_library' in profile:
        rhs = {'accepted':False,'status':'checked_persistent_capture_library_required'}
        if result['accepted']:
            rhs = check_scalar_rhs_library(profile,output,timeout)
        result['rhs_library'] = rhs
        result['accepted'] = result['accepted'] and rhs['accepted']
        (output/'persistent-scalar-rhs.json').write_text(json.dumps(rhs,indent=2)+'\n')
    return result


def check_scalar_rhs_library(profile, output, timeout):
    library = (adapter.ROOT/profile['scalar_rhs_library']).resolve()
    base = (adapter.ROOT/profile['scalar_capture_library']).resolve()
    try:
        relative = library.relative_to(adapter.ROOT/'src')
        base_relative = base.relative_to(adapter.ROOT/'src')
    except ValueError:
        raise ValueError('scalar RHS and base libraries must be project Coq sources') from None
    if library.suffix != '.v' or base.suffix != '.v':
        raise ValueError('scalar RHS and base libraries must be project Coq sources')
    report = scalar_rhs.emit_library(profile,library,profile['scalar_capture_roots'],
        check=True,base_module='.'.join(base_relative.with_suffix('').parts),base_source=base)
    flags = flags_for(profile,output)
    compiled,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
        output/'persistent-scalar-rhs.coqc.log',timeout)
    report.update(accepted=False,coqc_exit=compiled.returncode,timed_out=timed)
    if compiled.returncode == 0:
        audited = scalar_captures.audit_output(compiled.stdout,len(profile['scalar_capture_roots']))
        checked,check_timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',
            *flags,'-norec','Pfv.'+'.'.join(relative.with_suffix('').parts)],
            output/'persistent-scalar-rhs.coqchk.log',timeout)
        report.update(coqchk_exit=checked.returncode,coqchk_timed_out=check_timed,
            assumptions_accepted=audited,coq_checked=audited and checked.returncode==0,
            accepted=audited and checked.returncode==0)
    return report


def check_comb_registry_components(profile, output, timeout):
    """Check actual imported processes; residuals are not full-phase proofs."""
    if 'ast' not in profile:
        return None
    mode = profile.get('comb_rule_prove_ordered', False)
    if type(mode) is not bool:
        raise ValueError('comb_rule_prove_ordered must be boolean')
    return comb_registry.check_profile(profile, output/'comb-rule-registry',
        timeout, prove_ordered=mode)


def check_two_stage_components(profile, output, timeout):
    if 'ast' not in profile:
        return None
    mode=profile.get('two_stage_prove_phase',False)
    if type(mode)is not bool:
        raise ValueError('two_stage_prove_phase must be boolean')
    return two_stage_producers.check_profile(profile,output/'two-stage-producers',
        timeout,prove_phase=mode)


def check_nba_producer_components(profile,output,timeout):
    """Same checked structural backend for any actual AST, not a CPU-name rule."""
    if 'ast' not in profile:
        return None
    return comb_residuals.check(profile,output/'nba-output-free-producers',
        timeout,include_nba=True)


def check_known_producer_components(profile,output,timeout):
    if 'ast' not in profile:
        return None
    return known_producers.check_profile(profile,output/'known-producers',timeout)


def check_phase_from_known(profile,component,output,timeout):
    if ('ast' not in profile or not component or not component.get('accepted') or
        not component.get('complete_original_producer_list_proved')):
        return None
    return known_phase.check(profile,output/'known-producers',output/'phase-from-known',timeout)


def known_phase_stage_accepted(report):
    # Unsupported static order is not a successful phase proof. It may use an
    # existing separately checked route, but any actual attempted proof failure
    # must reject the registered pipeline, irrespective of old global success.
    if report is None:
        return True
    if not report.get('eligibility_checked'):
        return False
    if report.get('status')=='original_phase_static_conditions_not_satisfied':
        return not report.get('accepted') and not report.get('original_full_phase_proved')
    return bool(report.get('accepted') and report.get('original_full_phase_proved')
        and report.get('status')=='proved_original_phase')


def persist_known_phase(profile,component,output,timeout):
    """Optional checked library export; never manufacture missing phase evidence."""
    if 'known_phase_library_stem' not in profile:
        return None
    if not (component and component.get('accepted') and component.get('original_full_phase_proved')):
        return dict(accepted=False,status='complete_checked_phase_required',
            actual_consumer_reconnected=False,new_global_invariant_synthesized=False)
    return known_phase_library.publish(profile,output/'known-producers',
        output/'phase-from-known',profile['known_phase_library_stem'],
        output/'persistent-known-phase',timeout)


def check_root_free_components(profile,component,output,timeout):
    if 'ast' not in profile or not component or not component.get('accepted'):
        return None
    return root_free_producers.check(profile,output/'known-producers',
        output/'root-free-producers',timeout,use_public_assembly=True)


def check_output_dependency_components(profile,output,timeout):
    if 'ast' not in profile:return None
    return output_dependency_slices.check(profile,output/'output-dependency-slices',timeout)


def check_bounded_catalog_components(profile,output,timeout):
    """Opt-in original-budget backend; failed native gates never use old success."""
    if 'bounded_catalog_library_stem' not in profile:return None
    result=dict(accepted=False,actual_consumer_reconnected=False,
        existing_shape_compatibility_proved=False,new_global_invariant_synthesized=False,
        itree_refinement_proved=False)
    if 'ast' not in profile:
        result['status']='actual_ast_required';return result
    provider=dependency_catalog.check(profile,output/'dependency-catalog',timeout)
    result['catalog']=provider
    if not(provider.get('accepted') and provider.get('metadata',{}).get('converges')
           and provider.get('metadata',{}).get('covers_writers')):
        result['status']='complete_convergent_catalog_required';return result
    phase=bounded_catalog_phase.check(profile,output/'dependency-catalog',
        output/'bounded-catalog-phase',timeout,share_static_catalog=True)
    result['phase']=phase
    if not(phase.get('accepted') and phase.get('original_full_phase_under_catalog_shape_proved')):
        result['status']='checked_original_budget_phase_required';return result
    persistent=bounded_catalog_library.publish(profile,output/'dependency-catalog',
        output/'bounded-catalog-phase',profile['bounded_catalog_library_stem'],
        output/'persistent-bounded-catalog',timeout)
    result.update(library=persistent,accepted=bool(persistent.get('accepted')),
        status='checked_catalog_phase_library' if persistent.get('accepted') else 'library_check_failed')
    return result


def check_covered_comb_phase(profile,coverage,output,timeout):
    """Discover eligibility from checked coverage, never a CPU-name list."""
    if ('ast' not in profile or coverage is None or not coverage.get('accepted')
        or coverage.get('counts',{}).get('residual')!=0):
        return None
    return comb_phase.check_profile(profile,output/'comb-full-phase',timeout)


def check_projected_register_components(profile,output,timeout):
    """Run checked read abstraction and its original ISA instance, fail closed."""
    import cpu_projected_read as projected
    if 'rf_port_library' not in profile:
        return dict(accepted=False,status='checked_RF_port_library_required',llm_calls=0,
            global_invariant_synthesized=False)
    budget=min(timeout,1200)
    reader=projected.check(profile,output/'projected-register-reads',timeout=budget)
    isa=None
    if reader['accepted']:
        isa=projected.check_isa(profile,output/'projected-register-reads',
            output/'projected-register-isa',timeout=budget)
    return dict(accepted=bool(reader['accepted']and isa and isa['accepted']),
        read=reader,original_isa=isa,llm_calls=0,global_invariant_synthesized=False)


def run_one(name, profile, output, timeout, use_llm, key, projected_register_reads=False):
    output.mkdir()
    profile=dict(profile);profile['design']=name
    (output/'joint-obligations.json').write_text(
        json.dumps(joint_obligations.plan(profile, adapter.ROOT),indent=2)+'\n')
    local = adapter.check_profile(profile, output/'semantics', timeout)
    registry = check_comb_registry_components(profile, output, timeout)
    phase = check_covered_comb_phase(profile,registry,output,timeout)
    stages = check_two_stage_components(profile, output, timeout)
    nba = check_nba_producer_components(profile, output, timeout)
    known = check_known_producer_components(profile, output, timeout)
    root_free = check_root_free_components(profile,known,output,timeout)
    dependency_slices = check_output_dependency_components(profile,output,timeout)
    phase_from_known = check_phase_from_known(profile, known, output, timeout)
    persistent_known_phase = persist_known_phase(profile,phase_from_known,output,timeout)
    bounded_catalog = check_bounded_catalog_components(profile,output,timeout)
    sliced = check_plan_slice_components(profile,output,timeout)
    expressions = check_scalar_expression_components(profile,output,timeout)
    paths = check_scalar_path_components(profile,output,timeout)
    guards = check_guard_binding_components(profile,output,timeout)
    instruction = check_instruction_components(profile,output,timeout)
    captures = check_scalar_components(profile,output,timeout)
    bank = bank_adapter.check_profile(profile, output/'bank-components', timeout)
    readers = bank_reads.check_profile(profile, output/'bank-reads', timeout)
    ports = rf_ports.check_profile(profile, output/'rf-ports', timeout)
    persistent_ports = None
    if 'rf_port_library' in profile:
        relative = profile['rf_port_library']
        library = (adapter.ROOT/relative).resolve()
        if not library.is_relative_to(adapter.ROOT/'src') or library.suffix != '.v':
            raise ValueError('persistent RF port library must be a project Coq source')
        persistent_ports = rf_ports.emit_library(profile, library, check=True)
        flags = flags_for(profile, output)
        compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q',
            *flags, str(library)], output/'persistent-rf-ports.coqc.log', timeout)
        persistent_ports.update(coqc_exit=compiled.returncode,timed_out=timed,accepted=False)
        if compiled.returncode == 0:
            audited = rf_ports.audit_output(compiled.stdout,ports['audited_exports'])
            logical = 'Pfv.' + '.'.join(library.relative_to(adapter.ROOT/'src').with_suffix('').parts)
            checked,check_timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),
                '-silent',*flags,'-norec',logical],output/'persistent-rf-ports.coqchk.log',timeout)
            persistent_ports.update(coqchk_exit=checked.returncode,coqchk_timed_out=check_timed,
                assumptions_accepted=audited,coq_checked=audited and checked.returncode==0,
                accepted=audited and checked.returncode==0)
        (output/'persistent-rf-ports.json').write_text(json.dumps(persistent_ports,indent=2)+'\n')
    process_ports = None
    if persistent_ports is not None and persistent_ports['accepted']:
        process_ports = rf_process_ports.check_profile(profile, output/'rf-process-ports', timeout)
    view_expression = None
    if process_ports is not None and process_ports['accepted']:
        view_expression = rf_view_expression.check_profile(profile, output/'rf-view-expression', timeout)
    projected_reads = check_projected_register_components(profile,output,timeout) if projected_register_reads else None
    persistent_view = None
    if 'rf_view_library' in profile:
        persistent_view = {'accepted':False,'status':'checked_RF_port_prerequisite_required'}
        if view_expression is not None and view_expression['accepted']:
            library = (adapter.ROOT/profile['rf_view_library']).resolve()
            if not library.is_relative_to(adapter.ROOT/'src') or library.suffix != '.v':
                raise ValueError('persistent RF view library must be a project Coq source')
            persistent_view = rf_view_expression.emit_library(profile,library,check=True)
            flags = flags_for(profile,output)
            compiled,timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(library)],
                output/'persistent-rf-view.coqc.log',timeout)
            persistent_view.update(coqc_exit=compiled.returncode,timed_out=timed,accepted=False)
            if compiled.returncode == 0:
                audited = rf_ports.audit_output(compiled.stdout,4*view_expression['ports'])
                logical = 'Pfv.'+'.'.join(library.relative_to(adapter.ROOT/'src').with_suffix('').parts)
                checked,check_timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',
                    *flags,'-norec',logical],output/'persistent-rf-view.coqchk.log',timeout)
                persistent_view.update(coqchk_exit=checked.returncode,coqchk_timed_out=check_timed,
                    assumptions_accepted=audited,coq_checked=audited and checked.returncode==0,
                    accepted=audited and checked.returncode==0)
        (output/'persistent-rf-view.json').write_text(json.dumps(persistent_view,indent=2)+'\n')
    persistent_bank = None
    if 'bank_library' in profile:
        relative = profile['bank_library']
        library = (adapter.ROOT/relative).resolve()
        if not library.is_relative_to(adapter.ROOT/'src') or library.suffix != '.v':
            raise ValueError('persistent bank library must be a project Coq source')
        persistent_bank = bank_adapter.emit_library(profile, library, check=True)
        flags = flags_for(profile, output)
        compiled, timed = run_stage([str(adapter.ROOT/'_opam/bin/coqc'), '-q',
            *flags, str(library)], output/'persistent-bank.coqc.log', timeout)
        persistent_bank.update(coqc_exit=compiled.returncode, timed_out=timed,
            accepted=False)
        if compiled.returncode == 0:
            audited, assumptions = bank_adapter.audit_bank_output(compiled.stdout,
                len(bank['generated_banks']))
            logical = 'Pfv.' + '.'.join(library.relative_to(adapter.ROOT/'src').with_suffix('').parts)
            checked, check_timed = run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),
                '-silent', *flags, '-norec', logical], output/'persistent-bank.coqchk.log', timeout)
            persistent_bank.update(coqchk_exit=checked.returncode,
                coqchk_timed_out=check_timed, assumptions_accepted=audited,
                inherited_assumptions=assumptions,
                coq_checked=audited and checked.returncode == 0,
                accepted=audited and checked.returncode == 0)
        (output/'persistent-bank.json').write_text(json.dumps(persistent_bank,indent=2)+'\n')
    packet = json.loads((output/'joint-obligations.json').read_text())
    packet['generated_physical_components'] = {
        'output_sensitive_dependency_rows': {
            'accepted':bool(dependency_slices and dependency_slices.get('accepted')),
            'report':'output-dependency-slices/report.json' if dependency_slices is not None else None,
            'checked_rows':dependency_slices.get('checked_rows') if dependency_slices else None,
            'rejected_rows':dependency_slices.get('rejected_rows') if dependency_slices else None,
            'discharges_joint_preservation':False},
        'root_independent_partial_write_producers': {
            'accepted':bool(root_free and root_free.get('accepted')),
            'report':'root-free-producers/report.json' if root_free is not None else None,
            'counts':root_free.get('counts') if root_free else None,
            'discharges_joint_preservation':False},
        'persistent_known_phase_library': {
            'accepted':bool(persistent_known_phase and persistent_known_phase.get('accepted')),
            'requested':'known_phase_library_stem' in profile,
            'report':'persistent-known-phase/report.json' if persistent_known_phase and
                persistent_known_phase.get('libraries') else None,
            'actual_consumer_reconnected':False,
            'discharges_joint_preservation':False},
        'phase_from_complete_known_producers': {
            'accepted':bool(phase_from_known and phase_from_known.get('accepted')),
            'report':'phase-from-known/report.json' if phase_from_known is not None else None,
            'status':phase_from_known.get('status') if phase_from_known else 'complete_producers_required',
            'original_full_phase_proved':bool(phase_from_known and phase_from_known.get('original_full_phase_proved')),
            'discharges_joint_preservation':False},
        'actual_fuel_known_producers': {
            'accepted':bool(known and known['accepted']),
            'report':'known-producers/report.json' if known is not None else None,
            'counts':known.get('counts') if known else None,
            'complete_original_producer_list_proved':bool(known and known.get('complete_original_producer_list_proved')),
            'discharges_joint_preservation':False},
        'output_independent_nba_producers': {
            'accepted':bool(nba and nba['accepted']),
            'report':'nba-output-free-producers/report.json' if nba is not None else None,
            'counts':nba.get('counts') if nba else None,
            'discharges_joint_preservation':False},
        'original_full_comb_phase': {
            'accepted':bool(phase and phase['accepted']),
            'report':'comb-full-phase/report.json' if phase is not None else None,
            'discharges_joint_preservation':False},
        'state_threaded_two_stage_producers': {
            'accepted':bool(stages and stages['accepted']),
            'report':'two-stage-producers/report.json' if stages is not None else None,
            'selected_count':len(stages.get('selected',[])) if stages is not None else 0,
            'original_full_phase_proved':bool(stages and stages.get('original_full_phase_proved')),
            'discharges_joint_preservation':False},
        'comb_rule_registry': {
            'accepted':bool(registry and registry['accepted']),
            'report':'comb-rule-registry/report.json' if registry is not None else None,
            'full_ordered_certificate_proved':bool(registry and
                registry.get('full_ordered_certificate_proved')),
            'discharges_joint_preservation':False},
        'instruction_layout_and_aliases': {
            'accepted':bool(instruction and instruction['accepted']),
            'layout_report':'instruction-fields/report.json' if instruction is not None else None,
            'alias_report':'instruction-word-aliases/report.json' if instruction and instruction['fields']['accepted'] else None,
            'discharges_current_isa_identity':False,'discharges_operand_freshness':False,
            'discharges_joint_preservation':False},
        'sampled_guard_bindings': {'accepted':bool(guards and guards['accepted']),
            'report':'scalar-guards/report.json' if guards is not None else None,
            'partition_report':'guard-partitions/report.json' if guards and 'partition' in guards else None,
            'discharges_reachable_guards':False,'discharges_token_identity':False,
            'discharges_joint_preservation':False},
        'guarded_scalar_paths': {'accepted':bool(paths and paths['accepted']),
            'report':'scalar-paths/report.json' if paths is not None else None,
            'discharges_reachable_guards':False,'discharges_token_identity':False},
        'guarded_scalar_expressions': {'accepted':bool(expressions and expressions['accepted']),
            'report':'scalar-expressions/report.json' if expressions is not None else None,
            'discharges_token_identity':False},
        'guarded_plan_slices': {'accepted':bool(sliced and sliced['accepted']),
            'report':'plan-slices/report.json' if sliced is not None else None,
            'discharges_token_identity':False},
        'scalar_captures': {'accepted':bool(captures and captures['accepted']),
            'report':'scalar-captures/report.json' if captures is not None else None,
            'discharges_token_identity':False},
        'rf_port_outputs': {'accepted': ports['accepted'],
            'report': 'rf-ports/report.json', 'port_count': len(ports['ports']),
            'discharges_operand_freshness': False},
        'rf_process_outputs': {'accepted': bool(process_ports and process_ports['accepted']),
            'report': 'rf-process-ports/report.json' if process_ports is not None else None,
            'observation': 'actual process entry/exit, not final LFP',
            'discharges_operand_freshness': False},
        'rf_view_expression': {'accepted': bool(view_expression and view_expression['accepted']),
            'report': 'rf-view-expression/report.json' if view_expression is not None else None,
            'physical_lane_zero_retained': True,
            'discharges_operand_freshness': False},
        'projected_register_reads': {'requested':projected_register_reads,
            'accepted':bool(projected_reads and projected_reads['accepted']),
            'read_report':'projected-register-reads/report.json' if projected_reads else None,
            'isa_report':'projected-register-isa/report.json' if projected_reads and projected_reads.get('original_isa') else None,
            'discharges_operand_freshness':False},
        'register_bank_reads': {'accepted': readers['accepted'],
            'report': 'bank-reads/report.json', 'site_count': len(readers['sites']),
            'discharges_operand_freshness': False},
        'register_bank': {'accepted': bank['accepted'],
            'report': 'bank-components/report.json',
            'exports': [item.get('exports', {}) for item in bank['generated_banks']],
            'discharges_global_invariant_obligations': False}}
    (output/'joint-obligations.json').write_text(json.dumps(packet,indent=2)+'\n')
    suggestions = roles.suggest_roles(profile, output/'roles', use_llm, key)
    if 'joint_binding' in profile or 'api' in profile:
        global_result = assemble_contract(profile, output/'contract', timeout)
    else:
        global_result = {'accepted':False, 'status':'global_templates_required',
            'runtime_bindings_required':['commit observer','ISA state relation','reset/boot environment'],
            'proofs_required':['joint initialization','cycle/segment restoration','progress']}
        (output/'global-obligations.json').write_text(json.dumps(global_result,indent=2)+'\n')
    report = {'design': name, 'local_semantic_generation_accepted': local['local_semantics_accepted'],
        'comb_rule_registry_generation': registry,
        'automatic_original_full_phase_generation': phase,
        'state_threaded_two_stage_generation': stages,
        'output_independent_nba_producer_generation':nba,
        'actual_fuel_known_producer_generation':known,
        'root_independent_partial_write_producers':root_free,
        'output_sensitive_dependency_rows':dependency_slices,
        'phase_from_complete_known_producers':phase_from_known,
        'persistent_known_phase_library':persistent_known_phase,
        'original_budget_catalog_phase_library':bounded_catalog,
        'physical_bank_component_generation_accepted': bank['accepted'],
        'physical_bank_read_generation_accepted': readers['accepted'],
        'actual_rf_port_generation_accepted': ports['accepted'],
        'scalar_capture_generation': captures,
        'guarded_plan_slice_generation': sliced,
        'guarded_scalar_expression_generation': expressions,
        'guarded_scalar_path_generation': paths,
        'sampled_guard_binding_generation': guards,
        'instruction_layout_and_alias_generation': instruction,
        'generated_actual_rf_ports': len(ports['ports']),
        'persistent_rf_port_library': persistent_ports,
        'process_rf_port_generation': process_ports,
        'rf_view_expression_generation': view_expression,
        'projected_register_read_generation':projected_reads,
        'persistent_rf_view_library': persistent_view,
        'generated_physical_bank_read_sites': len(readers['sites']),
        'persistent_bank_library': persistent_bank,
        'generated_physical_bank_components': len(bank['generated_banks']),
        'bank_component_residuals': bank['residuals'],
        'bank_component_isa_effects_still_require_proof': True,
        'automatic_sequential_processes': local['generated_sequential_plans']+
            local['generated_state_threaded_effect_plans'],
        'sequential_processes': local['sequential_processes'],
        'phase_projections': local['generated_compiled_phase_projections'],
        'semantic_consequences': local['generated_semantic_consequences'],
        'local_residuals': local['residual_processes'],
        'existing_global_evidence_itree_assembly_accepted': global_result['accepted'] and not bool(profile.get('joint_binding')),
        'new_joint_local_evidence_itree_assembly_accepted': global_result['accepted'] and bool(profile.get('joint_binding')),
        'global_evidence_origin':global_result.get('global_evidence_origin','unproved'),
        'new_global_invariant_synthesized': False,
        'new_design_from_rtl_end_to_end_automatic': False,
        'llm': suggestions['llm'],
        'architectural_roles': 'UNPROVED proposals; not used to change fixed contract fields',
        'remaining_automatic_synthesis': ['commit identity', 'architecture binding',
            'instruction/operand freshness invariant', 'joint initialization and preservation',
            'environment-aware progress proof']}
    report['registered_design_pipeline_accepted'] = (
        report['local_semantic_generation_accepted'] and bank['accepted'] and readers['accepted']
        and ports['accepted'] and global_result['accepted']
        and (registry is None or registry['accepted'])
        and (phase is None or phase['accepted'])
        and (stages is None or stages['accepted'])
        and (nba is None or nba['accepted'])
        and (known is None or known['accepted'])
        and (root_free is None or root_free['accepted'])
        and (dependency_slices is None or dependency_slices['accepted'])
        and known_phase_stage_accepted(phase_from_known)
        and (persistent_known_phase is None or persistent_known_phase.get('accepted',False))
        and (bounded_catalog is None or bounded_catalog.get('accepted',False))
        and (sliced is None or sliced['accepted'])
        and (expressions is None or expressions['accepted'])
        and (paths is None or paths['accepted'])
        and (guards is None or guards['accepted'])
        and (instruction is None or instruction['accepted'])
        and (captures is None or captures['accepted'])
        and (persistent_ports is None or persistent_ports['accepted'])
        and (process_ports is None or process_ports['accepted'])
        and (view_expression is None or view_expression['accepted'])
        and (not projected_register_reads or bool(projected_reads and projected_reads['accepted']))
        and (persistent_view is None or persistent_view['accepted'])
        and (persistent_bank is None or persistent_bank['accepted']))
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report), flush=True)
    return report


def resolve_ast_input(file, ast_module=None, program=None):
    """Reuse registered global evidence only on exact imported-source identity.

    Unknown syntax still receives local proof generation; no guessed global
    invariant or nearest-looking CPU certificate is silently substituted.
    """
    file=Path(file).resolve()
    digest=hashlib.sha256(file.read_bytes()).hexdigest()
    source_matches=[]
    for p in sorted((adapter.ROOT/'framework/auto-contract-profiles').glob('*.json')):
        profile=json.loads(p.read_text())
        known=adapter.ROOT/profile['ast']['file']
        if hashlib.sha256(known.read_bytes()).hexdigest()==digest:
            source_matches.append((p.stem,profile))
    if source_matches:
        matches=[(name,profile) for name,profile in source_matches
            if (ast_module is None or ast_module==profile['ast']['module'])
            and (program is None or program==profile['ast']['program'])]
        if not matches:
            raise ValueError('registered AST module/program differs from requested binding; '
                'provide an explicit --profile for the requested runtime')
        if len(matches)!=1:
            raise ValueError('ambiguous registered AST runtime; choose an explicit --profile')
        name,profile=matches[0]
        return name,profile,'exact_registered_AST_identity'
    if not ast_module or not program:
        raise ValueError('unknown AST: provide --ast-module and --program for local proof generation')
    return 'new-design',{'ast':{'file':str(file),'module':ast_module,'program':program}},'unseen_AST_global_templates_required'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile', action='append', type=Path)
    parser.add_argument('--ast',type=Path)
    parser.add_argument('--ast-module')
    parser.add_argument('--program')
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=1200)
    parser.add_argument('--use-llm', action='store_true')
    parser.add_argument('--key-from-note', action='store_true')
    parser.add_argument('--projected-register-reads',action='store_true',
        help='Generate path-sensitive RF read and original ISA view proofs; require both to pass')
    args = parser.parse_args()
    if args.output.exists():
        parser.error('output must be fresh; preserve previous evidence')
    if not 1 <= args.jobs <= 4 or not 0 < args.timeout <= 3600:
        parser.error('jobs must be 1..4 and timeout 0..3600 seconds (default1200)')
    if args.key_from_note and not args.use_llm:
        parser.error('--key-from-note requires --use-llm')
    key = (roles.key_from_note() if args.key_from_note else os.environ.get('DASHSCOPE_API_KEY')) if args.use_llm else None
    selection='explicit_profiles' if args.profile else 'registered_four_designs'
    if args.ast:
        if args.profile:
            parser.error('--ast and --profile are mutually exclusive')
        try:
            name,profile,selection=resolve_ast_input(args.ast,args.ast_module,args.program)
        except ValueError as exc:
            parser.error(str(exc))
        profiles=[(name,profile)]
    else:
        paths = args.profile or sorted((adapter.ROOT/'framework/auto-contract-profiles').glob('*.json'))
        profiles = [(p.stem, json.loads(p.read_text())) for p in paths]
    args.output.mkdir(parents=True)
    environment = {'conda_environment': os.environ.get('CONDA_DEFAULT_ENV'),
        'profile_selection':selection,
        'coqc': subprocess.check_output([str(adapter.ROOT/'_opam/bin/coqc'), '--version'], text=True),
        'git_head': subprocess.check_output(['git','rev-parse','HEAD'], cwd=adapter.ROOT,text=True).strip(),
        'profiles': {name: hashlib.sha256(json.dumps(p,sort_keys=True).encode()).hexdigest() for name,p in profiles}}
    (args.output/'environment.json').write_text(json.dumps(environment,indent=2)+'\n')
    shared = check_shared(args.output/'shared', args.timeout)
    if len(shared)!=len(SHARED_MODULES) or any(
        r.get('coqchk_exit') != 0 or not r.get('assumptions_accepted',False) for r in shared):
        print('Shared semantic rule check failed; inspect retained logs.');return 1
    started=time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(run_one,name,p,args.output/name,args.timeout,args.use_llm,key,args.projected_register_reads)
                   for name,p in profiles]
        reports = [f.result() for f in futures]
    report = {'schema_version':1, 'registered_designs':reports, 'shared_modules':shared,
        'wall_seconds':time.monotonic()-started,
        'all_registered_pipelines_accepted':all(r['registered_design_pipeline_accepted'] for r in reports),
        'goal_of_unseen_cpu_global_proof_generation_complete':False,
        'local_proofs_origin':'deterministic AST to checked semantic plans',
        'global_proofs_origin':'per-design global_evidence_origin; old global assembly or NEW Joint from existing local component evidence'}
    (args.output/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
    return 0 if report['all_registered_pipelines_accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
