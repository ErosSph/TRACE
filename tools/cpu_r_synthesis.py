"""ISA-demand-driven R synthesis frontier, with no old CPU INV input.

The ISA scan is a conservative obligation proposal, not a footprint theorem.
Physical bank certificates are checked against the original AST. Generated
RF relations and their conditional transport do NOT discharge ISA ownership,
operand freshness, initialization, or complete R preservation.
"""
import argparse
import hashlib
import json
import os
import re
import time
from pathlib import Path

import cpu_pending_origins as origin
import cpu_instruction_scope as instruction_scopes
import cpu_auto_roles as roles
import cpu_bank_adapter as bank
import cpu_write_ownership_frontier as write_ownership
import cpu_r_operand_frontier as operands
import cpu_operand_routes as operand_routes
import cpu_operand_route_proofs as route_proofs
import cpu_operand_reference_requirements as reference_requirements
import cpu_computed_r_transfer as computed_r_transfer
import cpu_operand_phase_requirements as phase_requirements
import cpu_computed_phase_r as computed_phase_r
import cpu_effect_requirements as effect_requirements
import cpu_computed_effect_r as computed_effect_r
import cpu_ready_selection_requirements as ready_selection
import cpu_operand_address_origins as address_origins
import cpu_decoded_address_connection as decoded_addresses
import cpu_capture_address_connection as capture_addresses
import cpu_history_address_connection as history_addresses
import cpu_registered_address_history as registered_addresses
import cpu_tagged_capture_addresses as tagged_capture_addresses
import cpu_address_case_completion as address_case_completion
import cpu_operand_branch_proofs as branch_proofs
import cpu_blocking_selector as selector_proofs
import cpu_selector_sources as selector_sources
import cpu_selector_metadata as selector_metadata
import cpu_control_capture_frontier as control_captures
import cpu_pending_projection_origins as projection_origins
import cpu_selector_joint_connection as selector_joint
import cpu_nonzero_capture as nonzero_capture
import cpu_nonzero_projection_history as nonzero_projection
import cpu_synchronized_values as synchronized_values
import cpu_r_validity_strategy as validity_strategy
import cpu_zero_instruction_rf as zero_instruction_rf
import cpu_r_write_strategy as write_strategy
import cpu_write_address_history as write_address_history
import cpu_field_chain_history as field_chain_history
import cpu_capture_field_chain as capture_field_chain
import cpu_capture_chain_coverage as capture_chain_coverage
import cpu_word_field_copy as word_field_copy
import cpu_field_selector_origin as field_selector_origin
import cpu_field_selector_gap as field_selector_gap
import cpu_blocking_residuals as blocking_residuals
import cpu_operand_capture_proofs as capture_proofs
from cpu_certificate_acceptance import run_stage

ROOT = origin.ROOT
def exit_status(result, components_checked, analysis_only=False):
    """Exit policy, not a substitute for native proof/evidence validation.

    Component successes (including explicit unsupported statuses) do not
    establish an end-to-end generated invariant. Missing flags fail closed.
    """
    if analysis_only:
        return 0
    required=('complete_R_generated','initialization_proved','preservation_proved')
    return 0 if components_checked and all(result.get(k) is True for k in required) else 1

PRIMITIVES = {
    'getRegister': 'source_register_value', 'setRegister': 'register_write_value',
    'getPC': 'instruction_pc', 'setPC': 'redirect_target',
    'loadByte': 'memory_read', 'loadHalf': 'memory_read', 'loadWord': 'memory_read',
    'storeByte': 'memory_write', 'storeHalf': 'memory_write', 'storeWord': 'memory_write',
    'raiseExceptionWithInfo': 'exception_or_domain_certificate', 'fence': 'fence',
}


def backward_frontier(ast, destination):
    """Overapproximate control/address/data dependencies, stopping at registers.

    All process readers are retained, including branch and write-index readers.
    This is a synthesis search graph, not a semantic slicing certificate.
    """
    rtl = origin.pending.rtl
    writers = {}
    for proc in ast['processes']:
        reads = sorted({int(n.args[1].name) for n in rtl.walk(proc['body']) if n.name == 'EVar'})
        row = dict(process=proc['name'], kind=proc['kind'], reads=reads,
                   events=proc['events'], source_line=proc['line'])
        for root in proc['writers']: writers.setdefault(root, []).append(row)
    owners = writers.get(destination, [])
    seeds = sorted({r for row in owners for r in row['reads']})
    todo = list(seeds); seen = set(); edges = []; registers = []; inputs = []
    mixed = []
    while todo:
        root = todo.pop()
        if root in seen: continue
        seen.add(root)
        rows = writers.get(root, [])
        if not rows:
            inputs.append(root); continue
        if any(row['kind'] == 'Sequential' for row in rows):
            registers.append(root)
            if any(row['kind'] != 'Sequential' for row in rows): mixed.append(root)
            continue
        for row in rows:
            edges.append(dict(root=root, **row))
            todo.extend(row['reads'])
    return dict(destination=destination, write_processes=owners, roots=seeds,
                combinational_edges=edges, sequential_boundary=sorted(registers),
                external_inputs=sorted(inputs), mixed_writer_residuals=sorted(mixed),
                semantic_slice_proved=False,
                phase_policy='stop at sequential boundaries; do not equate old and sampled values')


def remove_comments(source):
    depth = 0
    out = []
    i = 0
    while i < len(source):
        if source[i:i+2] == '(*':
            depth += 1; out.append('  '); i += 2
        elif source[i:i+2] == '*)':
            if not depth: raise ValueError('unmatched comment')
            depth -= 1; out.append('  '); i += 2
        else:
            out.append(source[i] if not depth or source[i] == '\n' else ' '); i += 1
    if depth: raise ValueError('unterminated comment')
    return ''.join(out)


def isa_input_uses(body, operands):
    """Retain actual ISA argument uses, never infer roles from rs/imm names.

    This scanner proposes obligations only. Original ExecuteI/run1 proofs
    remain authoritative. Parameter representation/sign extension is kept
    verbatim, not reconstructed from an instruction name.
    """
    inputs, destinations = [], []
    accounted = set()
    for match in re.finditer(r'Spec\.Machine\.(getRegister|setRegister)\s+([A-Za-z_]\w*)\b', body):
        primitive, field = match.groups()
        if field not in operands:
            raise ValueError('ISA register argument is not a declared constructor field')
        accounted.add(field)
        item = dict(field=field, primitive=primitive, body_offset=match.start())
        if primitive == 'getRegister':
            inputs.append(dict(kind='register_value', **item))
        else:
            destinations.append(item)
    # Reject computed/register syntax that this scanner did not parse.
    for primitive, found in [('getRegister',sum(x['primitive']=='getRegister' for x in inputs)),
                              ('setRegister',len(destinations))]:
        if len(re.findall(r'Spec\.Machine\.'+primitive+r'\b',body)) != found:
            raise ValueError('unsupported ISA register argument syntax')
    for match in re.finditer(r'Spec\.Machine\.getPC\b',body):
        inputs.append(dict(kind='instruction_pc',primitive='getPC',body_offset=match.start()))
    for field in operands:
        if field in accounted:
            continue
        occurrences=[m.start() for m in re.finditer(r'\b'+re.escape(field)+r'\b',body)]
        if not occurrences:
            raise ValueError('unused ISA constructor field requires explicit handling')
        inputs.append(dict(kind='instruction_parameter',field=field,
            body_offset=occurrences[0], occurrences=occurrences,
            representation='original constructor value; conversions retained in execute_body'))
    inputs.sort(key=lambda x:x['body_offset'])
    return dict(inputs=inputs,destinations=destinations,execute_body=body.strip(),
                roles_inferred_from_names=False,semantic_input_correspondence_proved=False)


def isa_demands(source):
    clean = remove_comments(source)
    branches = list(re.finditer(r'^    \| Spec\.Decode\.(\w+) ([^\n]*?)=>', clean, re.M))
    # Fence_i has no operands and the whitespace before => belongs to the separator.
    if not branches: raise ValueError('no supported execute match')
    rows = []
    for index, match in enumerate(branches):
        end = branches[index+1].start() if index+1 < len(branches) else clean.index('    | inst =>', match.end())
        body = clean[match.end():end]
        calls = sorted(set(re.findall(r'Spec\.Machine\.(\w+)', body)) - {'Execute', 'Load', 'Store'})
        unknown = sorted(set(calls) - PRIMITIVES.keys())
        if unknown: raise ValueError('unsupported ISA primitives: ' + ','.join(unknown))
        if match[1] == 'Fence': continue  # Not in the requested 37 + FENCE.I scope.
        rows.append(dict(instruction=match[1], operands=match[2].split(),
            reference_uses=isa_input_uses(body,match[2].split()),
            source_line=clean[:match.start()].count('\n')+1,
            body_sha256=hashlib.sha256(body.encode()).hexdigest(), calls=calls,
            obligations=sorted({PRIMITIVES[c] for c in calls} |
                {'instruction_identity', 'instruction_fetch', 'retired_pc',
                 'register_frame', 'memory_frame', 'next_pc'})))
    if len(rows) != 38 or len({r['instruction'] for r in rows}) != 38:
        raise ValueError('expected exactly 38 original ISA branches; fail closed')
    return dict(source_sha256=hashlib.sha256(source.encode()).hexdigest(), instructions=rows,
                semantic_footprint_soundness_proved=False,
                explanation='source primitive scan proposes obligations; it never removes a Coq obligation')


def register_relation_source(root):
    return f'''From Coq Require Import ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVRegisterBank Lang.ExtendedSVBankPlan
 Ex.External.CPURegisterEffectRelation Ex.RvCore.FormalSpec
 coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte GeneratedBank.AutoBank.
Import ExtendedSV ExtendedSVRegisterBank ExtendedSVBankPlan CPURegisterEffectRelation.
Section GeneratedRelation.
Context {{word:Interface.word 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}.
Definition R_register(s:State)(a:FormalSpec.State):Prop:=
 RegisterRelated(lane_read 32(read_signal s {root}))a.
Definition actual_register_updates ev pre := bank_phase_operations 1024 pre
 (phase_driven_state _ ev pre) GeneratedBank.AutoBank.bank_{root}_entries.
End GeneratedRelation.
'''


def relation_source(root, program):
    source = register_relation_source(root).replace('(phase_driven_state _ ev pre)',
                                                   f'(phase_driven_state {program} ev pre)')
    source = source.replace('End GeneratedRelation.', f'''
Theorem R_register_transport ev pre before after:
 changed_signal ev<>{root}%nat ->R_register pre before ->
 ISAProjectedRegisterEffects before after(actual_register_updates ev pre) ->
 R_register(PhaseSemantics {program} ev pre)after.
Proof. exact(GeneratedBank.AutoBank.bank_{root}_isa_relation ev pre before after). Qed.
End GeneratedRelation.
Print Assumptions R_register_transport.''')
    return source


def check_isa_input_certificate(output, instruction_scope='rv32i38'):
    # Lazy import: the certificate generator reuses the original-source scan.
    import cpu_isa_input_certificate
    return cpu_isa_input_certificate.run(output,instruction_scope)


def run(ast_path, ast_module, output, use_llm=False, key=None, native=True):
    output = Path(output); output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    instruction_scope = instruction_scopes.for_input(ast_path,ast_module)
    spec = instruction_scopes.select(
        isa_demands((ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text()),instruction_scope)
    ast, profile, paths = origin.raw_binding(ast_path, ast_module)
    routes = operand_routes.discover(ast)
    (output/'operand_routes.json').write_text(json.dumps(routes, indent=2)+'\n')
    profile['coq_load_paths'] = paths
    candidates = roles.derive_candidates(ast)
    bindings = {role: dict(id=rows[0]['id'], origin='unique_structure', proved=False)
                for role, rows in candidates.items() if len(rows) == 1}
    unresolved = [role for role in candidates if role not in bindings]
    llm = dict(attempts=0, status='not_requested')
    ambiguous = [role for role in unresolved if candidates[role]]
    if use_llm and ambiguous:
        llm = roles.call_llm(candidates, ambiguous, key)
        for role, ident in llm.get('bindings', {}).items():
            bindings[role] = dict(id=ident, origin='llm_candidate', proved=False)
    plan = dict(schema_version=1, isa=spec, ast_sha256=ast['source_sha256'],
        actual_program=profile['ast']['program'], role_candidates=candidates, bindings=bindings,
        operand_routes_file='operand_routes.json',
        register_write_frontiers=[backward_frontier(ast, row['root']) for row in candidates['register_file']],
        per_write_ownership_frontier=write_ownership.analyze(ast),
        proposed_components=['committed_registers', 'pending_source_values', 'pending_results',
            'instruction_pc_order', 'rom_image', 'ram_effects', 'validity_and_ownership'],
        old_inv_read=False, old_cpu_proofs_used_for_synthesis=False,
        llm=llm, complete_R_generated=False)
    (output/'plan.json').write_text(json.dumps(plan, indent=2)+'\n')
    report = dict(accepted=False, goal_complete=False, old_inv_read=False,
        instruction_scope=instruction_scope, selected_instruction_count=len(spec['instructions']),
        excluded_instructions=spec['excluded_instructions'],
        complete_R_generated=False, initialization_proved=False, preservation_proved=False,
        itree_refinement_proved=False, llm=llm,
        operand_routes=dict(analysis_completed=True, count=len(routes['routes']),
            semantic_routes_checked=False, operand_freshness_proved=False),
        residuals=['pending operand freshness', 'ISA effect/retirement ownership',
                   'ROM and RAM mapping', 'PC order', 'initialization and full cycle preservation'])
    if native:
        import cpu_bank_index_certificate
        report['bank_index_certificate']=cpu_bank_index_certificate.check(
            ast_path,ast_module,output/'bank-indices')
        import cpu_fixed_lane_enable
        report['fixed_lane_enable_certificate']=cpu_fixed_lane_enable.check(
            ast_path,ast_module,output/'fixed-lane-enable')
        import cpu_fixed_lane_lfp
        if report['fixed_lane_enable_certificate'].get('accepted') is True:
            report['fixed_lane_lfp_certificate']=cpu_fixed_lane_lfp.check(
                ast_path,ast_module,output/'fixed-lane-enable',output/'fixed-lane-lfp')
        else:
            report['fixed_lane_lfp_certificate']=dict(accepted=False,
                status='local_decoder_certificate_not_available',
                full_lfp_bit_connection_proved=False,complete_R_generated=False)
        import cpu_isa_destination_certificate
        report['isa_destination_certificate']=cpu_isa_destination_certificate.run(
            output/'isa-destination-certificate',instruction_scope)
        report['isa_input_certificate']=check_isa_input_certificate(output/'isa-input-certificate',instruction_scope)
        report['decoded_address_connections']=decoded_addresses.run(ast_path,ast_module,output/'decoded-address-connections')
        import cpu_destination_field_connection
        field_provider=report['decoded_address_connections'].get('provider')
        if report['isa_destination_certificate'].get('accepted') is True and field_provider:
            report['destination_field_connections']=cpu_destination_field_connection.check(
                ast_path,ast_module,field_provider,output/'isa-destination-certificate',
                output/'destination-field-connections')
        else:
            report['destination_field_connections']=dict(accepted=False,
                status='checked_field_or_isa_provider_unavailable',complete_R_generated=False)
    chosen = bindings.get('register_file')
    if chosen and native:
        physical = bank.check_profile(profile, output/'bank')
        report['physical_bank_check'] = physical
        # Same rule for every supported complete bank, including reset and
        # prioritized multi-writer designs. This generates obligations only.
        if physical['accepted']:
            import cpu_bank_requirements
            report['register_restoration_requirements']=cpu_bank_requirements.check(
                ast_path,ast_module,output/'register-restoration-requirements')
        if report['isa_destination_certificate'].get('accepted') is True:
            import cpu_destination_dispatch
            report['write_destination_dispatch']=cpu_destination_dispatch.run(
                ast_path,ast_module,output/'isa-destination-certificate',
                output/'write-destination-dispatch',field_provider,
                output/'bank' if physical['accepted'] else None,native=True)
        root = int(chosen['id'].removeprefix('root_'))
        checked = {b['root'] for b in physical['generated_banks']}
        if physical['accepted'] and root in checked:
            source = f'Require Import {ast_module}.\n' + relation_source(root, profile['ast']['program'])
            path = output/'RegisterR.v'; path.write_text(source)
            flags = list(origin.pending.rtl.framework.FLAGS)
            for row in paths: flags += ['-R', row['directory'], row['namespace']]
            flags += ['-R', str(output.resolve()), 'GeneratedR',
                      '-R', str((output/'bank').resolve()), 'GeneratedBank']
            c, timed = run_stage([str(ROOT/'_opam/bin/coqc'), '-time', *flags, str(path.resolve())],
                                output/'RegisterR.coqc.log', 1200)
            item = dict(coqc_exit=c.returncode, timed_out=timed,
                        source_sha256=hashlib.sha256(source.encode()).hexdigest(), accepted=False)
            if c.returncode == 0:
                item['assumptions_closed'] = c.stdout.count('Closed under the global context') == 1 and 'Axioms:' not in c.stdout
                k, timed = run_stage([str(ROOT/'_opam/bin/coqchk'), '-silent', *flags,
                    '-norec', 'GeneratedR.RegisterR'], output/'RegisterR.coqchk.log', 1200)
                item.update(coqchk_exit=k.returncode, coqchk_timed_out=timed,
                            accepted=k.returncode == 0 and item['assumptions_closed'])
            report['register_R_component'] = item
            if item['accepted']:
                import cpu_register_result_r
                report['computed_register_result_R'] = cpu_register_result_r.check(
                    ast_path, ast_module, output/'computed-register-result')
    if native:
        report['operand_clauses'] = operands.check(ast_path, ast_module, output/'operands')
        report['operand_route_equations'] = route_proofs.check(ast_path, ast_module, output/'route-equations')
        if report['operand_route_equations'].get('accepted'):
            report['guarded_operand_requirements'] = ready_selection.check(
                ast_path, ast_module, output/'route-equations', output/'guarded-selection')
        else:
            report['guarded_operand_requirements'] = dict(accepted=False,
                status='raw_output_provider_unavailable', complete_R_generated=False)
        if report['operand_route_equations'].get('accepted') and report['isa_input_certificate'].get('accepted'):
            report['operand_reference_requirements'] = reference_requirements.check(
                ast_path, ast_module, output/'route-equations', output/'source-reference',
                isa_provider=output/'isa-input-certificate')
        else:
            report['operand_reference_requirements'] = dict(accepted=False,
                status='raw_output_or_scoped_isa_provider_unavailable', complete_R_generated=False)
        if report['operand_reference_requirements'].get('accepted'):
            report['computed_source_R_transfer']=computed_r_transfer.check(
                ast_path,ast_module,output/'source-reference',output/'computed-source-transfer')
            if report['computed_source_R_transfer'].get('accepted'):
                report['computed_source_phase_certificates']=phase_requirements.check(
                    ast_path,ast_module,output/'computed-source-phase-certificates')
                if report['computed_source_phase_certificates'].get('phase_value_relations_checked'):
                    report['computed_source_phase_R']=computed_phase_r.check(
                        ast_path,ast_module,output/'computed-source-phase-certificates',
                        output/'computed-source-transfer',output/'computed-source-phase-R')
                else:
                    report['computed_source_phase_R']=dict(accepted=False,
                        status='no_checked_scalar_phase_provider',complete_R_generated=False)
                phase=report['computed_source_phase_certificates']
                if phase.get('outputs') or phase.get('residuals'):
                    report['computed_source_effect_certificates']=effect_requirements.check(
                        ast_path,ast_module,output/'computed-source-effect-certificates')
                    if report['computed_source_effect_certificates'].get('accepted'):
                        report['computed_source_effect_R']=computed_effect_r.check(
                            ast_path,ast_module,output/'computed-source-effect-certificates',
                            output/'source-reference',output/'computed-source-effect-R')
                    else:
                        report['computed_source_effect_R']=dict(accepted=False,
                            status='no_checked_complete_effect_provider',complete_R_generated=False)
        else:
            report['computed_source_R_transfer']=dict(accepted=False,
                status='checked_source_R_provider_unavailable',complete_R_generated=False)
        report['operand_branch_equations'] = branch_proofs.check(ast_path, ast_module, output/'branch-equations')
        report['operand_selector_equations'] = selector_proofs.check_discovered(ast_path, ast_module, output/'selector-equations')
        report['operand_selector_sources'] = selector_sources.check(ast_path, ast_module, output/'selector-sources')
        if report['operand_selector_sources'].get('accepted'):
            report['operand_selector_metadata'] = selector_metadata.check_auto(ast_path, ast_module,
                output/'selector-sources',output/'selector-metadata')
        else:
            report['operand_selector_metadata'] = dict(accepted=False,status='source_certificates_unavailable')
        report['operand_capture_equations'] = capture_proofs.check(ast_path, ast_module, output/'capture-equations')
        report['control_capture_producers'] = control_captures.check(ast_path, ast_module, output/'control-producers')
        report['control_capture_histories'] = control_captures.check_histories(ast_path, ast_module, output/'control-histories')
        report['control_capture_transforms'] = control_captures.check_transforms(ast_path, ast_module, output/'control-transforms')
        report['synchronized_field_relations'] = projection_origins.check_synchronized(ast_path, ast_module, output/'synchronized-fields')
        report['narrow_field_histories'] = projection_origins.check_narrow(ast_path, ast_module, output/'narrow-field-histories')
        report['field_chain_histories'] = field_chain_history.check(ast_path, ast_module, output/'field-chain-histories')
        report['capture_field_chains'] = capture_field_chain.check(ast_path, ast_module, output/'capture-field-chains')
        report['capture_chain_coverage'] = capture_chain_coverage.check(ast_path, ast_module, output/'capture-chain-coverage')
        report['word_field_copies'] = word_field_copy.check(ast_path, ast_module, output/'word-field-copies')
        report['field_selector_origins'] = field_selector_origin.check(ast_path, ast_module, output/'field-selector-origins')
        report['projected_selector_origins'] = field_selector_origin.check(ast_path, ast_module, output/'projected-selector-origins', projected=True)
        report['blocking_residual_connections'] = blocking_residuals.run(ast_path, ast_module, output/'blocking-residual-connections')
        report['write_address_histories'] = write_address_history.check(ast_path, ast_module, output/'write-address-histories')
        report['selector_joint_relations'] = selector_joint.check_auto(ast_path, ast_module, output/'selector-joint')
        report['nonzero_capture_histories'] = nonzero_capture.check(ast_path, ast_module, output/'nonzero-histories')
        report['source_history_projections'] = nonzero_projection.check(ast_path, ast_module, output/'source-history-projections')
        report['synchronized_word_values'] = synchronized_values.check(ast_path, ast_module, output/'synchronized-word-values')
        report['zero_word_register_effects'] = zero_instruction_rf.check(ast_path, ast_module, output/'zero-word-register-effects')
        report['guarded_register_preservation'] = zero_instruction_rf.check(ast_path, ast_module,
            output/'guarded-register-preservation', derive_condition=True)
        report['reference_register_obligations'] = zero_instruction_rf.check(ast_path, ast_module,
            output/'reference-register-obligations', derive_reference=True)
        report['register_lane_expressions'] = zero_instruction_rf.check(ast_path, ast_module,
            output/'register-lane-expressions', derive_slices=True)
        report['operand_address_origins'] = address_origins.check(ast_path, ast_module, output/'address-origins')
        if (report['destination_field_connections'].get('status')=='no_supported_rd_field'
                and report['operand_address_origins'].get('tagged_origins',{}).get('accepted') is True):
            report['tagged_destination_field_connections']=cpu_destination_field_connection.check(
                ast_path,ast_module,field_provider,output/'isa-destination-certificate',
                output/'tagged-destination-field-connections',
                tagged_provider=output/'address-origins'/'tagged')
        if report['operand_address_origins'].get('accepted'):
            report['captured_operand_addresses'] = capture_addresses.automatic(ast_path,ast_module,
                output/'captured-addresses',address_provider=output/'address-origins')
        else:
            report['captured_operand_addresses'] = dict(accepted=False,
                status='address_provider_unavailable',complete_R_generated=False)
        if report['captured_operand_addresses'].get('status')=='no_supported_capture_address_join':
            report['history_operand_addresses']=history_addresses.check(ast_path,ast_module,
                output/'history-addresses')
            if report['history_operand_addresses'].get('status')=='no_direct_word_address_cone':
                report['registered_operand_addresses']=registered_addresses.check(ast_path,ast_module,
                    output/'registered-addresses')
                if report['registered_operand_addresses'].get('connections')==0:
                    tagged_report=report['operand_address_origins'].get('tagged_origins',{})
                    if tagged_report and not tagged_report.get('accepted'):
                        report['tagged_captured_addresses']=dict(accepted=False,status='tagged_provider_unavailable')
                    else:
                        report['tagged_captured_addresses']=tagged_capture_addresses.check(ast_path,ast_module,
                            output/'tagged-capture-addresses',address_provider=(output/'address-origins'/'tagged'
                            if tagged_report.get('accepted') else None))
        if use_llm:
            report['llm_address_case_completion']=address_case_completion.run(
                [dict(name=ast_module,ast=str(ast_path),ast_module=ast_module)],
                output/'llm-address-cases',key=key)
            report['llm_field_selector_gaps'] = field_selector_gap.run(ast_path, ast_module,
                output/'llm-field-selector-gaps', key)
            report['llm_register_write_gaps'] = write_strategy.run(ast_path, ast_module,
                output/'llm-register-write-gaps', key)
            report['llm_capture_gap_rules'] = validity_strategy.run(ast_path, ast_module,
                output/'llm-capture-gap-rules', key, check_proposals=True)
            report['llm_metadata_gap_rules'] = validity_strategy.run(ast_path, ast_module,
                output/'llm-metadata-gap-rules', key, metadata=True, check_proposals=True)
    report['seconds'] = time.monotonic()-started
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    for arg in ['ast', 'ast-module', 'output']: p.add_argument('--'+arg, required=True)
    p.add_argument('--use-llm', action='store_true')
    p.add_argument('--key-from-note', action='store_true')
    p.add_argument('--analysis-only', action='store_true')
    a = p.parse_args()
    key = roles.key_from_note() if a.key_from_note else os.environ.get('DASHSCOPE_API_KEY')
    result = run(a.ast, a.ast_module, a.output, a.use_llm, key, not a.analysis_only)
    print(json.dumps(result, indent=2))
    components_checked=(result.get('isa_input_certificate', {}).get('accepted')
        and result.get('decoded_address_connections', {}).get('accepted')
        and result.get('register_R_component', {}).get('accepted')
        and result.get('operand_clauses', {}).get('accepted')
        and result.get('operand_route_equations', {}).get('accepted')
        and result.get('operand_reference_requirements', {}).get('accepted')
        and result.get('computed_source_R_transfer', {}).get('accepted')
        and result.get('guarded_operand_requirements', {}).get('accepted')
        and (result.get('operand_branch_equations', {}).get('accepted')
             or result.get('operand_branch_equations', {}).get('status') == 'no_supported_branch')
        and (result.get('operand_capture_equations', {}).get('accepted')
             or result.get('operand_capture_equations', {}).get('status') == 'no_copy_storage_discovered_not_a_completeness_claim')
        and (result.get('operand_selector_equations', {}).get('accepted')
             or result.get('operand_selector_equations', {}).get('status') == 'no_supported_selector_not_a_completeness_claim')
        and (result.get('operand_selector_sources', {}).get('accepted')
             or result.get('operand_selector_sources', {}).get('status') == 'no_copy_edges_not_a_completeness_claim')
        and (result.get('operand_selector_metadata', {}).get('accepted')
             or result.get('operand_selector_metadata', {}).get('status') == 'no_supported_metadata_connection_not_a_completeness_claim'
             or (result.get('operand_selector_sources', {}).get('status') == 'no_copy_edges_not_a_completeness_claim'
                 and result.get('operand_selector_metadata', {}).get('status') == 'source_certificates_unavailable'))
        and (result.get('control_capture_producers', {}).get('accepted')
             or result.get('control_capture_producers', {}).get('status') == 'no_supported_control_producer_not_a_completeness_claim')
        and (result.get('control_capture_histories', {}).get('accepted')
             or result.get('control_capture_histories', {}).get('status') == 'no_control_storage_discovered_not_a_completeness_claim')
        and (result.get('control_capture_transforms', {}).get('accepted')
             or result.get('control_capture_transforms', {}).get('status') == 'no_transformed_capture_discovered_not_a_completeness_claim')
        and (result.get('synchronized_field_relations', {}).get('accepted')
             or result.get('synchronized_field_relations', {}).get('status') == 'no_synchronized_fields_discovered')
        and (result.get('narrow_field_histories', {}).get('accepted')
             or result.get('narrow_field_histories', {}).get('status') == 'no_narrow_field_transfer')
        and (result.get('field_chain_histories', {}).get('accepted')
             or result.get('field_chain_histories', {}).get('status') == 'no_internal_field_chain')
        and (result.get('capture_field_chains', {}).get('accepted')
             or result.get('capture_field_chains', {}).get('status') == 'no_capture_field_chain_connection')
        and (result.get('capture_chain_coverage', {}).get('accepted')
             or result.get('capture_chain_coverage', {}).get('status') in ['no_capture_field_chain_connection', 'incomplete_chain_validity'])
        and (result.get('word_field_copies', {}).get('accepted')
             or result.get('word_field_copies', {}).get('status') == 'no_word_field_copy_pair')
        and (result.get('field_selector_origins', {}).get('accepted')
             or result.get('field_selector_origins', {}).get('status') == 'no_supported_field_selector')
        and (result.get('projected_selector_origins', {}).get('accepted')
             or result.get('projected_selector_origins', {}).get('status') == 'no_supported_field_selector')
        and (result.get('blocking_residual_connections', {}).get('accepted')
             or result.get('blocking_residual_connections', {}).get('status') == 'no_matching_residuals_not_a_completeness_claim')
        and (result.get('write_address_histories', {}).get('accepted')
             or result.get('write_address_histories', {}).get('status') == 'no_write_address_history_match')
        and (result.get('selector_joint_relations', {}).get('accepted')
             or result.get('selector_joint_relations', {}).get('status') == 'unsupported_history_schema')
        and (result.get('nonzero_capture_histories', {}).get('accepted')
             or result.get('nonzero_capture_histories', {}).get('status') == 'unsupported_nonzero_capture')
        and (result.get('source_history_projections', {}).get('accepted')
             or result.get('source_history_projections', {}).get('status') in
                ('unsupported_source_history', 'no_source_history_projection_match'))
        and (result.get('synchronized_word_values', {}).get('accepted')
             or result.get('synchronized_word_values', {}).get('status') == 'unsupported_total_coupling')
        and (result.get('zero_word_register_effects', {}).get('accepted')
             or result.get('zero_word_register_effects', {}).get('status') == 'unsupported_zero_word_rf')
        and result.get('guarded_register_preservation', {}).get('accepted')
        and result.get('reference_register_obligations', {}).get('accepted')
        and result.get('register_lane_expressions', {}).get('accepted')
        and result.get('operand_address_origins', {}).get('all_discovered_addresses_covered'))
    raise SystemExit(exit_status(result,components_checked,a.analysis_only))
