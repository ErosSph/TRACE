"""Derive ADD admission/write coupling from the whole original controller.

The CDFG selects the actual producer control and its sequential capture. A
backward observation certificate preserves blocking read-after-write order;
checked LFP frames then connect the observation to the original Program.
No previously written CPU INV or claimed future correctness is an input.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_blocking_observation as observation
import cpu_captured_read_addresses as reads
import cpu_ready_rf_certificate as ready
import cpu_selector_sources as wires
import cpu_comb_scalar_bindings as comb
from cpu_cdfg_result_consumer import checked_graph
from cpu_hazard_capture_connection import checked
from cpu_certificate_acceptance import run_stage

rtl = observation.rtl


def verify_environment_paths(paths):
    folders = {r['directory'] for r in paths if r['namespace'] == 'GeneratedSeedBoot'}
    if len(folders) != 1:
        raise ValueError('one original seed/environment receipt required')
    plan = json.loads((Path(next(iter(folders))) / 'plan.json').read_text())
    hashes = plan['environment']['input_hashes']
    if not hashes:
        raise ValueError('empty environment provenance is not a checked original environment')
    for file, digest in hashes.items():
        if hashlib.sha256(Path(file).read_bytes()).hexdigest() != digest:
            raise ValueError('original seed/environment data changed: ' + file)
    return hashes


def reset_copy(expression):
    if not(expression.name == 'ECond' and expression.args[0].name == '1'
           and expression.args[1].name == expression.args[2].name == 'EVar'
           and expression.args[1].args[0].name == expression.args[2].args[0].name == '1'
           and expression.args[3] == rtl.Parser('(EConst 1 0)').complete()):
        raise ValueError('unsupported reset/capture expression; explicit rule required')
    return tuple(int(x.args[1].name) for x in expression.args[1:3])


def discover(raw, valid_plan, use_plan):
    data, _ = ready.discover(raw)
    first = {row['row']['binding']['first']['write'] for row in data['rows']}
    if len(first) != 1:
        raise ValueError('no unique youngest producer write port')
    producer = wires.trace(raw, 1, next(iter(first)))
    if producer['kind'] != 'sequential':
        raise ValueError('producer write port is not an actual sequential field')
    root = producer['terminal']
    scalar = next(s for s in observation.origin.pending.analyze(raw)['scalar_transitions'] if s['root'] == root)
    if scalar['width'] != 1 or scalar['process'] != valid_plan['process']:
        raise ValueError('write and valid do not have the same capture process')
    reset, incoming = reset_copy(rtl.Parser(scalar['next_expression']).complete())
    route = wires.trace(raw, 1, incoming)
    gate = valid_plan['control']
    if route['kind'] != 'computed' or route['process'] != gate['process']:
        raise ValueError('write and admission do not share one actual controller')
    proc = next(p for p in raw['processes'] if p['name'] == gate['process'])
    if proc['kind'] != 'Combinational':
        raise ValueError('controller is not combinational')
    cases = [c for cs in use_plan['decoders'].values() for c in cs if c['opcode'] == 51]
    resets = {c['reset'] for c in cases}
    if len(resets) != 1:
        raise ValueError('ADD decoder reset is not unique')
    control_reset = resets.pop()
    reset_routes = [wires.trace(raw, 1, x) for x in [reset, control_reset]]
    if any(r['kind'] != 'external' for r in reset_routes) or len({r['terminal'] for r in reset_routes}) != 1:
        raise ValueError('capture and decoder do not share the actual reset input')
    return dict(write=root, scalar=scalar, incoming=incoming, route=route,
                gate=gate['terminal'], process=proc['name'], reset=reset,
                control_reset=control_reset, reset_routes=reset_routes)


def graph_evidence(graph, raw, plan):
    """Bind BOTH controller outputs and the real NBA field, including guards."""
    from cpu_pyslang_cdfg import dependencies, backward_slice
    from cpu_result_companions import capture_graph_evidence
    by_root = {s['coq_root']: s for s in graph['symbols']}
    by_path = {s['path']: s for s in graph['symbols']}
    outputs = [by_root[plan[k]] for k in ['gate', 'write']]
    # The actual write bit is sequential; follow its proven incoming route to
    # the controller, never treat the sequential current value as its input.
    outputs[1] = by_root[plan['route']['terminal']]
    groups = [set(e['process'] for e in graph['edges'] if e['target'] == s['path']) for s in outputs]
    if len(groups[0]) != 1 or groups[0] != groups[1]:
        raise ValueError('graph control outputs do not share one ordered process')
    pid = next(iter(groups[0]))
    edges = [e for e in graph['edges'] if e['process'] == pid]
    proc = next(p for p in raw['processes'] if p['name'] == plan['process'])
    if any(e['assignment'] != 'blocking' for e in edges):
        raise ValueError('controller graph is not blocking')
    if {by_path[e['target']]['coq_root'] for e in edges} != set(proc['writers']):
        raise ValueError('controller graph/AST write identity mismatch')
    gd = {(by_path[p]['width'], by_path[p]['coq_root']) for e in edges for p in dependencies(e)}
    cd = observation.inputs(proc['body'])
    if gd != cd:
        raise ValueError('controller data/guard dependency or width mismatch')
    capture = capture_graph_evidence(graph, raw, [dict(plan['scalar'], recipe=plan['scalar']['next_expression'])])
    return dict(controller_process=pid, ordered_edges=[e['id'] for e in edges],
                complete_dependencies=sorted(gd), capture=capture,
                queries=[backward_slice(graph, s['path']) for s in outputs],
                translation_equivalence_proved=False)


def render(config, raw, profile, plan, vp, up):
    proc = next(p for p in raw['processes'] if p['name'] == plan['process'])
    gate, write = plan['gate'], plan['route']['terminal']
    post_expr = rtl.Parser(f'(ECond 1 (EVar 1 {gate}) (EVar 1 {write}) (EConst 1 1))').complete()
    compiler = observation.Compiler(1)
    last = compiler.compile(proc['body'], rtl.render(post_expr), observation.inputs(post_expr))
    p, am = profile['ast']['program'], raw['module']
    index = [p['name'] for p in raw['processes'] if p['kind'] == 'Combinational'].index(proc['name'])
    header = f'''From Coq Require Import List ZArith Bool.
Require Import {config['ast_module']} Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects
 Lang.ExtendedSVBlocking Lang.ExtendedSVSequentialSubstitution Lang.ExtendedSVProjectionConnection
 Lang.ExtendedSVExprAgreement Lang.ExtendedSVBlockingObservation Lang.ExtendedSVExpressionObservation
 Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory Lang.ExtendedSVStallFlush
 Lang.ExtendedSVExpressionPath Ex.External.CPUInstructionFields
 Ex.External.CPUISAAddControlFields.
Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVBlocking
 ExtendedSVSequentialSubstitution ExtendedSVProjectionConnection ExtendedSVExprAgreement
 ExtendedSVBlockingObservation ExtendedSVExpressionObservation ExtendedSVWordInvariant
 ExtendedSVScalarHistory ExtendedSVStallFlush ExtendedSVExpressionPath CPUInstructionFields CPUISAAddControlFields.
'''
    source = header + 'Module Controller.\n' + '\n'.join(compiler.lines) + f'''
Definition post_observation:Expr:={rtl.render(post_expr)}.
Lemma original_blocking:blocking_onlyb(process_body {am}.{proc['name']})=true.
Proof. vm_compute;reflexivity. Qed.
Lemma compiled:compile_effect(statement_fuel {p})(process_body {am}.{proc['name']})=Some {last[0]}.
Proof. vm_compute;reflexivity. Qed.
Lemma process_observation s:norm 1(eval_expr(run_process {p} s {am}.{proc['name']})post_observation)=
 norm 1(eval_expr s {last[1]}).
Proof. exact(actual_process_expression {p} {am}.{proc['name']} {last[0]} 1 post_observation {last[1]}
 original_blocking compiled {last[2]} s). Qed.
Definition original_combs:=filter is_comb(processes {p}).
Lemma registered:nth_error original_combs {index}=Some {am}.{proc['name']}.
Proof. vm_compute;reflexivity. Qed.
Lemma connected:observation_bindingb original_combs {index} post_observation {last[1]}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem lfp_observation seed fixed:CombLFP {p} seed fixed ->
 norm 1(eval_expr fixed post_observation)=norm 1(eval_expr fixed {last[1]}).
Proof. exact(checked_observation_binding {p} original_combs {index} {am}.{proc['name']}
 1 post_observation {last[1]} seed fixed eq_refl registered process_observation connected). Qed.
Theorem add_enabled_write seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {plan['control_reset']})=1%Z ->
'''
    # Find the three ISA decode fields by ORIGINAL expression layout, not name.
    candidates = {(w, r) for w, r in observation.inputs(proc['body']) if w in [3, 7]}
    field_data, _, _, _ = reads.origins.render(config['ast'], config['ast_module'], candidates)
    fields = []
    for row in field_data['origins']:
        field = reads.fields.match_field(reads.strip_identity_extensions(rtl.Parser(row['expanded']).complete()), row['width'])
        if field and field['field'] in ['Opcode', 'Funct3', 'Funct7']:
            fields.append(dict(row, field=field['field']))
    if len(fields) != 3 or {r['field'] for r in fields} != {'Opcode', 'Funct3', 'Funct7'} or len({r['source'] for r in fields}) != 1:
        raise ValueError('no unambiguous common-word ADD control-field binding')
    values = dict(Opcode=51, Funct3=0, Funct7=0)
    for row in fields:
        source += f" norm {row['width']}(read_signal fixed {row['root']})={values[row['field']]}%Z ->\n"
    source += f''' norm 1(read_signal fixed {gate})=1%Z ->norm 1(read_signal fixed {write})=1%Z.
Proof. intros HL HR {' '.join('H'+r['field'] for r in fields)} HG.
 pose proof(lfp_observation seed fixed HL)as HO.
 unfold post_observation in HO;cbn[eval_expr]in HO;rewrite HG in HO.
 assert(HB:norm 1(eval_expr fixed {last[1]})=1%Z).
 {{ let e:=eval cbv in {last[1]} in change(norm 1(eval_expr fixed e)=1%Z).
    cbn[eval_expr];rewrite HR,{','.join('H'+r['field'] for r in fields)}.
    repeat match goal with |- context[if ?b then _ else _]=>destruct b eqn:?;try discriminate end;reflexivity. }}
 change(norm 1(norm 1(norm 1(read_signal fixed {write})))=norm 1(eval_expr fixed {last[1]}))in HO.
 repeat rewrite norm_idempotent in HO;exact(eq_trans HO HB). Qed.
End Controller.
'''
    requested = {(r['width'], r['root']) for r in fields}
    fd, fs, _, _ = reads.origins.render(config['ast'], config['ast_module'], requested)
    if fd['residuals']:
        raise ValueError('control field connection has unresolved dependencies')
    _, residuals, _, ss, _ = observation.origin.expressions.proposal(profile, {plan['write']})
    if residuals:
        raise ValueError('write capture is not proved by actual scalar rules')
    roots = {e['root'] for route in [plan['route']] + plan['reset_routes'] for e in route['edges']}
    _, wp, ws = comb.proposal(profile, roots)
    if wp['residuals']:
        raise ValueError('control/reset aliases are unproved')
    ports = {row['output_root']: i for i, row in enumerate(wp['ports'])}
    source += 'Module Fields.\n' + fs + '\nEnd Fields.\nModule Capture.\n' + ss + '\nEnd Capture.\nModule Wires.\n' + ws + '\nEnd Wires.\n'
    source += f'''Require Import GeneratedReadyCapture.ReadyCapture GeneratedCapturedReads.CapturedReadAddresses
 GeneratedValidGate.ValidGate.
Import Lang.ExtendedSVCaptureBirth.ExtendedSVCaptureBirth.
Local Opaque {p} PhaseSemantics.
'''
    exports = ['Controller.process_observation', 'Controller.lfp_observation', 'Controller.add_enabled_write']
    for row in fields:
        x, w, carrier, field = row['root'], row['width'], row['source'], row['field']
        source += f'''Lemma field_{x}_layout code:Fields.address_{x}_reference code=field_reference code {field}.
Proof. let e:=eval cbv in Fields.address_{x}_expanded in
 change(norm {w}(eval_expr(write_signal [] {carrier} code)e)=field_reference code {field}).
 pose proof(native_field_reference(write_signal [] {carrier} code){carrier} {field})as HF.
 unfold field_expr in HF;cbn[field_width field_offset eval_expr]in HF.
 cbn[eval_expr];repeat rewrite norm_idempotent in *;rewrite read_signal_write_same in *;exact HF. Qed.
'''
    source += f'''Theorem original_add_enabled_write seed fixed code rd rs1 rs2:
 CombLFP {p} seed fixed ->
 norm 32(read_signal fixed {fields[0]['source']})=norm 32 code ->
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 norm 1(read_signal fixed {plan['control_reset']})=1%Z ->norm 1(read_signal fixed {gate})=1%Z ->
 norm 1(read_signal fixed {write})=1%Z.
Proof. intros HL HW HD HR HG;destruct(original_decode_add_fields code rd rs1 rs2 HD)as[HO[H3 H7]].
 apply(Controller.add_enabled_write seed fixed HL HR).
'''
    for row in fields:
        h = dict(Opcode='HO', Funct3='H3', Funct7='H7')[row['field']]
        source += f" - exact(eq_trans(Fields.address_{row['root']}_instruction seed fixed code HL HW)(eq_trans(field_{row['root']}_layout code){h})).\n"
    source += ' - exact HG. Qed.\n'
    exports.append('original_add_enabled_write')
    sample = f'(phase_driven_state {p} ev pre)'
    post = f'(PhaseSemantics {p} ev pre)'
    # Every alias remains a kernel-checked original-LFP equality.
    for root, i in ports.items():
        row = wp['ports'][i]
        if row['rhs'].name != 'EVar' or row['rhs'].args[0].name != '1':
            raise ValueError('one-bit alias required')
        parent = row['rhs'].args[1].name
        source += f'''Lemma wire_{root} seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {root})=norm 1(read_signal fixed {parent}).
Proof. intro HL;rewrite(Wires.port_{i}_lfp seed fixed HL);unfold Wires.port_{i}_rhs;
 cbn[eval_expr];apply norm_idempotent. Qed.
'''
    def route_term(route):
        term = 'eq_refl'
        for edge in reversed(route['edges']):
            term = f"(eq_trans(wire_{edge['root']} seed _ HL){term})"
        return term
    cap_reset, dec_reset = map(route_term, plan['reset_routes'])
    source += f'''Lemma actual_capture_reset ev pre:
 changed_signal ev<>{vp['valid']}%nat ->
 process_matches_states pre {sample}{am}.{vp['process']}=true ->
 norm 1(read_signal {post}{vp['valid']})<>0%Z ->
 norm 1(read_signal {sample}{plan['reset']})=1%Z.
Proof. intros HX HM HV.
 pose proof(GeneratedValidGate.ValidGate.S.root_{vp['valid']}_expression_phase ev pre HX)as HP.
 rewrite HM in HP;unfold GeneratedValidGate.ValidGate.S.root_{vp['valid']}_expression in HP;
 cbn[eval_expr]in HP;rewrite norm_idempotent in HP.
 destruct(one_bit_cases {sample}{plan['reset']})as[HZ|HZ];[rewrite HZ in HP;contradiction HV;exact HP|exact HZ]. Qed.
Theorem actual_add_capture_write seed ev pre code rd rs1 rs2:
 CombLFP {p} seed {sample} ->
 changed_signal ev<>{vp['valid']}%nat ->changed_signal ev<>{plan['write']}%nat ->
 process_matches_states pre {sample}{am}.{vp['process']}=true ->
 norm 1(read_signal {post}{vp['valid']})<>0%Z ->
 norm 32(read_signal {sample}{fields[0]['source']})=norm 32 code ->
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 norm 1(read_signal {post}{plan['write']})=1%Z.
Proof. intros HL HX HWX HM HV HCode HD.
 pose proof(actual_capture_reset ev pre HX HM HV)as HR.
 assert(HG:norm 1(read_signal {sample}{gate})=1%Z).
 {{ destruct(one_bit_cases {sample}{gate})as[HZ|HZ];[|exact HZ].
    exfalso;apply HV;exact(GeneratedValidGate.ValidGate.blocked_actual_capture seed ev pre HL HX HM HZ). }}
 assert(HDR:norm 1(read_signal {sample}{plan['control_reset']})=1%Z).
 {{ exact(eq_trans {dec_reset}(eq_trans(eq_sym {cap_reset})HR)). }}
 pose proof(original_add_enabled_write seed _ code rd rs1 rs2 HL HCode HD HDR HG)as HW.
 pose proof {route_term(plan['route'])} as HI.
 pose proof(Capture.root_{plan['write']}_expression_phase ev pre HWX)as HP.
 rewrite HM in HP.
 assert(HPath:PathHolds {sample} Capture.root_{plan['write']}_expression[true]).
 {{ change(Z.eqb(norm 1(read_signal {sample}{plan['reset']}))0%Z=false /\\True).
    rewrite HR;split;[reflexivity|exact I]. }}
 pose proof(selected_expression_sound 1 [true] Capture.root_{plan['write']}_expression
   (EVar 1 {plan['incoming']}){sample} eq_refl HPath)as HS.
 exact(eq_trans HP(eq_trans HS(eq_trans(norm_idempotent 1(read_signal {sample}{plan['incoming']}))(eq_trans HI HW)))). Qed.
'''
    exports += ['actual_capture_reset', 'actual_add_capture_write']
    source += f'''Theorem actual_admitted_add_write image events ev token rd rs1 rs2:
 let pre:=phase_run {p} events(GeneratedCapturedReads.CapturedReadAddresses.H.F.boot image)in
 Forall GeneratedCapturedReads.CapturedReadAddresses.H.W.Environment events ->
 GeneratedCapturedReads.CapturedReadAddresses.H.W.Environment ev ->
 current(fst(GeneratedCapturedReads.CapturedReadAddresses.H.boot_history image events))=Some token ->
 changed_signal ev<>{vp['valid']}%nat ->changed_signal ev<>{plan['write']}%nat ->
 process_matches_states pre {sample}{am}.{vp['process']}=true ->
 norm 1(read_signal {post}{vp['valid']})<>0%Z ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 norm 1(read_signal {post}{plan['write']})=1%Z.
Proof. intros pre HE HEv HT HX HWX HM HV HD.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(GeneratedReadyCapture.ReadyCapture.active_reset image events ev HE HEv HX HM HV)as HR;fold pre in HR.
 assert(HG:norm 1(read_signal {sample}{gate})=1%Z).
 {{ destruct(one_bit_cases {sample}{gate})as[HZ|HZ];[|exact HZ].
    exfalso;apply HV;exact(GeneratedValidGate.ValidGate.blocked_actual_capture seed ev pre HL HX HM HZ). }}
 assert(HDR:norm 1(read_signal {sample}{plan['control_reset']})=1%Z).
 {{ exact(eq_trans {dec_reset}(eq_trans(eq_sym {cap_reset})HR)). }}
 pose proof(original_add_enabled_write seed _ (token_word token)rd rs1 rs2 HL
 (GeneratedCapturedReads.CapturedReadAddresses.sampled_current_word image events ev token HE HEv HT)HD HDR HG)as HW.
 pose proof {route_term(plan['route'])} as HI.
 pose proof(Capture.root_{plan['write']}_expression_phase ev pre HWX)as HP.
 rewrite HM in HP.
 assert(HPath:PathHolds {sample} Capture.root_{plan['write']}_expression[true]).
 {{ change(Z.eqb(norm 1(read_signal {sample}{plan['reset']}))0%Z=false /\\True).
    rewrite HR;split;[reflexivity|exact I]. }}
 pose proof(selected_expression_sound 1 [true] Capture.root_{plan['write']}_expression
   (EVar 1 {plan['incoming']}){sample} eq_refl HPath)as HS.
 exact(eq_trans HP(eq_trans HS(eq_trans(norm_idempotent 1(read_signal {sample}{plan['incoming']}))(eq_trans HI HW)))). Qed.
Goal True. idtac "ADMISSION_WRITE_AUDIT". exact I. Qed.
'''
    exports.append('actual_admitted_add_write')
    source += ''.join(f'Print Assumptions {x}.\n' for x in exports)
    plan.update(observation=rtl.render(post_expr), observation_dependencies=sorted(last[3]),
                observation_rules=compiler.serial, fields=fields, proof_count=len(exports))
    return source


def check(config, output):
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    raw, profile, paths = observation.origin.raw_binding(config['ast'], config['ast_module'])
    provider_paths = json.loads((Path(config['use']) / 'providers.json').read_text())
    valid = next(p['directory'] for p in provider_paths if p['namespace'] == 'GeneratedValidGate')
    vp = checked(valid, 'ValidGate', raw['source_sha256'])
    up = checked(config['use'], 'HazardSourceUse', raw['source_sha256'])
    environment_hashes = verify_environment_paths(json.loads((Path(config['history']) / 'plan.json').read_text())['paths'])
    cr = json.loads((Path(config['capture']) / 'report.json').read_text())
    if not(cr.get('accepted') and cr.get('coqc_exit') == cr.get('coqchk_exit') == 0
           and cr.get('assumptions_audit_passed') and cr.get('local_assumptions_closed')
           and hashlib.sha256((Path(config['capture']) / 'ReadyCapture.v').read_bytes()).hexdigest() == cr['source_sha256']
           and (Path(config['capture']) / 'ReadyCapture.vo').is_file()):
        raise ValueError('unchanged checked actual-capture provider required')
    if json.loads((Path(config['capture']) / 'plan.json').read_text())['ast_sha256'] != raw['source_sha256']:
        raise ValueError('capture provider has different original AST')
    plan = discover(raw, vp, up)
    graph = checked_graph(config['graph'], config['ast'], out / 'replayed')
    evidence = graph_evidence(graph, raw, plan)
    source = render(config, raw, profile, plan, vp, up)
    plan['ast_sha256'] = raw['source_sha256']
    (out / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    (out / 'graph-evidence.json').write_text(json.dumps(evidence, indent=2) + '\n')
    path = out / 'AdmissionWrite.v'
    path.write_text(source)
    flags = list(rtl.framework.FLAGS)
    dependencies = json.loads((Path(config['history']) / 'plan.json').read_text())['paths'] + provider_paths
    for key, namespace in [('selectors', 'GeneratedReadySelector'), ('ready_data', 'GeneratedReadyData'),
                           ('ready_rf', 'GeneratedReadyRF'), ('current_fields', 'GeneratedCurrentControlFields'),
                           ('use', 'GeneratedHazardSourceUse'), ('reader', 'GeneratedCapturedReads'),
                           ('operands', 'GeneratedResultCompanions'), ('capture', 'GeneratedReadyCapture')]:
        dependencies.append(dict(directory=str(Path(config[key]).resolve()), namespace=namespace))
    for row in dependencies:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedAdmissionWrite']
    (out / 'providers.json').write_text(json.dumps(dependencies, indent=2) + '\n')
    start = time.monotonic()
    c, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
                          str(observation.origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(path.resolve())],
                         out / 'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=c.returncode, coqc_timed_out=timed,
                  source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  ast_sha256=raw['source_sha256'], old_inv_read=False, llm_calls=0,
                  complete_R_generated=False, infinite_itree_refinement_proved=False,
                  valid_add_implies_actual_write_proved=False,
                  caller_write_enable_assumption_eliminated=False,
                  controller_read_after_write_preserved=True, graph_queries=2,
                  proof_count=plan['proof_count'], original_environment_input_hashes=environment_hashes)
    if c.returncode == 0:
        audit = c.stdout.split('ADMISSION_WRITE_AUDIT')[-1]
        closed = audit.count('Closed under the global context') == plan['proof_count'] and 'Axioms:' not in audit
        k, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
                              str(observation.origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags,
                              '-norec', 'GeneratedAdmissionWrite.AdmissionWrite'], out / 'coqchk.log',
                             max(.1, 1200 - (time.monotonic() - start)))
        accepted = closed and k.returncode == 0
        report.update(coqchk_exit=k.returncode, coqchk_timed_out=timed, assumptions_closed=closed,
                      accepted=accepted, valid_add_implies_actual_write_proved=accepted,
                      caller_write_enable_assumption_eliminated=accepted)
    report['seconds'] = time.monotonic() - start
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inputs', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    try:
        result = check(json.loads(Path(args.inputs).read_text()), args.output)
    except Exception as error:
        directory = Path(args.output)
        if directory.is_dir() and not(directory / 'report.json').exists():
            (directory / 'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight',
                error_type=type(error).__name__, error=str(error), cli_exit=1,
                complete_R_generated=False, infinite_itree_refinement_proved=False), indent=2) + '\n')
        raise
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
