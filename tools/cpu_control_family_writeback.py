"""Generate real ADD/ADDI/JAL RF writeback for the same three-class Current.

Reuses the physical bank/destination rules, not the old whole-CPU invariant.
The original reference initial-state alignment is propagated along its actual
retired execution chain; no independent JAL operand/target correctness is assumed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_joint as family
import cpu_add_family_writeback as old
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

NS = 'GeneratedControlFamilyWriteback'
J = 'GeneratedControlFamilyJoint.ControlFamilyJoint'
P = 'GeneratedJalProducerControls.JalProducerControls'


def once(source, a, b):
    if source.count(a) != 1:raise ValueError('writeback template mismatch: ' + a[:100])
    return source.replace(a, b)


def render(c, raw, profile, plan, selector):
    source, exports = old.render(c, raw, profile, plan, selector)
    source = source.replace('GeneratedAddFamilyJoint.AddFamilyJoint', J)
    # The normalized Current3 exports its relations/theorems, not copied private
    # module aliases. Bind every physical dependency to its checked provider.
    for short, target in [('H', 'GeneratedCapturedHistoryBoot.CapturedHistoryBoot'),
            ('C', 'GeneratedCapturedHistoryBoot.CapturedHistoryBoot.C'),
            ('Q', 'GeneratedPhasePendingCommit.PhasePendingCommit'),
            ('V', 'GeneratedValidResult.ValidResult')]:
        source = once(source, 'Module ' + short + ':=J.' + short + '.', 'Module ' + short + ':=' + target + '.')
    source = source.replace('J.O.', 'GeneratedOperandResultJoint.OperandResultJoint.')
    source = source.replace('Module F:=CPUISAAddFamilyReferenceValues.', 'Module F:=CPUISAControlFamilyReferenceValues.\n'
        'Local Notation reference_pc := GeneratedFetchReference.FetchReference.recorded_pc.')
    source = once(source, 'GeneratedAddiReadyControls.AddiReadyControls.\nImport ListNotations',
        'GeneratedAddiReadyControls.AddiReadyControls GeneratedJalProducerControls.JalProducerControls\n'
        ' GeneratedJalLinkPhase.JalLinkPhase GeneratedFetchReference.FetchReference\n'
        ' Ex.External.CPUISAControlFamilyReferenceValues Ex.External.CPUISAJalEffects Ex.External.CPUISAJalSuccessEffects.\nImport ListNotations')
    source = once(source, '{word_ok:word.ok word}{registers_ok:map.ok Registers}.',
        '{word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.')
    source = source.replace('(reference_pc:Token->Z)', ' ')
    for name in ['J.Current', 'J.OperandClause', 'J.ResultJoint', 'J.actual_result_phase',
                 'operand_clause_idle', 'actual_family_writeback_restores_RF']:
        source = source.replace(name + ' reference_pc ', name + ' ')
    source = source.replace('Theorem operand_clause_idle reference_pc ', 'Theorem operand_clause_idle ')
    source = once(source, 'destruct HProjection as[HAdd|HAddi].',
        'destruct HProjection as[HAdd|[HAddi|HJal]].')
    source = once(source, ' - right;destruct HAddi', ' - right;left;destruct HAddi')
    marker = '\nQed.\n\nTheorem actual_family_writeback_restores_RF'
    source = once(source, marker, '\n - right;right;exact HJal.' + marker)
    endpoint, result, data = selector['endpoint'], selector['result'], selector['write_data']
    valid = plan['writeback_valid']
    p = profile['ast']['program'];sample = f'(phase_driven_state {p} ev pre)'
    helper = f'''Theorem jal_selects_alu image events token rd imm:
 let pre:=phase_run {p} events(H.F.boot image)in
 Forall H.W.Environment events ->norm 1(read_signal pre {valid}%nat)<>0%Z ->
 C.C.chain_tag2(snd(H.boot_history image events))=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 norm 1(read_signal pre {endpoint})=0%Z.
Proof. intros pre HE HV HT HD;exact(proj2({P}.actual_jal_producer_controls_2 image events token rd imm HE HV HT HD)). Qed.
'''
    data_block = re.search(r'Theorem actual_addi_write_data\b.*?Qed\.', source, re.S).group(0)
    data_block = data_block.replace('actual_addi_write_data', 'actual_jal_write_data')
    data_block = data_block.replace('token rd rs imm:', 'token rd imm:')
    data_block = data_block.replace('Decode.Addi rd rs imm', 'Decode.Jal rd imm')
    data_block = data_block.replace('Forall H.W.Environment events ->H.W.Environment ev ->',
        f'Forall H.W.Environment events ->H.W.Environment ev ->norm 1(read_signal pre {valid}%nat)<>0%Z ->')
    data_block = data_block.replace('intros pre HE HEv HT HD;', 'intros pre HE HEv HV HT HD;')
    data_block = data_block.replace('addi_selects_alu image events token rd rs imm HE HT HD',
        'jal_selects_alu image events token rd imm HE HV HT HD')
    source = once(source, 'Section ISA.', helper + data_block + '\nSection ISA.')
    source = once(source,
        f'F.computed_value token_word token before=Some(norm 32(read_signal pre {result})) ->\n FormalSpec.run1',
        f'F.computed_value token_word token before=Some(norm 32(read_signal pre {result})) ->\n'
        ' CPUISAJalEffects.NextPCAligned before ->\n FormalSpec.run1')
    source = once(source, ' HR HValue.\n destruct(CPUReferenceAddFamilyProducers.computed_value_implies_family',
        ' HR HValue HAligned.\n destruct(F.computed_value_implies_family')
    source = once(source, 'as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].',
        'as[[rd[rs1[rs2 HD]]]|[[rd[rs[imm HD]]]|[rd[imm HD]]]].')
    source = source.replace('unfold F.computed_value in HValue;',
        'unfold F.computed_value,CPUISAAddFamilyReferenceValues.computed_value in HValue;')
    write = selector['write']
    guards = [f'Z.eqb(eval_expr {sample}{g})0%Z={str(not taken).lower()}' for g, taken in write['guards']]
    gs = ' '.join('HG' + str(i) for i in range(len(guards)))
    new_branch = f''' - destruct(Destination.actual_write_destination_from_boot image events ev HE HEv HP {gs})as[actual[HActual HOperations]].
   assert(actual=token)by congruence;subst actual.
   specialize(HOperations(Decode.Jal rd imm)rd [] HD eq_refl).
   pose proof(V.actual_write_is_valid image events ev HE HEv HG{len(guards)-1})as HV.
   pose proof(actual_jal_write_data image events ev token rd imm HE HEv HV HT HD)as HData;fold pre in HData,HOperations.
   pose proof(CPUISAJalSuccessEffects.original_token_jal_effect reference_pc token_word token before after rd imm HSTEP HD)as HOriginal.
   rewrite(F.computed_jal token_word token before rd imm HD)in HValue;injection HValue as HValue.
   unfold CPUISAJalEffects.NextPCAligned,CPUISAJalEffects.link in HAligned;rewrite HAligned in HValue.
   split;[exact(proj2(proj2(instruction_effect_sound reference_pc token_word token before after HSTEP)))|].
   apply(actual_phase_register_transport {p} {write['bank']} {write['total']} Bank.bank_{write['bank']}_entries Bank.bank_{write['bank']}_certificate ev pre before after
    (R.protect_bank ev HEv)HR).
   rewrite HOperations;apply(register_operations_as_lane before after rd(word.add(getPc before)(word.of_Z 4))_HOriginal).
   cbn[eval_expr];rewrite !norm_idempotent;exact(eq_trans HData(eq_sym HValue)).
'''.replace(')_HOriginal', ') _ HOriginal')
    marker = '\nQed.\n\nTheorem actual_family_write_preserves_Current'
    source = once(source, marker, '\n' + new_branch + marker)
    source = once(source, ' J.Current initial retired current pre(H.boot_history image events) ->',
        ' CPUISAJalEffects.NextPCAligned initial ->\n J.Current initial retired current pre(H.boot_history image events) ->')
    source = once(source, gs + ' HCurrent.\n', gs + ' HInitial HCurrent.\n')
    source = once(source, ' HR HValue)as[HRun HRNext].',
        ' HR HValue(GeneratedJalLinkPhase.JalLinkPhase.effect_chain_next_pc_aligned initial retired current HInitial HC))as[HRun HRNext].')
    source = once(source, ' image events ev HE HEv HN HOp).',
        ' image events ev HE HEv HN HInitial HOp).')
    source = source.replace('FAMILY_WRITEBACK_AUDIT', 'CONTROL_FAMILY_WRITEBACK_AUDIT')
    exports += ['jal_selects_alu', 'actual_jal_write_data']
    source += 'Print Assumptions jal_selects_alu.\nPrint Assumptions actual_jal_write_data.\n'
    return source, exports


def inline_aliases(source):
    pattern = re.compile(r'\bModule\s+([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*'
                         r'([A-Za-z_][A-Za-z0-9_.]*)\s*\.\s*')
    aliases = dict(pattern.findall(source))
    if set(aliases) != {'J','H','C','Q','V','F','S','R','Destination','Bank'}:
        raise ValueError('unexpected writeback alias set')
    name = re.compile(r'(?<![A-Za-z0-9_.])('+'|'.join(aliases)+r')\.(?=[A-Za-z_])')
    normalized = name.sub(lambda m:aliases[m.group(1)]+'.',pattern.sub('',source))
    return normalized, aliases


def check(c, current, controls, output, after_timeout=None, prior_seconds=0):
    raw, profile, _ = family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'], c['ast_module'])
    plan = family.discover(c, raw);paths = [];receipts = []
    for folder, stem, namespace in [(current, 'ControlFamilyJoint', 'GeneratedControlFamilyJoint'),
            (controls, 'JalProducerControls', 'GeneratedJalProducerControls'),
            (c['addi_ready'], 'AddiReadyControls', 'GeneratedAddiReadyControls')]:
        folder = Path(folder)
        if stem == 'JalProducerControls':
            # This older receipt lacks the redundant flat audit Boolean.
            # Validate its actual main/type/kernel facts without rewriting it.
            report = json.loads((folder / 'report.json').read_text())
            audit = report.get('exact_type_audit', {})
            if not(report.get('accepted') and report.get('coqc_exit') == report.get('coqchk_exit') == 0
                   and audit.get('accepted') and audit.get('coqc_exit') == audit.get('coqchk_exit') == 0
                   and report.get('assumptions') == [] and audit.get('assumptions') == []
                   and audit.get('expected_explicit_mappings') == 27
                   and hashlib.sha256((folder / (stem + '.v')).read_bytes()).hexdigest() == report['source_sha256']):
                raise ValueError('checked JAL producer controls and all 27 original types required')
        else:report = verified(folder, stem)
        if report['ast_sha256'] != raw['source_sha256'] or report.get('old_inv_read') is not False:
            raise ValueError('same original physical runtime required')
        object_sha = hashlib.sha256((folder / (stem + '.vo')).read_bytes()).hexdigest()
        if 'object_sha256' in report and object_sha != report['object_sha256']:
            raise ValueError('changed accepted provider object')
        paths += json.loads((folder / 'providers.json').read_text())
        paths += [dict(namespace=namespace, directory=str(folder.resolve()))]
        receipts += [dict(namespace=namespace, source_sha256=report['source_sha256'], object_sha256=object_sha,
            upstream_object_hash_recorded='object_sha256' in report,
            dependency_policy='original source receipt plus native Coq imported-library digest; consumer pins observed object hash')]
    bindings = {}
    for row in paths:
        if row['namespace'] in bindings and bindings[row['namespace']] != row['directory']:
            raise ValueError('conflicting actual writeback provider')
        bindings[row['namespace']] = row['directory']
    paths = [dict(namespace=n, directory=d) for n, d in bindings.items()]
    selector = json.loads((Path(bindings['GeneratedWritebackSelector']) / 'plan.json').read_text())
    pending = json.loads((Path(plan['queue_context']) / 'plan.json').read_text())
    indexes = [i for i, node in enumerate(pending['nodes'][:-1]) if node['index'] == plan['head']['index'] and node['process'] == plan['head']['process']]
    if len(indexes) != 1:raise ValueError('ambiguous actual EX capture-idle rule')
    plan['capture_idle_index'] = indexes[0]
    valids = [node['valid'] for node in pending['nodes'] if node['index'] == 2]
    if len(valids) != 1:raise ValueError('ambiguous actual WB valid bit')
    plan['writeback_valid'] = valids[0]
    source, exports = render(c, raw, profile, plan, selector)
    out = Path(output).resolve();out.mkdir(parents=True, exist_ok=False)
    evidence = None
    if after_timeout:
        prior=Path(after_timeout);previous=json.loads((prior/'report.json').read_text())
        original=(prior/'ControlFamilyWriteback.v').read_text()
        if not(previous['seconds']>=1200 and previous.get('coqchk_timed_out')
               and not previous.get('performance_attempt') and original==source
               and hashlib.sha256(source.encode()).hexdigest()==previous['source_sha256']):
            raise ValueError('same-source actual first timeout required')
        source, aliases=inline_aliases(source)
        evidence=dict(original_source_sha256=hashlib.sha256(original.encode()).hexdigest(),
            new_source_sha256=hashlib.sha256(source.encode()).hexdigest(),alias_mapping=aliases,
            normalized_full_source_exact_equal=True)
        (out/'same-target-alias-normalization.json').write_text(json.dumps(evidence,indent=2)+'\n')
    target = out / 'ControlFamilyWriteback.v';target.write_text(source)
    for name, data in [('providers', paths), ('receipts', receipts), ('plan', dict(operands=plan, selector=selector)), ('exports', exports)]:
        (out / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    flags = list(family.derived.rtl.framework.FLAGS)
    for row in paths:flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out), NS]
    root = family.derived.controls.history.admission.observation.origin.ROOT
    if prior_seconds >= 1200:raise ValueError('same-point native budget exhausted')
    start = time.monotonic();remaining = lambda: max(.1, 1200 - prior_seconds - (time.monotonic() - start))
    def stage(name, command):
        return run_stage(['/usr/bin/time', '-v', '-o', str(out / (name + '.resources')), *command], out / (name + '.log'), remaining())
    cc, ct = stage('coqc', [str(root / '_opam/bin/coqc'), '-time', *flags, str(target)])
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=ct,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'],
        old_inv_read=False, actual_three_class_RF_write_restores_same_Current=False,
        target_alignment_or_correct_writeback_assumed=False, external_llm_api_calls=0,
        complete_R_generated=False, full_cycle_preserved=False, infinite_itree_refinement_proved=False,
        performance_attempt=1 if after_timeout else 0, actual_timeout_evidence=after_timeout,
        unchanged_normalized_original_source=evidence is not None)
    if cc.returncode == 0:
        axioms = audit_all_exports(cc.stdout.split('CONTROL_FAMILY_WRITEBACK_AUDIT')[-1], len(exports))
        baseline = out / 'Baseline.v';baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\nGoal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\nPrint Assumptions CPUISAInstructionExecution.token_execute.\n')
        bc, bt = stage('baseline', [str(root / '_opam/bin/coqc'), *flags, str(baseline)])
        allowed = parse_assumptions(bc.stdout) if bc.returncode == 0 else set()
        audit = source[:source.index('Lemma addi_load_zero')] + 'Require Import ' + NS + '.ControlFamilyWriteback.\n'
        args = ['code rd rs imm', 'image events token rd rs imm', 'image events ev token rd rs imm',
                'initial ledger image events ev', 'image events ev token before after',
                'initial retired current image events ev', 'image events token rd imm', 'image events ev token rd imm']
        # The final two physical helpers precede the ISA section in the source.
        ordered = [(exports[i], args[i]) for i in [0, 1, 2, 6, 7, 3, 4, 5]]
        for name, arguments in ordered:
            if name == 'operand_clause_idle':
                audit += source[source.index('Section ISA.'):source.index('Theorem operand_clause_idle')]
            declaration = re.search(r'(?:Lemma|Theorem) ' + name + r'\b.*?(?=\nProof\.)', source, re.S).group(0)
            audit += declaration.replace(name, 'exact_' + name, 1) + '\nProof. exact (' + NS + '.ControlFamilyWriteback.' + name + ' ' + arguments + '). Qed.\n'
        audit += 'End ISA.\nGoal True. idtac "CONTROL_WRITEBACK_TYPES". exact I. Qed.\n'
        audit += ''.join('Print Assumptions exact_' + name + '.\n' for name in exports)
        typefile = out / 'ExactTypes.v';typefile.write_text(audit)
        ac, at = stage('exact-types', [str(root / '_opam/bin/coqc'), '-time', *flags, str(typefile)])
        ta = audit_all_exports(ac.stdout.split('CONTROL_WRITEBACK_TYPES')[-1], len(exports)) if ac.returncode == 0 else set()
        kk, kt = stage('coqchk', [str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec', NS + '.ControlFamilyWriteback', '-norec', NS + '.ExactTypes']) if ac.returncode == 0 else (None, False)
        okay = bc.returncode == ac.returncode == 0 and kk is not None and kk.returncode == 0 and not(axioms - allowed) and not(ta - allowed) and not(allowed - ALLOWED_AXIOMS)
        report.update(accepted=okay, baseline_exit=bc.returncode, baseline_timed_out=bt, baseline_assumptions=sorted(allowed), assumptions=sorted(axioms),
            exact_types_exit=ac.returncode, exact_types_timed_out=at, exact_type_assumptions=sorted(ta),
            coqchk_exit=kk.returncode if kk is not None else None, coqchk_timed_out=kt, assumptions_audit_passed=okay,
            actual_three_class_RF_write_restores_same_Current=okay)
    report['seconds'] = time.monotonic() - start
    report['cumulative_seconds'] = report['seconds'] + prior_seconds
    if report['accepted']:report['object_sha256'] = hashlib.sha256(target.with_suffix('.vo').read_bytes()).hexdigest()
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n');return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__);parser.add_argument('--current', required=True)
    parser.add_argument('--controls', required=True);parser.add_argument('--output', required=True)
    parser.add_argument('--inline-aliases-after-timeout');parser.add_argument('--prior-seconds',type=float,default=0)
    args = parser.parse_args();config = family.inputs();config['addi_ready'] = 'results/r-addi-ready-controls-20261027-a10'
    try:result = check(config, args.current, args.controls, args.output,args.inline_aliases_after_timeout,args.prior_seconds)
    except Exception as error:
        out = Path(args.output);out.mkdir(parents=True, exist_ok=True)
        if not(out / 'report.json').exists():
            (out / 'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight_or_pipeline_exception',
                cli_exit=1, error=str(error)), indent=2) + '\n')
        raise
    print(json.dumps(result, indent=2));raise SystemExit(0 if result['accepted'] else 1)
