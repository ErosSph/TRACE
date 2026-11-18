"""Generate a separate ADD/ADDI/JAL data relation from checked physical roles.

The two-class accepted interface stays unchanged.  The reference PC is the
actual token recorder; JAL uses the original ISA next-PC, not a guessed PC+4.
This is a data/operand/result relation, not a claim of whole-cycle preservation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_joint as family
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

NS = 'GeneratedControlFamilyJoint'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('unsupported family syntax template: ' + old[:100])
    return source.replace(old, new)


def render(c, raw, profile, plan):
    source, _ = family.render(c, raw, profile, plan)
    source = replace_once(source, 'Ex.External.CPUISAAddFamilyReferenceValues ',
        'Ex.External.CPUISAAddFamilyReferenceValues Ex.External.CPUISAControlFamilyReferenceValues '
        'Ex.External.CPUISAJalEffects ')
    source = replace_once(source, 'GeneratedAddResult.AddResult GeneratedPhasePendingCommit.PhasePendingCommit.',
        'GeneratedAddResult.AddResult GeneratedPhasePendingCommit.PhasePendingCommit\n'
        ' GeneratedFetchReference.FetchReference GeneratedJalLinkPhase.JalLinkPhase\n'
        ' GeneratedAddFamilyInitial.AddFamilyInitial GeneratedLedgerInitial.LedgerInitial\n'
        ' GeneratedRegisterInitial.RegisterInitial.')
    source = replace_once(source, 'Module F:=CPUISAAddFamilyReferenceValues.',
        'Module F:=CPUISAControlFamilyReferenceValues.\n'
        'Local Notation reference_pc := GeneratedFetchReference.FetchReference.recorded_pc.')
    source = replace_once(source, '{word_ok:word.ok word}{registers_ok:map.ok Registers}.',
        '{word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.')
    source = source.replace('(reference_pc:Token->Z)', ' ')
    for name in ['OperandClause', 'ResultJoint', 'Current', 'head_from_operand_clause']:
        source = source.replace(name + ' reference_pc ', name + ' ')
    source = replace_once(source,
        'O.OperandProjection token pre before after \\/ I.OperandProjection token pre before after.',
        'O.OperandProjection token pre before after \\/ I.OperandProjection token pre before after \\/\n'
        ' (exists rd imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm)).')
    context = ('Forall H.W.Environment events ->H.W.Environment ev ->NoDup(map token_id ledger) ->\n'
               ' OperandClause initial ledger pre(H.boot_history image events) ->')
    if source.count(context) != 2:
        raise ValueError('head and phase must share exactly one alignment context each')
    source = source.replace(context,
        'Forall H.W.Environment events ->H.W.Environment ev ->NoDup(map token_id ledger) ->\n'
        ' CPUISAJalEffects.NextPCAligned initial ->\n'
        ' OperandClause initial ledger pre(H.boot_history image events) ->')
    source = replace_once(source, 'Proof. intros pre HE HEv HN HC HV token HT.',
        'Proof. intros pre HE HEv HN HInitial HC HV token HT.')
    source = replace_once(source, 'HLookup[HStep[HAdd|HAddi]]',
        'HLookup[HStep[HAdd|[HAddi|HJal]]]')
    source = replace_once(source,
        'exact(eq_trans(F.addi_at_cut reference_pc token_word token_id initial ledger index token before\n'
        '    rd rs imm x HN HBefore HD HX)(f_equal Some(eq_sym HResult))).\nQed.',
        'rewrite(F.at_cut reference_pc token_word token_id initial ledger index token before HN HBefore),\n'
        '    (F.computed_addi token_word token before rd rs imm x HD HX).\n'
        '   exact(f_equal Some(eq_sym HResult)).\n'
        ' - destruct HJal as[rd[imm HD]].\n'
        '   exact(GeneratedJalLinkPhase.JalLinkPhase.actual_jal_reference_link\n'
        '    initial ledger index token before after image events ev rd imm\n'
        '    HE HEv HN HBefore HInitial HStep HV HT HD).\nQed.')
    source = replace_once(source, 'Proof. intros pre HE HEv HN HO HJ;',
        'Proof. intros pre HE HEv HN HInitial HO HJ;')
    source = replace_once(source,
        '(head_from_operand_clause initial ledger image events ev HE HEv HN HO)',
        '(head_from_operand_clause initial ledger image events ev HE HEv HN HInitial HO)')
    li = 'GeneratedLedgerInitial.LedgerInitial'
    ri = 'GeneratedRegisterInitial.RegisterInitial'
    ni = 'GeneratedAddFamilyInitial.AddFamilyInitial'
    queue = json.loads((Path(plan['queue_context']) / 'plan.json').read_text())
    valids = {row['index']: row['valid'] for row in queue['nodes'] if row['index'] is not None}
    if set(valids) != {0, 1, 2}:
        raise ValueError('unrecognized actual reset stage coverage')
    roots = [plan['birth']['valid'], valids[0], valids[1], valids[2]]
    boot = f'''Theorem actual_boot_current image initial_imem:
 Current(FormalSpec.initial_state initial_imem)[](FormalSpec.initial_state initial_imem)
 (H.F.boot image)(H.boot_history image []).
Proof. constructor.
 - unfold ledger;cbn[app];rewrite {li}.actual_boot_pending_empty;constructor.
 - constructor.
 - rewrite({ri}.boot_bank_zero image);exact({ri}.zero_RF_initial initial_imem).
 - split.
   + rewrite {li}.actual_boot_history_empty;apply {ni}.empty_covered.
'''
    for root in roots:
        boot += f'     {{ exact(proj1(Forall_forall _ _)({li}.actual_boot_valids_zero image){root}%nat ltac:(cbn;tauto)). }}\n'
    boot += '   + split.\n'
    for root in [valids[1], valids[2]]:
        boot += f'''     * intro HV;exfalso;apply HV.
       exact(proj1(Forall_forall _ _)({li}.actual_boot_valids_zero image){root}%nat ltac:(cbn;tauto)).
'''
    boot += f''' - intro HV;exfalso;apply HV.
   exact(proj1(Forall_forall _ _)({li}.actual_boot_valids_zero image){plan['head']['valid']}%nat ltac:(cbn;tauto)).
 - exists(FormalSpec.initial_state initial_imem);rewrite {li}.actual_boot_pending_empty;constructor.
Qed.
'''
    source = replace_once(source, 'End ISA.\nGoal True.', boot + 'End ISA.\nGoal True.')
    source += 'Print Assumptions actual_boot_current.\n'
    source = source.replace('FAMILY_JOINT_AUDIT', 'CONTROL_FAMILY_JOINT_AUDIT')
    return source, ['sampled_add_controls', 'head_from_operand_clause', 'actual_result_phase', 'actual_boot_current']


def paths_for(c, link, raw):
    # A receipt must pin both the exact elaborated AST and proof object.
    paths = []
    receipts = []
    for folder, stem, namespace in [(link, 'JalLinkPhase', 'GeneratedJalLinkPhase'),
            (c['family_joint'], 'AddFamilyJoint', 'GeneratedAddFamilyJoint'),
            (c['family_initial'], 'AddFamilyInitial', 'GeneratedAddFamilyInitial')]:
        verified(folder, stem)
        folder = Path(folder)
        report = json.loads((folder / 'report.json').read_text())
        if report['ast_sha256'] != raw['source_sha256'] or report.get('old_inv_read') is not False:
            raise ValueError('same AST and no old CPU invariant required')
        if digest((folder / (stem + '.vo')).read_bytes()) != report['object_sha256']:
            raise ValueError('checked provider object has changed: ' + stem)
        if 'graph_sha256' in report and report['graph_sha256'] != digest(Path(c['graph']).read_bytes()):
            raise ValueError('checked provider CDFG has changed: ' + stem)
        paths += json.loads((folder / 'providers.json').read_text())
        paths += [dict(namespace=namespace, directory=str(folder.resolve()))]
        receipts.append(dict(namespace=namespace, source_sha256=report['source_sha256'],
                             object_sha256=report['object_sha256']))
    bindings = {}
    for row in paths:
        if row['namespace'] in bindings and bindings[row['namespace']] != row['directory']:
            raise ValueError('incompatible original physical providers')
        bindings[row['namespace']] = row['directory']
    return [dict(namespace=n, directory=d) for n, d in bindings.items()], receipts


def inline_aliases(source):
    declarations = re.compile(r'\bModule\s+([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*'
        r'([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\s*\.\s*')
    aliases = {}
    for match in declarations.finditer(source):
        name, target = match.groups();first, *rest = target.split('.')
        aliases[name] = '.'.join([aliases.get(first, first), *rest])
    if set(aliases) != {'V', 'H', 'C', 'O', 'I', 'A', 'AC', 'AR', 'Q', 'F'}:
        raise ValueError('unrecognized module alias list')
    qualifier = re.compile(r'(?<![A-Za-z0-9_.])(' + '|'.join(aliases) + r')\.(?=[A-Za-z_])')
    normalized = qualifier.sub(lambda m: aliases[m.group(1)] + '.', declarations.sub('', source))
    return normalized, aliases


def check(c, link, output, after_timeout=None):
    out = Path(output).resolve();out.mkdir(parents=True, exist_ok=False)
    raw, profile, _ = family.derived.controls.history.admission.observation.origin.raw_binding(c['ast'], c['ast_module'])
    plan = family.discover(c, raw)
    paths, receipts = paths_for(c, link, raw)
    source, exports = render(c, raw, profile, plan)
    normalized_evidence = None
    if after_timeout:
        prior = Path(after_timeout);previous = json.loads((prior / 'report.json').read_text())
        original = (prior / 'ControlFamilyJoint.v').read_text()
        if not(previous['seconds'] >= 1200 and not previous.get('performance_attempt')
               and (previous.get('coqc_timed_out') or previous.get('coqchk_timed_out')
                    or previous.get('exact_type_audit_timed_out'))
               and original == source and previous['source_sha256'] == digest(source.encode())):
            raise ValueError('unchanged actual timed-out point required before its unique alias repair')
        source, aliases = inline_aliases(source)
        normalized_evidence = dict(alias_mapping=aliases, original_source_sha256=digest(original.encode()),
            new_source_sha256=digest(source.encode()), normalized_full_source_exact_equal=True)
        (out / 'same-target-alias-normalization.json').write_text(json.dumps(normalized_evidence, indent=2) + '\n')
    target = out / 'ControlFamilyJoint.v';target.write_text(source)
    for name, data in [('providers', paths), ('receipts', receipts), ('plan', plan), ('exports', exports), ('inputs', c)]:
        (out / (name + '.json')).write_text(json.dumps(data, indent=2) + '\n')
    flags = list(family.derived.rtl.framework.FLAGS)
    for row in paths:flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out), NS]
    start = time.monotonic();remaining = lambda: max(.1, 1200 - (time.monotonic() - start))
    root = family.derived.controls.history.admission.observation.origin.ROOT
    def stage(name, command):
        return run_stage(['/usr/bin/time', '-v', '-o', str(out / (name + '.resources')), *command],
                         out / (name + '.log'), remaining())
    cc, ct = stage('coqc', [str(root / '_opam/bin/coqc'), '-time', *flags, str(target)])
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=ct,
        source_sha256=digest(source.encode()), ast_sha256=raw['source_sha256'], old_inv_read=False,
        scope='ADD/ADDI/JAL current data and actual result phase', old_two_class_relation_modified=False,
        external_llm_api_calls=0, complete_R_generated=False, full_cycle_preserved=False,
        infinite_itree_refinement_proved=False, performance_attempt=1 if after_timeout else 0,
        actual_timeout_evidence=after_timeout, unchanged_normalized_original_source=normalized_evidence is not None)
    if cc.returncode == 0:
        axioms = audit_all_exports(cc.stdout.split('CONTROL_FAMILY_JOINT_AUDIT')[-1], len(exports))
        baseline = out / 'Baseline.v'
        baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
            'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
            'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
        bc, bt = stage('baseline', [str(root / '_opam/bin/coqc'), *flags, str(baseline)])
        allowed = parse_assumptions(bc.stdout) if bc.returncode == 0 else set()
        prefix = source[:source.index('Theorem sampled_add_controls')]
        prefix += 'Require Import GeneratedControlFamilyJoint.ControlFamilyJoint.\n'
        types = prefix
        # A copied Coq Record is a NEW nominal type, unlike copied Definitions.
        # Audit the imported original Current, never a locally redeclared record.
        scopes = source[source.index('Section ISA.'):source.index('Record Current')]
        for name in exports:
            if name == 'head_from_operand_clause':types += scopes
            match = re.search(r'Theorem ' + name + r'\b.*?(?=\nProof\.)', source, re.S)
            if not match:raise ValueError('missing original declaration ' + name)
            declaration = match.group(0)
            arguments = ('image events ev token rd rs1 rs2' if name == 'sampled_add_controls'
                         else 'image initial_imem' if name == 'actual_boot_current'
                         else 'initial ledger image events ev')
            types += declaration.replace(name, 'exact_' + name, 1) + '\nProof. exact (' + NS + '.ControlFamilyJoint.' + name + ' ' + arguments + '). Qed.\n'
        types += 'End ISA.\n'
        types += ''.join('Print Assumptions exact_' + name + '.\n' for name in exports)
        audit = out / 'ExactTypeAudit.v';audit.write_text(types)
        ac, at = stage('exact-type-audit', [str(root / '_opam/bin/coqc'), '-time', *flags, str(audit)])
        type_axioms = audit_all_exports(ac.stdout, len(exports)) if ac.returncode == 0 else set()
        kk, kt = stage('coqchk', [str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec', NS + '.ControlFamilyJoint'])
        ek, et = stage('exact-type-coqchk', [str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec', NS + '.ExactTypeAudit']) if ac.returncode == 0 else (None, False)
        okay = bc.returncode == ac.returncode == kk.returncode == 0 and ek is not None and ek.returncode == 0
        okay = okay and not(axioms - allowed) and not(type_axioms - allowed) and not(allowed - ALLOWED_AXIOMS)
        report.update(accepted=okay, baseline_coqc_exit=bc.returncode, baseline_timed_out=bt,
            baseline_assumptions=sorted(allowed), assumptions=sorted(axioms), exact_type_assumptions=sorted(type_axioms),
            assumptions_audit_passed=okay,
            exact_type_audit_exit=ac.returncode, exact_type_audit_timed_out=at,
            coqchk_exit=kk.returncode, coqchk_timed_out=kt,
            exact_type_coqchk_exit=ek.returncode if ek is not None else None, exact_type_coqchk_timed_out=et)
    report['seconds'] = time.monotonic() - start
    if report['accepted']:report['object_sha256'] = digest(target.with_suffix('.vo').read_bytes())
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--link', required=True);parser.add_argument('--output', required=True)
    parser.add_argument('--inline-aliases-after-timeout')
    args = parser.parse_args();config = family.inputs()
    config['family_joint'] = 'results/r-add-family-joint-20261027-a2'
    config['family_initial'] = 'results/r-add-family-initial-20261027-optimization1-b'
    try:result = check(config, args.link, args.output, args.inline_aliases_after_timeout)
    except Exception as error:
        out = Path(args.output)
        if out.is_dir() and not(out / 'report.json').exists():
            (out / 'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight', error=str(error)), indent=2) + '\n')
        raise
    print(json.dumps(result, indent=2));raise SystemExit(0 if result['accepted'] else 1)
