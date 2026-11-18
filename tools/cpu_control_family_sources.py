"""Restore real ADD/ADDI sources in Current3, including older JAL writes."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_family_sources as old
from cpu_add_capture_result_certificate import verified
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

NS = 'GeneratedControlFamilySources'
STEM = 'ControlFamilySources'


def replace_once(source, before, after):
    return old.replace_once(source, before, after)


def qualify(source):
    """New consumer starts fully qualified; never clones an imported module."""
    aliases = dict(re.findall(r'Module\s+(\w+)\s*:=\s*([\w.]+)\s*\.', source))
    source = re.sub(r'Module\s+\w+\s*:=\s*[\w.]+\s*\.\s*', '', source)
    for _ in range(len(aliases) + 1):
        changed = False
        for short, path in aliases.items():
            source, count = re.subn(r'(?<![\w.])' + short + r'\.(?=[A-Za-z_])', path + '.', source)
            changed |= bool(count)
        if not changed:
            return source
    raise ValueError('cyclic module alias in physical source syntax')


def render(c, raw, profile, plan, cov):
    source, exports = old.render(c, raw, profile, plan, cov)
    p, am = profile['ast']['program'], raw['module']
    h = 'Runtime'; packed = '(Runtime.boot_history image events)'
    sample = f'(phase_driven_state {p} ev pre)'; post = f'(PhaseSemantics {p} ev pre)'
    j = 'GeneratedControlFamilyJoint.ControlFamilyJoint'
    q = 'GeneratedPhasePendingCommit.PhasePendingCommit'
    refpc = 'GeneratedFetchReference.FetchReference.recorded_pc'
    source = source.replace('GeneratedAddFamilyJoint.AddFamilyJoint', j)
    source = source.replace('CPUReferenceAddFamilyProducers', 'CPUReferenceControlFamilyProducers')
    source = source.replace('CPUISAAddFamilyReferenceValues', 'CPUISAControlFamilyReferenceValues')
    source = replace_once(source, 'Ex.External.CPUISAAddiEffects Ex.External.CPUISAControlFamilyReferenceValues.',
        'Ex.External.CPUISAAddiEffects Ex.External.CPUISAControlFamilyReferenceValues Ex.External.CPUISAJalEffects\n'
        ' GeneratedControlFamilyProducerAdapter.ControlFamilyProducerAdapter\n'
        ' GeneratedJalProducerControls.JalProducerControls GeneratedFetchReference.FetchReference.')
    source = source.replace('{word_ok:word.ok word}{registers_ok:map.ok Registers}.',
                            '{word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.')
    source = replace_once(source, 'Definition Current(token_pc:Token->Z)', 'Definition Current')
    for name in exports:
        source = re.sub(r'\b' + name + r' token_pc\b', name, source)
    source = source.replace('Current token_pc ', 'Current ')
    for name in ['OperandClause', 'head_from_operand_clause']:
        source = source.replace('J.' + name + ' token_pc ', 'J.' + name + ' ')
    source = source.replace('Family.reference_result_family_compatible',
        'GeneratedControlFamilyProducerAdapter.ControlFamilyProducerAdapter.actual_reference_result_family_compatible')
    source = source.replace('HE HEv HN HOp)as HH', 'HE HEv HN HInitial HOp)as HH')
    # Initial ISA alignment is a pure relation, never an environment predicate.
    aligned = [name for name in exports if name not in ['actual_admitted_tag', 'operand_clause_idle']]
    for name in aligned:
        match = re.search(r'(?:Theorem|Lemma) ' + name + r'\b.*?(?=\nProof\.)', source, re.S)
        if not match:
            raise ValueError('missing source declaration: ' + name)
        head = match.group(0)
        if head.count('Runtime.W.Environment ev ->') != 1:
            raise ValueError('ambiguous source environment: ' + name)
        source = source[:match.start()] + head.replace('Runtime.W.Environment ev ->',
            'Runtime.W.Environment ev ->CPUISAJalEffects.NextPCAligned initial ->') + source[match.end():]
    source = source.replace('HE HEv HJ', 'HE HEv HInitial HJ')
    source = source.replace('intros pre HE HEv HT', 'intros pre HE HEv HInitial HT')
    source = source.replace('HE HEv HClass', 'HE HEv HInitial HClass')
    source = source.replace('HE HEv(eq_sym HTag)', 'HE HEv HInitial(eq_sym HTag)')
    source = source.replace('ps[token]before HC)', 'ps[token]before HInitial HC)')
    source = source.replace('right;exists dest,rs,imm;', 'right;left;exists dest,rs,imm;')
    # Producer classification includes JAL and its actual write/load controls.
    source = source.replace('destruct HDecode as[[rs1[rs2 HD]]|[rs[imm HD]]].',
        'destruct HDecode as[[rs1[rs2 HD]]|[[rs[imm HD]]|[imm HD]]].')
    for row in plan['rows']:
        i = row['stage']; rd = row['routes']['rd']['input']
        old_tail = f'exact(AI.actual_addi_sampled_controls_{i} image events ev token _ rs imm HE HEv HV HT HD). }}'
        new_tail = f'exact(AI.actual_addi_sampled_controls_{i} image events ev token _ rs imm HE HEv HV HT HD).\n'
        new_tail += f'      - exact(actual_jal_sampled_controls_{i} image events ev token _ imm HE HEv HV HT HD). }}'
        source = replace_once(source, old_tail, new_tail)
    # Inactive EX capture preserves all three semantic operand alternatives.
    source = replace_once(source,
        'destruct HProjection as[[rd[rs1[rs2[HD HReads]]]]|[rd[rs[imm[HD HReads]]]]].',
        'destruct HProjection as[[rd[rs1[rs2[HD HReads]]]]|[[rd[rs[imm[HD HReads]]]]|[rd[imm HD]]]].')
    source = source.replace(' - right;exists rd,rs,imm;', ' - right;left;exists rd,rs,imm;')
    before = source.index('Lemma operand_clause_idle')
    end = source.index('\nQed.', before)
    source = source[:end] + '\n - right;right;exists rd,imm;exact HD.' + source[end:]
    # The incoming class is current-state evidence, not a future ISA guess.
    old_class = fr'''(forall token,current(fst {packed})=Some token ->
  (exists rd rs1 rs2,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) \/
  (exists rd rs imm,Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Addi rd rs imm))) ->'''
    if source.count(old_class) != 2:
        raise ValueError('unrecognized original two-family capture predicate')
    source = source.replace(old_class, f'(forall token,current(fst {packed})=Some token ->CPUISAControlFamilyReferenceValues.ControlFamily token_word token) ->')
    source = replace_once(source,
        'destruct(HClass token(eq_sym HTag))as[[rd[rs1[rs2 HD]]]|[rd[rs[imm HD]]]].',
        'destruct(HClass token(eq_sym HTag))as[[rd[rs1[rs2 HD]]]|[[rd[rs[imm HD]]]|[rd[imm HD]]]].')
    marker = ' - destruct HJ as[HN HC HR HResult HOp HChain].'
    source = replace_once(source, marker,
        '   + exact(actual_admitted_jal_operand_relation initial retired current_state image events ev token rd imm HE HEv HInitial(eq_sym HTag)HM HV HD HJ).\n' + marker)
    # JAL needs no source value, but its original token/effect cut is retained.
    jal = f'''Theorem actual_admitted_jal_operand_relation initial retired current image events ev token rd imm:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->CPUISAJalEffects.NextPCAligned initial ->
 ExtendedSVCaptureBirth.current(fst {packed})=Some token ->
 process_matches_states pre {sample}{am}.{plan['head']['process']}=true ->
 norm 1(read_signal {post}{plan['head']['valid']})<>0%Z ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 Current initial retired current pre{packed} ->
 computed_result_R(instruction_effect token_pc token_word)token_eq_dec
 (J.OperandProjection token {post})token initial(ledger retired pre{packed}).
Proof. intros pre HE HEv HInitial HT HM HV HD HJ.
 destruct(GeneratedCapturedReads.CapturedReadAddresses.sample_evidence image events ev HE HEv)as[seed HL];fold pre in HL.
 pose proof(admitted_source_valid seed ev pre HEv HL HM HV)as HSource.
 pose proof(admission_old_clock_zero ev pre HEv HM HV)as HClock.
 destruct HJ as[HN HC HR HResult HOp[frontier HChain]].
 set(older:={q}.slot pre 286(Captured.C.chain_tag1(snd{packed}))++{q}.slot pre 250(Captured.C.chain_tag0(snd{packed}))).
 assert(HPending:{q}.actual_pending pre{packed}=older++[token]).
 {{ rewrite({q}.pending_low pre{packed}HClock);unfold {q}.lower_pending,older.
    rewrite({q}.slot_nonempty pre 141 _ token HSource HT),app_assoc;reflexivity. }}
 rewrite HPending in HChain.
 destruct(chain_split(instruction_effect token_pc token_word)older current[token]frontier HChain)as[before[HOlder HSingle]].
 inversion HSingle as[|a t after rest last HStep HNil];subst;inversion HNil;subst.
 assert(HLedger:ledger retired pre{packed}=(retired++older)++[token])by(unfold ledger;rewrite HPending;apply app_assoc).
 assert(HBefore:BeforeToken(instruction_effect token_pc token_word)initial(ledger retired pre{packed})(length(retired++older))token before).
 {{ rewrite HLedger;apply Ref.before_prefix;eapply chain_append;[exact HC|exact HOlder]. }}
 assert(HND:NoDup(ledger retired pre{packed}))by(eapply NoDup_map_inv;exact HN).
 apply(proj2(computed_result_R_exact(instruction_effect token_pc token_word)token_eq_dec
 (J.OperandProjection token {post})token initial(ledger retired pre{packed}))).
 exists(length(retired++older)),before,frontier;split.
 - exact(lookup_before_complete(instruction_effect token_pc token_word)token_eq_dec token(ledger retired pre{packed})initial _ before HND HBefore).
 - split;[exact HStep|];right;right;exists rd,imm;exact HD.
Qed.
'''
    index = source.index('Lemma actual_admitted_tag')
    source = source[:index] + jal + source[index:]
    # Small local wrappers discharge JAL producer controls with proved wires.
    controls = ''
    for row in plan['rows']:
        i = row['stage']; wr = row['routes']['write']['input']; ld = row['routes']['load']['input']; rdroot = row['routes']['rd']['input']
        controls += f'''Theorem actual_jal_sampled_controls_{i} image events ev token rd imm:
 let pre:=phase_run {p} events(Runtime.F.boot image)in
 Forall Runtime.W.Environment events ->Runtime.W.Environment ev ->norm 1(read_signal pre {row['valid']})<>0%Z ->
 Captured.C.chain_tag{i}(snd{packed})=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Jal rd imm) ->
 GeneratedReadySelector.ReadySelector.bit {sample}{wr}=true /\\
 GeneratedReadySelector.ReadySelector.bit {sample}{ld}=false /\\norm 5(read_signal {sample}{rdroot})=rd.
Proof. intros pre HE HEv HV HT HD.
 destruct(GeneratedJalProducerControls.JalProducerControls.actual_jal_producer_controls_{i} image events token rd imm HE HV HT HD)as[HW HL].
 exact(conj(f_equal(fun value=>Z.eqb value 1%Z)(eq_trans(GeneratedReadyControls.ReadyControls.sampled_{i}_write image events ev HE HEv)HW))
 (conj(f_equal(fun value=>Z.eqb value 1%Z)(eq_trans(GeneratedReadyControls.ReadyControls.sampled_{i}_load image events ev HE HEv)HL))
 (eq_trans(GeneratedReadyControls.ReadyControls.sampled_token_destination_{i} image events ev token HE HEv HV HT)
 (GeneratedControlFamilyProducerAdapter.ControlFamilyProducerAdapter.actual_jal_destination_field token_word token rd imm HD)))). Qed.
'''
    index = source.index('Section OriginalISA.')
    source = source[:index] + controls + source[index:]
    source = re.sub(r'\btoken_pc\b', refpc, source)
    # All new source records/fields use the fixed actual token PC recorder.
    exports = [f'actual_jal_sampled_controls_{row["stage"]}' for row in plan['rows']] + exports
    exports.insert(exports.index('actual_admitted_tag'), 'actual_admitted_jal_operand_relation')
    source = source[:source.index('Goal True. idtac "FAMILY_SOURCES_AUDIT"')]
    source += 'Goal True. idtac "CONTROL_FAMILY_SOURCES_AUDIT". exact I. Qed.\n'
    source += ''.join('Print Assumptions ' + name + '.\n' for name in exports)
    source = qualify(source)
    if 'QueueRegisterInv' in source or re.search(r'Module\s+\w+\s*:=', source):
        raise ValueError('old invariant or copied module escaped source rendering')
    return source, exports


def check(c, family, addi_controls, addi_capture, jal_controls, producers, output, spent=()):
    providers = [(family, 'ControlFamilyJoint', 'GeneratedControlFamilyJoint'),
                 (addi_controls, 'AddiReadyControls', 'GeneratedAddiReadyControls'),
                 (addi_capture, 'AddiCapture', 'GeneratedAddiCapture'),
                 (jal_controls, 'JalProducerControls', 'GeneratedJalProducerControls')]
    paths = []
    for folder, stem, namespace in providers:
        if stem == 'JalProducerControls':
            path = Path(folder)
            r = json.loads((path / 'report.json').read_text())
            audit = r.get('exact_type_audit', {})
            if not (r.get('accepted') and r.get('coqc_exit') == r.get('coqchk_exit') == 0 and
                    audit.get('accepted') and audit.get('coqc_exit') == audit.get('coqchk_exit') == 0 and
                    not r.get('assumptions') and not audit.get('assumptions') and
                    hashlib.sha256((path / (stem + '.v')).read_bytes()).hexdigest() == r['source_sha256'] and
                    hashlib.sha256((path / (stem + '.vo')).read_bytes()).hexdigest() == r['object_sha256']):
                raise ValueError('closed independently checked JAL controls required')
        else:
            verified(folder, stem)
        paths += json.loads((Path(folder) / 'providers.json').read_text())
        paths.append(dict(namespace=namespace, directory=str(Path(folder).resolve())))
    producer_path = Path(producers)
    receipt = json.loads((producer_path / 'report.json').read_text())
    if not (receipt.get('accepted') and receipt.get('assumptions_audit_passed') and
            all(stage['exit'] == 0 for stage in receipt['stages'].values())):
        raise ValueError('accepted F3 producer library and adapter required')
    for file, key in [('src/Ex/External/CPUReferenceControlFamilyProducers.v', 'source_sha256'),
                      ('src/Ex/External/CPUReferenceControlFamilyProducers.vo', 'library_object_sha256')]:
        if hashlib.sha256(Path(file).read_bytes()).hexdigest() != receipt[key]:
            raise ValueError('F3 library changed since acceptance: ' + file)
    for file, key in [('ControlFamilyProducerAdapter.v', 'adapter_source_sha256'),
                      ('ControlFamilyProducerAdapter.vo', 'adapter_object_sha256')]:
        if hashlib.sha256((producer_path / file).read_bytes()).hexdigest() != receipt[key]:
            raise ValueError('F3 adapter changed since acceptance: ' + file)
    paths += json.loads((producer_path / 'providers.json').read_text())
    paths.append(dict(namespace='GeneratedControlFamilyProducerAdapter', directory=str(producer_path.resolve())))
    unique = {}
    for row in paths:
        directory = str(Path(row['directory']).resolve())
        if row['namespace'] in unique and unique[row['namespace']] != directory:
            raise ValueError('conflicting structural provider: ' + row['namespace'])
        unique[row['namespace']] = directory
    paths = [dict(namespace=key, directory=value) for key, value in unique.items()]
    raw, profile, _ = old.base.controls.history.admission.observation.origin.raw_binding(c['ast'], c['ast_module'])
    plan = old.joint.discover(c, raw)
    covdir = unique['GeneratedCoveredCapture']
    cov = json.loads((Path(covdir) / 'plan.json').read_text())
    source, exports = render(c, raw, profile, plan, cov)
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    file = out / (STEM + '.v')
    file.write_text(source)
    for key, value in [('providers', paths), ('exports', exports), ('plan', plan), ('inputs', c)]:
        (out / (key + '.json')).write_text(json.dumps(value, indent=2) + '\n')
    flags = list(old.base.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), NS]
    root = old.base.controls.history.admission.observation.origin.ROOT
    prior_seconds = 0
    for prior in spent:
        prior_receipt = json.loads((Path(prior) / 'report.json').read_text())
        if prior_receipt.get('accepted'):
            raise ValueError('accepted proof point must not be rebuilt')
        prior_seconds += prior_receipt['seconds']
    budget = 1200 - prior_seconds
    if budget <= 0:
        raise ValueError('proof point budget exhausted; separate authorization required')
    started = time.monotonic()
    stages = {}

    def run(name, command):
        result, timed_out = run_stage(command, out / (name + '.log'), max(.1, budget - (time.monotonic() - started)))
        stages[name] = dict(exit=result.returncode, timed_out=timed_out)
        return result

    baseline = out / 'Baseline.v'
    baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
                        'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
                        'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
    bc = run('baseline', [str(root / '_opam/bin/coqc'), *flags, str(baseline.resolve())])
    cc = run('coqc', [str(root / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())])
    report = dict(accepted=False, exports=exports, stages=stages, source_sha256=hashlib.sha256(source.encode()).hexdigest(),
                  ast_sha256=raw['source_sha256'], coqc_exit=cc.returncode, old_inv_read=False,
                  complete_R_generated=False, infinite_itree_refinement_proved=False)
    if cc.returncode == 0:
        assumptions = audit_all_exports(cc.stdout.split('CONTROL_FAMILY_SOURCES_AUDIT')[-1], len(exports))
        baseline_assumptions = parse_assumptions(bc.stdout)
        audit = (bc.returncode == 0 and not (assumptions - baseline_assumptions) and not (assumptions - ALLOWED_AXIOMS))
        types = source[:source.index('Lemma protect')]
        types += f'\nRequire Import {NS}.{STEM}.\nImport {NS}.{STEM}.\nSection ExactTypes.\n'
        types += ('Context {word:Interface.word 32}{BW:Bitwidth 32}{Registers:map.map Z word}{Mem:map.map word byte}\n'
                  ' {word_ok:word.ok word}{registers_ok:map.ok Registers}{mem_ok:map.ok Mem}.\n')
        original_headers = {}
        for name in exports:
            match = re.search(r'(?:Theorem|Lemma) ' + name + r' ([^:]+):(.*?)\nProof\.', source, re.S)
            if not match:
                raise ValueError('cannot independently restate original export: ' + name)
            binders, statement = match.groups()
            original_headers[name] = match.group(0)
            # The original header is unchanged modulo explicit resolution of
            # this file's two definitions; imported older short names cannot
            # silently select another relation in the independent audit.
            statement = re.sub(r'(?<![\w.])Current\b', NS + '.' + STEM + '.Current', statement)
            statement = re.sub(r'(?<![\w.])ledger(?= retired\b)', NS + '.' + STEM + '.ledger', statement)
            types += f'Definition checked_{name} {binders}:{statement}\nProof. exact({NS}.{STEM}.{name} {binders}). Qed.\n'
        types += 'End ExactTypes.\n'
        (out / 'original-export-headers.json').write_text(json.dumps(original_headers, indent=2) + '\n')
        target = out / 'TargetTypes.v'
        target.write_text(types)
        tc = run('target-types', [str(root / '_opam/bin/coqc'), *flags, str(target.resolve())])
        kc = run('coqchk', [str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec', NS + '.' + STEM])
        kt = run('target-coqchk', [str(root / '_opam/bin/coqchk'), '-silent', *flags, '-norec', NS + '.TargetTypes'])
        report.update(coqchk_exit=kc.returncode, target_types_exit=tc.returncode,
                      assumptions=sorted(assumptions), baseline_assumptions=sorted(baseline_assumptions),
                      assumptions_audit_passed=audit, accepted=audit and all(row['exit'] == 0 for row in stages.values()))
    report['seconds'] = time.monotonic() - started
    report['prior_seconds'] = prior_seconds
    report['point_total_seconds'] = prior_seconds + report['seconds']
    report['spent_from'] = list(spent)
    if report['accepted']:
        report['object_sha256'] = hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['family', 'addi-controls', 'addi-capture', 'jal-controls', 'producers', 'output']:
        parser.add_argument('--' + key, required=True)
    parser.add_argument('--spent', action='append', default=[])
    args = parser.parse_args()
    result = check(old.joint.inputs(), args.family, args.addi_controls, args.addi_capture,
                   args.jal_controls, args.producers, args.output, args.spent)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
