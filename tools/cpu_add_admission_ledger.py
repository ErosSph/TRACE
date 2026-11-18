"""Use actual admission queue/data certificates on the SAME extended ledger.

The generated R candidate includes a present-state serial-range clause. This
consumer proves its admission preservation, not its full reset/cycle closure.
No new instruction execution success is smuggled into the environment.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_add_admission_queue as queue
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports


def checked_provider(folder, filename, ast_sha, obligations):
    folder = Path(folder); report = json.loads((folder / 'report.json').read_text())
    source = folder / filename
    if not (report.get('accepted') is True and report.get('coqc_exit') == report.get('coqchk_exit') == 0
            and report.get('assumptions_audit_passed') is True and report.get('old_inv_read') is False
            and report.get('ast_sha256') == ast_sha
            and hashlib.sha256(source.read_bytes()).hexdigest() == report['source_sha256']
            and source.with_suffix('.vo').is_file()
            and set(report['isa_assumptions']) <= set(report['baseline_assumptions']) <= ALLOWED_AXIOMS
            and all(report.get(key) is True for key in obligations)):
        raise ValueError('same-source accepted native admission provider required: ' + str(folder))
    return json.loads((folder / 'providers.json').read_text())


def qualify_module_aliases(source):
    """Remove only module re-exports, preserving their exact constant bindings."""
    bindings = {
        'AQ': ('GeneratedAdmissionQueue.AdmissionQueue', 'GeneratedAdmissionQueue.AdmissionQueue'),
        'AD': ('GeneratedAdmissionData.AdmissionData', 'GeneratedAdmissionData.AdmissionData'),
        'D': ('AQ.D', 'GeneratedAdmissionQueue.AdmissionQueue.D'),
        'Q': ('GeneratedPhasePendingCommit.PhasePendingCommit', 'GeneratedPhasePendingCommit.PhasePendingCommit'),
        'O': ('GeneratedOperandResultJoint.OperandResultJoint', 'GeneratedOperandResultJoint.OperandResultJoint'),
        'V': ('O.V', 'GeneratedOperandResultJoint.OperandResultJoint.V')}
    for name,(declared,_) in bindings.items():
        declaration = f'Module {name}:={declared}.'
        if source.count(declaration) != 1:
            raise ValueError('unexpected module alias declaration: ' + name)
        source = source.replace(declaration, '', 1)
    pattern = re.compile(r'(?<![A-Za-z0-9_.])(AQ|AD|D|Q|O|V)\.')
    return pattern.sub(lambda match: bindings[match.group(1)][1] + '.', source)


def render(c, raw, profile, plan, qualify_aliases=False):
    p, am = profile['ast']['program'], raw['module']; b, head = plan['birth'], plan['head']
    packed = '(D.Runtime.boot_history image events)'
    sample = f'(phase_driven_state {p} ev pre)'; post = f'(PhaseSemantics {p} ev pre)'
    after = f'(D.Captured.advance_capture_fields ev pre {packed} tt)'
    decision = f'(phase_decision {p} {am}.{b["process"]} {b["root"]} AQ.N.B.root_{b["root"]}_expression AQ.N.B.root_{b["valid"]}_expression ev pre)'
    source = f'''From Coq Require Import List ZArith.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCapturedPending Lang.ExtendedSVCompanionField Lang.ExtendedSVValidCompanion
 Ex.External.CPUReferenceLedgerExtension Ex.External.CPUReferenceValues Ex.External.CPUISAAddReferenceValues
 Ex.RvCore.FormalSpec coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth coqutil.Map.Interface coqutil.Byte
 GeneratedAdmissionData.AdmissionData GeneratedAdmissionQueue.AdmissionQueue.
Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVWordInvariant ExtendedSVCaptureBirth
 ExtendedSVCapturedPending ExtendedSVCompanionField ExtendedSVValidCompanion CPUReferenceLedgerExtension.
Module AQ:=GeneratedAdmissionQueue.AdmissionQueue. Module AD:=GeneratedAdmissionData.AdmissionData.
Module D:=AQ.D. Module Q:=GeneratedPhasePendingCommit.PhasePendingCommit.
Module O:=GeneratedOperandResultJoint.OperandResultJoint. Module V:=O.V.
Local Opaque {p} PhaseSemantics.
Definition LedgerRange pre(packed:D.Captured.Packed)retired:=
 HistoryRange(serial(fst packed))(retired++Q.actual_pending pre packed).
Lemma admitted_form ev pre packed:
 AQ.admitted ev pre packed=NewTokens {decision}(serial(fst packed)){sample} AQ.N.B.capture_0_pc.
Proof. destruct packed as[g tags];destruct tags;reflexivity. Qed.
Lemma actual_post_serial ev pre packed:
 serial(fst(D.Captured.advance_capture_fields ev pre packed tt))=next_serial {decision}(serial(fst packed)).
Proof. destruct packed as[g tags];destruct tags;reflexivity. Qed.
Section OriginalISA.
Context {{word:Interface.word 32}}{{BW:Bitwidth 32}}{{Registers:map.map Z word}}{{Mem:map.map word byte}}
 {{word_ok:word.ok word}}{{registers_ok:map.ok Registers}}.
Definition CurrentWithRange token_pc initial retired current pre packed:=
 D.Current token_pc initial retired current pre packed /\\LedgerRange pre packed retired.
Theorem reference_results_survive_append token_pc initial retired pending extra pre packed:
 V.ReferenceJoint token_pc initial retired pending pre packed ->
 V.ReferenceJoint token_pc initial retired(pending++extra)pre packed.
Proof. unfold V.ReferenceJoint,V.Joint;rewrite app_assoc;intros[HC[HM HW]].
 split;[exact HC|];split;intros HV token HT.
 - unfold CPUISAAddReferenceValues.values;apply successful_lookup_extends.
   exact(HM HV token HT).
 - unfold CPUISAAddReferenceValues.values;apply successful_lookup_extends.
   exact(HW HV token HT).
Qed.
Theorem actual_admission_restores_extended_register_data token_pc initial retired current_state image events ev:
 let pre:=phase_run {p} events(D.Runtime.F.boot image)in
 Forall D.Runtime.W.Environment events ->D.Runtime.W.Environment ev ->
 (forall token,current(fst {packed})=Some token ->exists rd rs1 rs2,
  Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2)) ->
 CurrentWithRange token_pc initial retired current_state pre {packed} ->
 process_matches_states pre {sample}{am}.{head['process']}=true ->
 norm 1(read_signal {post}{head['valid']})<>0%Z ->
 O.RFJoint token_pc initial retired(Q.actual_pending {post}{after})current_state {post}{after} /\\
 LedgerRange {post}{after} retired.
Proof. intros pre HE HEv HClass[HCurrent HRange]HM HV.
 pose proof(AQ.actual_admission_pending_transfer image events ev HE HEv HM HV)as HQ;fold pre in HQ.
 pose proof(AD.actual_admission_preserves_physical_RFJoint token_pc initial retired current_state image events ev
 HE HEv HClass HCurrent HM HV)as HData;fold pre in HData.
 destruct HData as[HN[[HC[HR HResults]]HOldOperands]].
 pose proof(AQ.actual_admission_restores_operand_clause token_pc initial retired current_state image events ev
 HE HEv HClass HCurrent HM HV)as HOperands;fold pre in HOperands.
 assert(HNewUnique:NoDup(map token_id(retired++(Q.actual_pending pre {packed}++AQ.admitted ev pre {packed})))).
 {{ rewrite app_assoc,admitted_form.
    exact(actual_births_preserve_unique_ledger {decision}(serial(fst {packed})){sample} AQ.N.B.capture_0_pc
     (retired++Q.actual_pending pre {packed})HRange HN). }}
 assert(HNewRange:HistoryRange(serial(fst {after}))(retired++(Q.actual_pending pre {packed}++AQ.admitted ev pre {packed}))).
 {{ rewrite actual_post_serial,app_assoc,admitted_form.
    exact(actual_births_preserve_ledger_range {decision}(serial(fst {packed})){sample} AQ.N.B.capture_0_pc
     (retired++Q.actual_pending pre {packed})HRange). }}
 pose proof(reference_results_survive_append token_pc initial retired(Q.actual_pending pre {packed})
 (AQ.admitted ev pre {packed}){post}{after} HResults)as HNewResults.
 assert(HNewData:O.RFJoint token_pc initial retired(Q.actual_pending pre {packed}++AQ.admitted ev pre {packed})
 current_state {post}{after}).
 {{ split;[exact HNewUnique|];split;[exact(conj HC(conj HR HNewResults))|].
    exact(eq_rect _ (fun pending=>O.OperandClause token_pc initial(retired++pending){post}{after})
      HOperands _ HQ). }}
 split.
 - exact(eq_rect _ (fun pending=>O.RFJoint token_pc initial retired pending current_state {post}{after})HNewData _ (eq_sym HQ)).
 - unfold LedgerRange.
   exact(eq_rect _ (fun pending=>HistoryRange(serial(fst {after}))(retired++pending))HNewRange _ (eq_sym HQ)).
Qed.
End OriginalISA.
Goal True. idtac "ADMISSION_LEDGER_LOCAL_AUDIT". exact I. Qed.
Print Assumptions admitted_form. Print Assumptions actual_post_serial.
Goal True. idtac "ADMISSION_LEDGER_ISA_AUDIT". exact I. Qed.
Print Assumptions reference_results_survive_append.
Print Assumptions actual_admission_restores_extended_register_data.
'''
    return qualify_module_aliases(source) if qualify_aliases else source


def check(c, output, qualify_aliases=False, baseline=None):
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    raw, profile, _ = queue.sources.controls.history.admission.observation.origin.raw_binding(c['ast'], c['ast_module'])
    plan = queue.checked_sources(c['derived_sources'], raw['source_sha256'])
    paths = checked_provider(c['admission_queue'], 'AdmissionQueue.v', raw['source_sha256'],
        ['actual_post_ledger_queue_equation_proved', 'actual_post_operand_clause_proved'])
    paths += checked_provider(c['admission_data'], 'AdmissionData.v', raw['source_sha256'], ['actual_physical_RFJoint_proved'])
    paths += [dict(directory=str(Path(c[key]).resolve()), namespace=ns) for key, ns in
        [('admission_queue', 'GeneratedAdmissionQueue'), ('admission_data', 'GeneratedAdmissionData')]]
    bindings = {}
    for row in paths:
        previous = bindings.get(row['namespace'])
        if previous is not None and previous != row['directory']:
            raise ValueError('different underlying current R providers')
        bindings[row['namespace']] = row['directory']
    paths = [dict(directory=v, namespace=k) for k, v in bindings.items()]
    queue.sources.controls.history.admission.verify_environment_paths(paths)
    queue.sources.controls.history.admission.checked_graph(c['graph'], c['ast'], out / 'replayed')
    rules = json.loads((Path(c['ledger_rules']) / 'report.json').read_text())
    row = next((r for r in rules['modules'] if r['module'] == 'Ex/External/CPUReferenceLedgerExtension'), None)
    if not (rules['accepted'] and row and row['accepted'] and row['assumptions'] == []
            and row['source_sha256'] == hashlib.sha256((queue.normal.origin.ROOT / 'src/Ex/External/CPUReferenceLedgerExtension.v').read_bytes()).hexdigest()):
        raise ValueError('native-checked generic ledger extension rules required')
    source = render(c, raw, profile, plan, qualify_aliases); file = out / 'AdmissionLedger.v'; file.write_text(source)
    if qualify_aliases:
        if baseline is None:
            raise ValueError('the one repair requires an actual timed-out baseline')
        bp=Path(baseline);br=json.loads((bp/'report.json').read_text());old=(bp/'AdmissionLedger.v').read_text()
        if not(br['accepted'] is False and br['seconds']>=1200
            and ((br.get('coqc_exit')==124 and br.get('coqc_timed_out'))
              or (br.get('coqchk_exit')==124 and br.get('coqchk_timed_out')))
            and br['ast_sha256']==raw['source_sha256']
            and hashlib.sha256(old.encode()).hexdigest()==br['source_sha256']
            and old==render(c,raw,profile,plan) and qualify_module_aliases(old)==source):
            raise ValueError('same-statement actual twenty-minute baseline required')
        receipt=dict(optimization_attempt=1,baseline=str(bp),baseline_exit=br.get('coqchk_exit',br['coqc_exit']),
            baseline_seconds=br['seconds'],original_source_sha256=br['source_sha256'],
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),
            mechanically_qualified_source_identical=True,RTL_ISA_environment_goal_unchanged=True,
            native_budget_seconds=1200,output=str(out))
        with (bp/'one-same-goal-repair.json').open('x')as lock:
            lock.write(json.dumps(receipt,indent=2)+'\n')
        (out/'same-goal-repair.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (out / 'providers.json').write_text(json.dumps(paths, indent=2) + '\n')
    (out / 'plan.json').write_text(json.dumps(dict(ast_sha256=raw['source_sha256'], birth=plan['birth'], head=plan['head']), indent=2) + '\n')
    flags = list(queue.sources.rtl.framework.FLAGS)
    for row in paths: flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedAdmissionLedger']; start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
        str(queue.normal.origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())], out / 'coqc.log', 1200)
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'], old_inv_read=False,
        same_actual_post_ledger_RF_results_operands_proved=False, serial_range_admission_preservation_proved=False,
        serial_range_from_all_actual_histories_proved=False, full_pending_ISA_chain_proved=False,
        complete_R_generated=False, itree_refinement_proved=False, external_llm_api_calls=0,
        qualify_module_aliases=qualify_aliases,optimization_baseline=baseline)
    if cc.returncode == 0:
        local = cc.stdout.split('ADMISSION_LEDGER_LOCAL_AUDIT')[-1].split('ADMISSION_LEDGER_ISA_AUDIT')[0]
        axioms = audit_all_exports(cc.stdout.split('ADMISSION_LEDGER_ISA_AUDIT')[-1], 2)
        closed = local.count('Closed under the global context') == 2 and 'Axioms:' not in local
        baseline = set(json.loads((Path(c['derived_sources']) / 'report.json').read_text())['baseline_assumptions'])
        audit = closed and not (axioms - baseline) and not (axioms - ALLOWED_AXIOMS)
        kk, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
            str(queue.normal.origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec', 'GeneratedAdmissionLedger.AdmissionLedger'],
            out / 'coqchk.log', max(.1, 1200 - (time.monotonic() - start)))
        ok = audit and kk.returncode == 0
        report.update(accepted=ok, coqchk_exit=kk.returncode, coqchk_timed_out=timed,
            local_assumptions_closed=closed, assumptions_audit_passed=audit, isa_assumptions=sorted(axioms), baseline_assumptions=sorted(baseline),
            same_actual_post_ledger_RF_results_operands_proved=ok, serial_range_admission_preservation_proved=ok)
    report['seconds'] = time.monotonic() - start
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n'); return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['inputs', 'output']: parser.add_argument('--' + key, required=True)
    parser.add_argument('--qualify-aliases',action='store_true')
    parser.add_argument('--baseline')
    args = parser.parse_args()
    try: report = check(json.loads(Path(args.inputs).read_text()), args.output,args.qualify_aliases,args.baseline)
    except Exception as exc:
        out = Path(args.output)
        if out.is_dir() and not (out / 'report.json').exists():
            (out / 'report.json').write_text(json.dumps(dict(accepted=False, stage='preflight', error=str(exc), cli_exit=1), indent=2) + '\n')
        raise
    print(json.dumps(report, indent=2)); raise SystemExit(0 if report['accepted'] else 1)
