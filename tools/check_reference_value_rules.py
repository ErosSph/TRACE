"""Native compile, assumption audit and independent kernel checks for R rules."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
from cpu_certificate_acceptance import run_stage, parse_assumptions, ALLOWED_AXIOMS
import cpu_pending_origins as origin


def audit_all_exports(stdout, count):
    groups = re.findall(r'^Axioms:\n(.*?)(?=^Chars|\Z)', stdout, re.M | re.S)
    if stdout.count('Closed under the global context') + len(groups) != count:
        raise ValueError('missing or extra native export audit')
    axioms = set()
    for group in groups:
        names = re.findall(r'^([A-Za-z_][A-Za-z0-9_.]*)\s*:', group, re.M)
        if not names:
            raise ValueError('unrecognized native axiom block')
        axioms.update(names)
    return axioms


def check(output, selected=None):
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    flags = origin.pending.rtl.framework.FLAGS
    baseline = out / 'Baseline.v'
    baseline.write_text('Require Import Ex.External.CPUISAInstructionExecution.\n'
        'Goal True. idtac "ACCEPTANCE_ASSUMPTIONS". exact I. Qed.\n'
        'Print Assumptions CPUISAInstructionExecution.token_execute.\n')
    bc, bt = run_stage([str(origin.ROOT / '_opam/bin/coqc'), *flags, str(baseline.resolve())], out / 'baseline.log', 1200)
    allowed = parse_assumptions(bc.stdout) if bc.returncode == 0 else set()
    result = dict(accepted=bc.returncode == 0 and not(allowed - ALLOWED_AXIOMS),
                  baseline_coqc_exit=bc.returncode, baseline_assumptions=sorted(allowed), modules=[])
    modules = [('Lang/ExtendedSVRuntimeRelation', True, 1), ('Lang/ExtendedSVHistoryRepresentation', True, 2),
               ('Ex/External/CPUReferenceValues', True, 4),
               ('Ex/External/CPUISAAddReferenceValues', False, 5), ('Ex/External/CPUReferenceValuesRegression', True, 4),
               ('Lang/ExtendedSVValidCompanion', True, 2), ('Lang/ExtendedSVValidCompanionRegression', True, 4),
               ('Lang/ExtendedSVOppositeClock', True, 1), ('Lang/ExtendedSVOppositeClockRegression', True, 3),
               ('Lang/ExtendedSVClockBoundary', True, 2), ('Lang/ExtendedSVClockBoundaryRegression', True, 2),
               ('Lang/ExtendedSVPhaseIdle', True, 2), ('Lang/ExtendedSVExpressionObservation', True, 2),
               ('Lang/ExtendedSVSelectedCompanion', True, 5),
               ('Lang/ExtendedSVSelectedCompanionRegression', True, 3),
               ('Ex/External/CPUReferenceProducerBatches', False, 15),
               ('Ex/External/CPUReferenceProducerBatchesRegression', True, 6),
               ('Ex/External/CPUOriginalInstructionSuccess', False, 5),
               ('Ex/External/CPUReferenceLedgerExtension', True, 4),
               ('Lang/ExtendedSVExpressionFold', True, 3),
               ('Lang/ExtendedSVInvalidPayload', True, 6),
               ('Ex/External/CPUOriginalADDFrontier', False, 4),
               ('Ex/External/CPUByteBankRelation', False, 3),
               ('Lang/ExtendedSVCaptureClass', True, 3),
               ('Ex/External/CPUISAAddiFields', True, 2),
               ('Ex/External/CPUISAAddiEffects', False, 2),
               ('Ex/External/CPUISAAddFamilyReferenceValues', False, 6),
               ('Ex/External/CPUReferenceAddFamilyProducers', False, 5),
               ('Ex/External/CPUOriginalADDIFetchRules', False, 2),
               ('Ex/External/CPUQueueCreditProgress', True, 3),
               ('Ex/External/CPUISAControlFamilyReferenceValues', False, 8),
               ('Ex/External/CPUISAJalSuccessEffects', False, 3),
               ('Ex/External/CPUISAJalSuccessfulState', False, 3),
               ('Ex/External/CPUReferenceControlFamilyProducers', False, 6)]
    if selected is not None:
        unknown = set(selected) - {name for name, _, _ in modules}
        if unknown:
            raise ValueError('unknown rule modules: ' + ', '.join(sorted(unknown)))
        modules = [row for row in modules if row[0] in selected]
    result['selected_modules'] = [name for name, _, _ in modules]
    for name, closed, exports in modules:
        target = origin.ROOT / 'src' / (name + '.v')
        folder = out / Path(name).name
        folder.mkdir()
        start = time.monotonic()
        cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str((folder / 'coqc.resources').resolve()),
            str(origin.ROOT / '_opam/bin/coqc'), '-time', *flags, str(target)], folder / 'coqc.log', 1200)
        ax = audit_all_exports(cc.stdout, exports) if cc.returncode == 0 else set()
        audit = cc.returncode == 0 and not(ax if closed else ax - allowed)
        row = dict(module=name, source_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
            coqc_exit=cc.returncode, coqc_timed_out=timed, assumptions=sorted(ax),
            closed_required=closed, assumptions_audit_passed=audit, accepted=False)
        if cc.returncode == 0:
            kk, timed = run_stage(['/usr/bin/time', '-v', '-o', str((folder / 'coqchk.resources').resolve()),
                str(origin.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec', 'Pfv.' + name.replace('/', '.')],
                folder / 'coqchk.log', max(.1, 1200 - (time.monotonic() - start)))
            row.update(coqchk_exit=kk.returncode, coqchk_timed_out=timed, accepted=audit and kk.returncode == 0)
            if row['accepted']:
                row['object_sha256']=hashlib.sha256(target.with_suffix('.vo').read_bytes()).hexdigest()
        row['seconds'] = time.monotonic() - start
        result['modules'].append(row)
        result['accepted'] = result['accepted'] and row['accepted']
        (out / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True)
    p.add_argument('--module', action='append', help='check only named registered modules; omit for all')
    a = p.parse_args()
    r = check(a.output, a.module)
    print(json.dumps(r, indent=2))
    raise SystemExit(0 if r['accepted'] else 1)
