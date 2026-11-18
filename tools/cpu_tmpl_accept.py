#!/usr/bin/env python3
"""Acceptance gate for one generated template-route module ("double 0": coqc + coqchk, assumption audit).

Writes results/<dir>/{<Module>.v, coqc.log, coqchk.log, *.resources, providers.json, report.json}.
Accepted iff coqc exit 0, every exported theorem is closed or uses only functional extensionality,
and coqchk -norec on the module exits 0.
"""
import hashlib
import json
import os
import sys
import time
from pathlib import Path
import cpu_framework as framework
from cpu_certificate_acceptance import run_stage, ALLOWED_AXIOMS
from check_reference_value_rules import audit_all_exports

MARK = 'TMPL_AUDIT_BEGIN'
AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ensure_generic_deps():
    """Fresh-checkout step: build and kernel-check the generic template-route libraries (framework/template-route-deps.txt)."""
    import subprocess
    r = subprocess.run(['bash', 'tools/build_template_deps.sh'], cwd=framework.ROOT, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError('generic template-route libraries failed to build:\n' + r.stdout + r.stderr)


def accept(out, namespace, module, text, exports, loadpaths, providers=(), timeout=1800, extra=None, factcheck=True):
    if os.environ.get('TMPL_SKIP_DEPS') != '1':    # additive: the route driver builds the deps once per run
        ensure_generic_deps()
    fc = None
    if factcheck:    # non-vacuity of every literal fact list / premise conjunction (tools/cpu_tmpl_factcheck.py, z3)
        import cpu_tmpl_factcheck as FC
        sets = FC.scan(text)
        if sets:
            verdict = FC.check_sets(sets)
            bad = sorted(k for k, v in verdict.items() if v[0] != 'sat')
            if bad:
                raise SystemExit(f'factcheck: {len(bad)} of {len(sets)} fact sets of {module} are not satisfiable (vacuous): {bad[:5]}')
            fc = dict(sets=len(sets), unsat=0)
    out = Path(out)
    out.mkdir(parents=True, exist_ok=False)
    # The audit marker separates compilation chatter from the Print Assumptions block.
    marker = 'Goal True. idtac "' + MARK + '". exact I. Qed.\n'
    body = text.replace('\n' + 'Print Assumptions ', '\n' + marker + 'Print Assumptions ', 1) if marker not in text else text
    f = out / (module + '.v')
    f.write_text(body)
    flags = list(framework.FLAGS)
    for d, ns in loadpaths:
        flags += ['-R', d, ns]
    for row in providers:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), namespace]
    (out / 'providers.json').write_text(json.dumps(list(providers), indent=2) + '\n')
    start = time.monotonic()
    cc, ct = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'coqc.resources'), '_opam/bin/coqc', '-time', *flags, str(f)], out / 'coqc.log', timeout)
    t_coqc = time.monotonic() - start
    report = dict(accepted=False, module=namespace + '.' + module, coqc_exit=cc.returncode, coqc_timed_out=ct,
                  coqc_seconds=t_coqc, source_sha256=sha(f), proof_author=AUTHOR, external_llm_api_calls=0,
                  old_inv_read=False, exports=len(exports), loadpaths=[list(x) for x in loadpaths])
    if fc:
        report['factcheck'] = fc
    if extra:
        report.update(extra)
    if cc.returncode == 0:
        try:
            axioms = audit_all_exports(cc.stdout.split(MARK)[-1], len(exports))
        except ValueError as e:
            axioms = {'AUDIT_ERROR: ' + str(e)}
        chk = ['_opam/bin/coqchk', '-silent', *flags, '-norec', namespace + '.' + module]
        if os.environ.get('TMPL_DEFER_COQCHK') == '1':
            # Deferred mode: coqc (full, every proof checked) and the assumption audit run now; the
            # independent kernel re-check runs later in a parallel batch (tools/cpu_tmpl_coqchk_batch.py).
            # The module is NOT accepted until that batch records coqchk exit 0.
            report.update(assumptions=sorted(axioms), coqchk_deferred=True,
                          coqc_accepted=not (axioms - ALLOWED_AXIOMS), accepted=False,
                          object_sha256=sha(f.with_suffix('.vo')))
            import cpu_tmpl_coqchk_batch as B
            B.register(out, chk, timeout_hint=timeout)
        else:
            t0 = time.monotonic()
            kk, kt = run_stage(['/usr/bin/time', '-v', '-o', str(out / 'coqchk.resources'), *chk],
                               out / 'coqchk.log', timeout)
            report.update(assumptions=sorted(axioms), coqchk_exit=kk.returncode, coqchk_timed_out=kt,
                          coqchk_seconds=time.monotonic() - t0,
                          accepted=kk.returncode == 0 and not (axioms - ALLOWED_AXIOMS))
            if report['accepted']:
                report['object_sha256'] = sha(f.with_suffix('.vo'))
    report['seconds'] = time.monotonic() - start
    for stage in ('coqc', 'coqchk'):
        r = out / (stage + '.resources')
        if r.exists():
            for line in r.read_text().splitlines():
                if 'Maximum resident set size' in line:
                    report[stage + '_peak_rss_kb'] = int(line.split(':')[-1])
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report
