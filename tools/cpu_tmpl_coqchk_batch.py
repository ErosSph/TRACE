#!/usr/bin/env python3
"""Deferred kernel re-check (coqchk) for template-route gates, run as a parallel batch.

Development mode (user decision 2026-11-04): gates run full coqc (every proof checked) and the
assumption audit immediately, register the coqchk command here, and continue. A module counts as
accepted ("double 0") only after this batch records coqchk exit 0 in its report.json.

  register:  called by the gate (cpu_tmpl_accept.accept with TMPL_DEFER_COQCHK=1), or by hand:
             python tools/cpu_tmpl_coqchk_batch.py register <result_dir> -- <coqchk argv...>
  run:       python tools/cpu_tmpl_coqchk_batch.py run --parallel 8 [--min-free-gb 120]
  status:    python tools/cpu_tmpl_coqchk_batch.py status
The .vo files a result depends on must not be rebuilt between coqc and coqchk; result dirs are
immutable, and the batch re-hashes the module's .vo against the hash recorded at coqc time.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PENDING = ROOT / 'framework' / 'coqchk-pending.txt'
ALLOWED = {'FunctionalExtensionality.functional_extensionality_dep'}


def register(out, argv, timeout_hint=None):
    out = Path(out).resolve()
    (out / 'coqchk_cmd.json').write_text(json.dumps(dict(argv=list(argv), cwd=str(ROOT),
                                                         timeout_hint=timeout_hint), indent=2) + '\n')
    rel = str(out.relative_to(ROOT))
    lines = PENDING.read_text().split() if PENDING.exists() else []
    if rel not in lines:
        with open(PENDING, 'a') as fh:
            fh.write(rel + '\n')


def free_gb():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) / 1024 / 1024
    return 0.0


def state(d):
    rep = d / 'report.json'
    if not rep.exists():
        return 'no-report'
    r = json.loads(rep.read_text())
    if r.get('accepted'):
        return 'accepted'
    if 'coqchk_exit' in r and r.get('coqchk_exit') != 0:
        return 'coqchk-failed'
    if r.get('coqchk_deferred') and not r.get('coqc_accepted', True):
        return 'coqc-rejected'
    if r.get('coqchk_deferred') or (d / 'coqchk_cmd.json').exists():
        return 'pending'
    return 'other'


def check_one(d, min_free):
    cmd = json.loads((d / 'coqchk_cmd.json').read_text())
    rep_path = d / 'report.json'
    r = json.loads(rep_path.read_text())
    vo = sorted(d.glob('*.vo'))
    if r.get('object_sha256') and vo and hashlib.sha256(vo[0].read_bytes()).hexdigest() != r['object_sha256']:
        r.update(coqchk_exit=-2, coqchk_error='module .vo changed since coqc')
        rep_path.write_text(json.dumps(r, indent=2) + '\n')
        return d, 'vo-changed'
    while free_gb() < min_free:
        time.sleep(30)
    t0 = time.monotonic()
    with open(d / 'coqchk.log', 'w') as log:
        p = subprocess.run(['/usr/bin/time', '-v', '-o', str(d / 'coqchk.resources'), *cmd['argv']],
                           cwd=cmd['cwd'], stdout=log, stderr=subprocess.STDOUT)
    r = json.loads(rep_path.read_text())
    r.update(coqchk_exit=p.returncode, coqchk_seconds=time.monotonic() - t0, coqchk_deferred_batch=True)
    res = d / 'coqchk.resources'
    if res.exists():
        for line in res.read_text().splitlines():
            if 'Maximum resident set size' in line:
                r['coqchk_peak_rss_kb'] = int(line.split(':')[-1])
    axioms = set(r.get('assumptions') or [])
    r['accepted'] = p.returncode == 0 and r.get('coqc_exit', 0) == 0 and r.get('coqc_accepted', True) \
        and not (axioms - ALLOWED)
    rep_path.write_text(json.dumps(r, indent=2) + '\n')
    return d, 'accepted' if r['accepted'] else 'coqchk-failed'


def pending_dirs():
    if not PENDING.exists():
        return []
    return [ROOT / x for x in dict.fromkeys(PENDING.read_text().split())]


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    rg = sub.add_parser('register')
    rg.add_argument('dir')
    rg.add_argument('argv', nargs=argparse.REMAINDER)
    rn = sub.add_parser('run')
    rn.add_argument('--parallel', type=int, default=8)
    rn.add_argument('--min-free-gb', type=float, default=120)
    sub.add_parser('status')
    a = ap.parse_args()
    if a.cmd == 'register':
        argv = a.argv[1:] if a.argv[:1] == ['--'] else a.argv
        register(a.dir, argv)
    elif a.cmd == 'status':
        for d in pending_dirs():
            print(f'{state(d):14} {d.relative_to(ROOT)}')
    else:
        todo = [d for d in pending_dirs() if state(d) == 'pending']
        print(f'{len(todo)} pending, parallel {a.parallel}', flush=True)
        with ThreadPoolExecutor(a.parallel) as ex:
            for d, s in ex.map(lambda d: check_one(d, a.min_free_gb), todo):
                print(f'{s:14} {d.relative_to(ROOT)}', flush=True)
