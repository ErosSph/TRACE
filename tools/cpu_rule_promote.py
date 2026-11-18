#!/usr/bin/env python3
"""PROMOTION check: turn LLM-solved residual work into a rule of framework/rule-library.json.

    python tools/cpu_rule_promote.py framework/rule-candidates/<name>.json [--no-gate] [--write] [--tag aN]

A candidate (same fields as a library rule plus `gate`) is ACCEPTED only if all three checks pass:
 1. generic   its Coq libraries and its generator contain no design-specific signal ids or names
              (scan_coq / scan_python below; comments and docstrings are ignored; argparse defaults and file names
              are reported as warnings, not failures);
 2. pattern   its pattern function (tools/cpu_rule_patterns.py) matches the design it came from (`learned_from`), and
              every route field the rule instantiates (gate.route_field_check) is RE-DERIVED equal to the hand-written one;
 3. gate      its generated output for that design passes the gate of tools/cpu_tmpl_accept.accept (coqc + assumption audit;
              coqchk deferred and registered, TMPL_DEFER_COQCHK=1).  A library-only candidate is gated by a probe module that
              Requires the library and prints the assumptions of its theorems.
--write appends an accepted candidate to the library (status promoted, with the evidence directory).  The report is
written to results/rule-promote-<name>-<date>[-tag]/promote.json.  No Admitted, no axioms are introduced (the audit checks it).
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0.
"""
import argparse
import io
import json
import os
import re
import subprocess
import sys
import time
import tokenize
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_rule_patterns as P

ROOT = P.ROOT
LIBRARY = ROOT / 'framework' / 'rule-library.json'
DESIGNS = ['bzeeno', 'darkriscv', 'steel', 'srv32', 'nerv', 'angelo5fix', 'cv32e40p', 'picorv32']
DESIGN_WORDS = re.compile(r'\b(steel|srv32|nerv|angelo5\w*|a5|bzeeno|bz|darkriscv|dark\w*|cv32e40p|cv|picorv32|pico)\b', re.I)
# small integers that are widths / counts / masks rather than signal ids
COMMON = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 20, 24, 25, 30, 31, 32, 33, 63, 64, 100, 127, 128, 255, 256, 511, 512,
          1000, 1023, 1024, 2047, 2048, 3000, 4095, 4096}
COQ_SIG = [re.compile(r'EVar\s+\(?\d+%?n?a?t?\)?\s+\(?(\d+)%nat'), re.compile(r'read_signal\s+\S+\s+\(?(\d+)%nat'), re.compile(r'LVar\s+\d+\s+(\d+)%nat'),
           re.compile(r'write_signal\s+\S+\s+(\d+)%nat')]


def strip_coq_comments(t):
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i):
            depth += 1; i += 2; continue
        if depth and t.startswith('*)', i):
            depth -= 1; i += 2; continue
        if not depth:
            out.append(t[i])
        i += 1
    return ''.join(out)


def signal_ids(design):
    try:
        return set(P.Ctx(design).sigtab)
    except Exception:
        return set()


def signal_names(design):
    try:
        return {r['path'].split('.')[-1] for r in P.Ctx(design).sigtab.values() if len(r['path'].split('.')[-1]) >= 6 and '_' in r['path'].split('.')[-1]}
    except Exception:
        return set()


def scan_coq(path, design):
    t = strip_coq_comments(Path(path).read_text())
    ids, names = signal_ids(design), signal_names(design)
    hits = sorted({int(m.group(1)) for rx in COQ_SIG for m in rx.finditer(t)} - {0, 1} if True else [])
    words = sorted({m.group(0) for m in DESIGN_WORDS.finditer(t)})
    nm = sorted(n for n in names if re.search(r'\b' + re.escape(n) + r'\b', t))
    fails = []
    if hits:
        fails.append(f'literal signal ids in signal positions: {hits[:12]}')
    if words:
        fails.append(f'design names: {words[:8]}')
    if nm:
        fails.append(f'RTL signal names of {design}: {nm[:8]}')
    return dict(file=str(path), kind='coq', fails=fails, warnings=[])


def _py_code_tokens(src):
    """(type, string, line) of the tokens that are code (comments and docstring statements dropped)"""
    toks = list(tokenize.generate_tokens(io.StringIO(src).readline))
    out, prev_sig = [], None
    for i, tk in enumerate(toks):
        if tk.type == tokenize.COMMENT:
            continue
        if tk.type == tokenize.STRING and prev_sig in (None, tokenize.NEWLINE, tokenize.INDENT, tokenize.DEDENT, 'NL'):
            # a string that starts a statement is a docstring / bare string
            nxt = next((t for t in toks[i + 1:] if t.type not in (tokenize.NL, tokenize.COMMENT)), None)
            if nxt is None or nxt.type in (tokenize.NEWLINE, tokenize.ENDMARKER):
                prev_sig = tokenize.NEWLINE
                continue
        if tk.type in (tokenize.NL,):
            continue
        out.append(tk)
        prev_sig = tk.type
    return out


def scan_python(path, design):
    src = Path(path).read_text()
    ids, names = signal_ids(design), signal_names(design)
    toks = _py_code_tokens(src)
    fails, warns = [], []
    sig_in_str, ints, words, defaults = set(), [], set(), set()
    for k, tk in enumerate(toks):
        if tk.type == tokenize.STRING:
            for rx in COQ_SIG:
                for m in rx.finditer(tk.string):
                    sig_in_str.add(int(m.group(1)))
            for m in DESIGN_WORDS.finditer(tk.string):
                if k >= 2 and toks[k - 1].string == '=' and toks[k - 2].string == 'default':
                    defaults.add(m.group(0))
                else:
                    words.add(m.group(0))
            for n in names:
                if re.search(r'\b' + re.escape(n) + r'\b', tk.string):
                    words.add(n)
        elif tk.type == tokenize.NUMBER and tk.string.isdigit():
            v = int(tk.string)
            if v in ids and v not in COMMON:
                ints.append((v, tk.start[0]))
        elif tk.type == tokenize.NAME and DESIGN_WORDS.fullmatch(tk.string):
            words.add(tk.string)
    sig_in_str -= {0, 1}
    if sig_in_str:
        fails.append(f'literal signal ids inside Coq text: {sorted(sig_in_str)[:12]}')
    distinct = sorted({v for v, _ in ints})
    if len(distinct) >= 3:
        fails.append(f'{len(distinct)} integer literals equal to {design} signal ids (e.g. {distinct[:10]}, lines {sorted({l for _, l in ints})[:6]})')
    elif distinct:
        warns.append(f'integer literals equal to signal ids (likely widths/counts): {distinct}')
    if words:
        fails.append(f'design names in code/strings: {sorted(words)[:8]}')
    if defaults:
        warns.append(f'argparse default design {sorted(defaults)} (callers pass --design)')
    if any(DESIGN_WORDS.fullmatch(w) for w in re.split(r'[_\W]+', Path(path).stem)):
        warns.append(f'file name {Path(path).name} names a design (rename recommended when promoted)')
    return dict(file=str(path), kind='python', fails=fails, warnings=warns)


def content_files(cand):
    c = cand.get('content', {})
    libs = [x.split(' ')[0] for x in c.get('libraries', [])]
    gens = [x.split(' ')[0] for x in ([c['generator']] if c.get('generator') else []) + c.get('frontend', [])]
    return [ROOT / x for x in libs if x.endswith('.v')], [ROOT / x for x in gens if x.endswith('.py')]


def check_generic(cand):
    design = cand['learned_from']
    libs, gens = content_files(cand)
    res = [scan_coq(f, design) for f in libs if f.exists()] + [scan_python(f, design) for f in gens if f.exists()]
    missing = [str(f) for f in libs + gens if not f.exists()]
    ok = (not missing and all(not r['fails'] for r in res)) if res or missing else None     # None: nothing to scan
    return dict(ok=ok, files=res, missing=missing)


def check_pattern(cand):
    design = cand['learned_from']
    ctx = P.Ctx(design)
    f = getattr(P, cand['pattern']['function'], None)
    if f is None:
        return dict(ok=False, error=f"no pattern function {cand['pattern']['function']}")
    m = f(ctx)
    out = dict(ok=bool(m), design=design, match=m)
    fld = cand.get('gate', {}).get('route_field_check')
    if m and fld:
        full = json.loads((P.PROFILE / f'{design}.json').read_text())
        hand = (full.get('route') or {}).get(fld)
        out['route_field'] = dict(field=fld, hand_written=hand, derived=m.get(fld), equal=(hand == m.get(fld)))
        out['ok'] = out['ok'] and hand == m.get(fld)
    return out


def route_providers(design):
    """stage name -> record of the most recent accepted route dir of the design (providers for {mod:S}/{dir:S})"""
    best = None
    for rj in sorted((ROOT / 'results').glob(f'route-{design}-*/route.json')):
        j = json.loads(rj.read_text())
        if j.get('failed') or 'gen' in j['route'] or 'rules' in j['route']:
            continue
        if not all(s.get('status') == 'coqc_accepted' for s in j['stages']):
            continue
        if best is None or rj.stat().st_mtime > best[0]:
            best = (rj.stat().st_mtime, j)
    return {s['name']: s for s in best[1]['stages']} if best else {}


def gate(cand, tag, reuse=False):
    import cpu_tmpl_accept as acc
    design = cand['learned_from']
    g = cand.get('gate', {})
    stamp = time.strftime('%Y%m%d')
    out = ROOT / 'results' / (f"rule-promote-{cand['name'].replace('_', '-')}-{stamp}" + (f'-{tag}' if tag else ''))
    if reuse and (out / 'report.json').exists():     # an earlier gate of the same tag: reuse its evidence (no second coqc)
        r = json.loads((out / 'report.json').read_text())
        return dict(ok=bool(r.get('accepted') or r.get('coqc_accepted')), dir=str(out.relative_to(ROOT)), coqc_seconds=round(r.get('coqc_seconds', 0), 1),
                    assumptions=r.get('assumptions'), reused_gate=True, coqchk='deferred (registered)')
    os.environ['TMPL_DEFER_COQCHK'] = '1'
    man = json.loads((P.PROFILE / f'{design}.json').read_text())
    ast = man['pipeline_roles']['ast']
    lp = [(ast['file'].rsplit('/', 1)[0], ast['module'].split('.')[0])]
    t0 = time.monotonic()
    if cand['instantiate']['type'] == 'library':
        mod = g['library_module']
        src = (ROOT / 'src' / (mod.replace('.', '/') + '.v')).read_text()
        short = mod.split('.')[-1]
        thms = re.findall(r'^Theorem\s+(\w+)', strip_coq_comments(src), flags=re.M)
        module = f'Probe{short}'
        text = (f'(** promotion probe for {mod}.  proof_author: {P.AUTHOR}; external_llm_api_calls=0. *)\nRequire Import {mod}.\n'
                f'Module {module}.\nEnd {module}.\n' + ''.join(f'Print Assumptions {short}.{t}.\n' for t in thms))
        r = acc.accept(out, 'RulePromote', module, text, [f'{short}.{t}' for t in thms], lp, providers=[], extra=dict(design=design, rule=cand['name'], kind='library_probe'))
    else:
        prov = route_providers(design)
        ins = cand['instantiate']
        module, ns = g['module'], g['namespace']
        scratch = Path(os.environ.get('TMPL_ROUTE_SCRATCH', '/tmp')) / f'promote-{os.getpid()}'
        scratch.mkdir(parents=True, exist_ok=True)
        fo = scratch / f'{module}.v'

        def sub(a):
            def one(m):
                k, _, v = m.group(1).partition(':')
                if k == 'design':
                    return design
                if k == 'module':
                    return module
                if k == 'out':
                    return str(fo)
                s = prov[v]
                return {'mod': s['module'] + '.' + s['module'].split('.')[-1], 'modq': s['module'], 'dir': s['dir']}[k]
            return re.sub(r'\{([^{}]+)\}', one, a)
        argv = [sys.executable] + [sub(a) for a in ins['cmd']]
        rr = subprocess.run(argv, cwd=ROOT, env=dict(os.environ, PYTHONPATH=str(ROOT / 'tools')), capture_output=True, text=True)
        if rr.returncode != 0:
            return dict(ok=False, error='generator failed: ' + (rr.stdout + rr.stderr)[-1500:], cmd=argv[1:])
        text = fo.read_text()
        exports = re.findall(r'^Print Assumptions (\S+?)\.\s*$', text, flags=re.M)
        need = [n for n in prov if any(n2 in ' '.join(ins['cmd']) for n2 in (f'{{mod:{n}}}', f'{{modq:{n}}}', f'{{dir:{n}}}'))]
        providers = [dict(namespace=prov[n]['namespace'], directory=str(Path(prov[n]['dir']).resolve())) for n in prov]
        r = acc.accept(out, ns, module, text, exports, lp, providers=providers, extra=dict(design=design, rule=cand['name'], cmd=argv[1:]))
    ok = bool(r.get('accepted') or r.get('coqc_accepted'))
    return dict(ok=ok, dir=str(out.relative_to(ROOT)), coqc_seconds=round(r.get('coqc_seconds', 0), 1), assumptions=r.get('assumptions'),
                error=r.get('error'), wall_seconds=round(time.monotonic() - t0, 1), coqchk='deferred (registered)')


def audit_library(path=LIBRARY):
    """check 1 (genericity scan) and check 2 (pattern matches the learning design) for every rule already in the library"""
    lib = json.loads(Path(path).read_text())
    rows = []
    for r in lib['rules']:
        g = check_generic(r)
        if r['learned_from'] in P.GENERATED:
            try:
                pt = check_pattern(dict(r, gate={}))
            except Exception as e:
                pt = dict(ok=False, error=repr(e)[:200])
        else:
            pt = dict(ok=None, note=f"learned on {r['learned_from']} (not one of the six route designs)")
        rows.append(dict(rule=r['name'], kind=r['kind'], learned_from=r['learned_from'], generic=g['ok'],
                         generic_fails={Path(f['file']).name: f['fails'] for f in g['files'] if f['fails']},
                         generic_warnings={Path(f['file']).name: f['warnings'] for f in g['files'] if f['warnings']},
                         pattern_matches_origin=pt.get('ok'), note=pt.get('note') or pt.get('error')))
    return rows


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--audit-library':
        os.chdir(ROOT)
        rows = audit_library()
        out = ROOT / 'framework' / 'rule-library-audit.json'
        out.write_text(json.dumps(dict(proof_author=P.AUTHOR, external_llm_api_calls=0, date=time.strftime('%Y-%m-%dT%H:%M'), rules=rows), indent=1) + '\n')
        for r in rows:
            print(f"{r['rule']:24s} generic={r['generic']!s:5s} pattern@origin={r['pattern_matches_origin']!s:5s} {json.dumps(r['generic_fails'])[:140]}")
        print(f'written {out.relative_to(ROOT)}')
        return 0
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('candidate')
    ap.add_argument('--no-gate', action='store_true', help='checks 1 and 2 only (no Coq)')
    ap.add_argument('--write', action='store_true', help='append an accepted candidate to framework/rule-library.json')
    ap.add_argument('--tag', default='')
    ap.add_argument('--reuse-gate', action='store_true', help='reuse the gate evidence of an earlier run with the same tag')
    ap.add_argument('--build-deps', action='store_true', help='rebuild/re-check the generic libraries first (default: TMPL_SKIP_DEPS=1, as after a driver run)')
    a = ap.parse_args()
    os.chdir(ROOT)
    if not a.build_deps:
        os.environ['TMPL_SKIP_DEPS'] = '1'
    cand = json.loads(Path(a.candidate).read_text())
    lib = json.loads(LIBRARY.read_text())
    rep = dict(candidate=a.candidate, name=cand['name'], proof_author=P.AUTHOR, external_llm_api_calls=0, date=time.strftime('%Y-%m-%dT%H:%M'))
    if any(r['name'] == cand['name'] for r in lib['rules']):
        rep['already_in_library'] = True
    rep['generic'] = check_generic(cand)
    rep['pattern'] = check_pattern(cand)
    if a.no_gate:
        rep['gate'] = dict(ok=None, skipped=True)
    elif rep['generic']['ok'] and rep['pattern']['ok']:
        try:
            rep['gate'] = gate(cand, a.tag, a.reuse_gate)
        except Exception as e:
            rep['gate'] = dict(ok=False, error=repr(e)[:2000])
    else:
        rep['gate'] = dict(ok=None, skipped='checks 1/2 failed')
    rep['accepted'] = bool(rep['generic']['ok'] is True and rep['pattern']['ok'] and rep['gate'].get('ok'))
    print(json.dumps(rep, indent=1, default=str))
    od = ROOT / rep['gate']['dir'] if rep['gate'].get('dir') else ROOT / 'results' / f"rule-promote-{cand['name'].replace('_', '-')}-{time.strftime('%Y%m%d')}-{a.tag or 'nogate'}-report"
    od.mkdir(parents=True, exist_ok=True)
    (od / 'promote.json').write_text(json.dumps(rep, indent=1, default=str) + '\n')
    if a.write and rep['accepted'] and not rep.get('already_in_library'):
        rule = {k: v for k, v in cand.items() if k not in ('gate', 'proof_author')}
        rule.update(status='promoted', promotion=dict(date=rep['date'], evidence=str(od.relative_to(ROOT)), coqchk='deferred (registered)'))
        lib['rules'].append(rule)
        LIBRARY.write_text(json.dumps(lib, indent=1) + '\n')
        print(f"promoted: {cand['name']} appended to {LIBRARY.relative_to(ROOT)}")
    return 0 if rep['accepted'] else 1


if __name__ == '__main__':
    sys.exit(main())
