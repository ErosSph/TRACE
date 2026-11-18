#!/usr/bin/env python3
"""Stage-major template-route DRIVER (S1): one command per design, driven by the manifest.

    python tools/cpu_tmpl_route.py --design D [--stages a,b,..] [--dry-run] [--gen-only] [--tag aN] [--resume]

The manifest framework/auto-contract-profiles/<D>.json carries a top-level `route` object
(every design-specific choice lives there, none in this file):
  route.date                  stamp used in the result directory name
  route.env                   environment for every generator (e.g. {"TMPL_RST_IDLE": "0"} for an active-high reset)
  route.stages[]              in order; each stage:
      name        stage id (used by --stages, by {mod:X}/{dir:X}, and as sub-directory)
      layer       lfp | edge | reset | stage | frame | target | cycle | value | ctl | imm | rf | ram | wire | next | fetch | domain | ...
      module, namespace       Coq module / namespace of the generated module
      cmd         argv of a TEXT-MODE generator (writes the module text to {out}); placeholders:
                  {design} {module} {namespace} {out} {mod:S} (= NS.Mod.Mod of stage S) {modq:S} (= NS.Mod) {dir:S}
      env         extra environment for this generator
      text_sub    [[old,new],..] textual replacements applied to the generated text (documented generator gaps)
      needs       stages whose result dirs are Coq providers (default: all earlier stages of the route)
      ref         an already accepted result dir with identical expected text (regression reference)
      provenance  automatic | generalized_rule | llm_adapted | llm_written
      generator   text recorded in the report
      optional    true: a failure is recorded but does not stop the route
Every stage is generated, then gated by cpu_tmpl_accept.accept with TMPL_DEFER_COQCHK=1 (coqc + assumption audit now,
coqchk deferred to tools/cpu_tmpl_coqchk_batch.py).  The route stops at the first real failure.  Output:
results/route-<design>-<date>[-<tag>]/<stage>/ (module dirs) and .../route.json (accepted module per stage, wall time,
regression result) which the lift and closure agents consume.
Rule library (additive, claude-opus-5-5): --match-rules runs every pattern of framework/rule-library.json on the design and prints
the matched rules, the stages they cover, the residual obligations and the validation against the hand-written route;
--apply-rules runs the route with rst_idle and the rule-covered stages filled from the matches (uncovered stages stay as
hand-written residual stages, flagged `residual`); --rule-variant RULE=VARIANT picks a declared rule variant.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLS = ROOT / 'tools'
PROFILE = ROOT / 'framework' / 'auto-contract-profiles'
LEDGER = ROOT / 'framework' / 'template-route-ledger.json'
AUTHOR = 'LLM-generated: Claude Code (claude-sonnet-5-5)'
MARK = 'Goal True. idtac "TMPL_AUDIT_BEGIN". exact I. Qed.\n'


def load_manifest(design):
    m = json.loads((PROFILE / f'{design}.json').read_text())
    if 'route' not in m:
        raise SystemExit(f'{design}: manifest has no `route` section')
    return m


def exports_of(text):
    return re.findall(r'^Print Assumptions (\S+?)\.\s*$', text, flags=re.M)


def statements(text, names):
    """name -> whitespace-normalised statement (text between the keyword and the first `Proof`) of every exported theorem"""
    out = {}
    for n in names:
        short = n.split('.')[-1]
        m = re.search(r'^(?:Theorem|Lemma|Corollary)\s+' + re.escape(short) + r'\b(.*?)(?=\bProof\b)', text, flags=re.M | re.S)
        out[n] = ' '.join(m.group(1).split()) if m else None
    return out


def strip_mark(t):
    return t.replace(MARK, '')


def compare(text, ref_dir, module):
    ref = Path(ref_dir) / f'{module}.v'
    if not ref.exists():
        return dict(ref=str(ref_dir), error='reference module file missing')
    rt = ref.read_text()
    names = exports_of(text)
    a, b = statements(text, names), statements(rt, names)
    same = sum(1 for n in names if a[n] is not None and a[n] == b[n])
    return dict(ref=str(ref_dir), text_identical=strip_mark(text) == strip_mark(rt), exports=len(names), statements_equal=same,
                statements_missing=sorted(n for n in names if a[n] is None or b[n] is None),
                statements_different=sorted(n for n in names if a[n] is not None and b[n] is not None and a[n] != b[n]))


class Route:
    def __init__(self, design, tag, stages_sel, resume, cfg=None):
        self.design = design
        self.man = load_manifest(design) if cfg is None else json.loads((PROFILE / f'{design}.json').read_text())
        self.cfg = self.man['route'] if cfg is None else cfg      # cfg: rule-derived route (--apply-rules)
        self.date = self.cfg.get('date', time.strftime('%Y%m%d'))
        self.rname = f'route-{design}-{self.date}' + (f'-{tag}' if tag else '')
        self.rdir = ROOT / 'results' / self.rname
        self.stages = self.cfg['stages']
        names = [s['name'] for s in self.stages]
        if stages_sel:
            bad = [x for x in stages_sel if x not in names and x not in {s.get('layer') for s in self.stages}]
            if bad:
                raise SystemExit(f'unknown stage/layer {bad}; stages: {names}')
        self.sel = stages_sel
        self.done = {}      # name -> route.json stage record (accepted in this route dir)
        self.resume = resume
        rj = self.rdir / 'route.json'
        if rj.exists() and (resume or stages_sel):
            old = json.loads(rj.read_text())
            self.done = {s['name']: s for s in old.get('stages', []) if s.get('status') in ('coqc_accepted', 'accepted')}
        self.records = list(self.done.values())

    def selected(self, s):
        return (not self.sel) or s['name'] in self.sel or s.get('layer') in self.sel

    def dir_of(self, name):
        if name in self.done:
            return self.done[name]['dir']
        st = next(s for s in self.stages if s['name'] == name)
        if st.get('ref'):
            return st['ref']
        raise SystemExit(f'stage {name} is needed as a provider but neither accepted in {self.rname} nor has a ref')

    def sub(self, arg, st):
        def one(m):
            k, _, v = m.group(1).partition(':')
            if k == 'design':
                return self.design
            if k in ('module', 'namespace', 'out'):
                return st['_out'] if k == 'out' else st[k]
            tgt = next(s for s in self.stages if s['name'] == v)
            if k == 'mod':
                return f"{tgt['namespace']}.{tgt['module']}.{tgt['module']}"
            if k == 'modq':
                return f"{tgt['namespace']}.{tgt['module']}"
            if k == 'dir':
                return self.dir_of(v)
            raise SystemExit(f'bad placeholder {m.group(0)}')
        return re.sub(r'\{([^{}]+)\}', one, arg)

    def providers(self, st, idx):
        needs = st.get('needs')
        if needs is None:
            needs = [s['name'] for s in self.stages[:idx] if s.get('provider', True)]
        out = []
        for n in needs:
            tgt = next(s for s in self.stages if s['name'] == n)
            out.append(dict(namespace=tgt['namespace'], directory=str(Path(self.dir_of(n)).resolve())))
        return out

    def generate(self, st, idx, scratch):
        st['_out'] = str(scratch / f"{st['name']}.v")
        argv = [sys.executable] + [self.sub(a, st) for a in st['cmd']]
        env = dict(os.environ, PYTHONPATH=str(TOOLS))
        if 'rst_idle' in self.cfg:      # level of the primary reset input in operation (0 for an active-high reset)
            env['TMPL_RST_IDLE'] = str(self.cfg['rst_idle'])
        env.update({k: str(v) for k, v in {**self.cfg.get('env', {}), **st.get('env', {})}.items()})
        t0 = time.monotonic()
        r = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, text=True)
        gen_s = time.monotonic() - t0
        if r.returncode != 0:
            return None, argv, gen_s, (r.stdout + r.stderr)[-3000:]
        text = Path(st['_out']).read_text()
        for old, new in st.get('text_sub', []):
            if old not in text:
                return None, argv, gen_s, f'text_sub pattern not found: {old!r}'
            text = text.replace(old, new)
        return text, argv, gen_s, ''

    def write(self, total, failed=None):
        self.rdir.mkdir(parents=True, exist_ok=True)
        order = [s['name'] for s in self.stages]
        recs = sorted(self.records, key=lambda r: order.index(r['name']) if r['name'] in order else 99)
        accepted = {r['name']: r['module'] for r in recs if r['status'] in ('coqc_accepted', 'accepted')}
        j = dict(design=self.design, route=self.rname, date=self.date, proof_author=AUTHOR, external_llm_api_calls=0,
                 coqchk='deferred (tools/cpu_tmpl_coqchk_batch.py)', accepted_modules=accepted, stages=recs,
                 wall_seconds_total=round(sum(r.get('wall_seconds', 0) for r in recs), 1), failed=failed,
                 manifest_sha256=hashlib.sha256((PROFILE / f'{self.design}.json').read_bytes()).hexdigest())
        (self.rdir / 'route.json').write_text(json.dumps(j, indent=1) + '\n')


def ledger_add(entry):
    led = json.loads(LEDGER.read_text())
    led['modules'] = [m for m in led['modules'] if m.get('id') != entry['id']] + [entry]
    LEDGER.write_text(json.dumps(led, indent=1) + '\n')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--design', required=True)
    ap.add_argument('--stages', help='comma list of stage names or layers (default: all)')
    ap.add_argument('--dry-run', action='store_true', help='print the plan (commands, providers, refs); generate and gate nothing')
    ap.add_argument('--gen-only', action='store_true', help='generate the module texts and compare them with the refs; no Coq')
    ap.add_argument('--tag', default='', help='suffix of the route directory (a new run needs a new tag or date)')
    ap.add_argument('--resume', action='store_true', help='keep stages already accepted in the route directory')
    ap.add_argument('--skip-deps', action='store_true', help='do not rebuild the generic libraries before the first gate')
    ap.add_argument('--no-ledger', action='store_true')
    ap.add_argument('--match-rules', action='store_true', help='run the rule patterns on the design: matched rules, covered stages, residual obligations, validation')
    ap.add_argument('--apply-rules', action='store_true', help='fill rst_idle and the rule-covered stages from the rule matches (default tag: rules)')
    ap.add_argument('--rule-variant', action='append', default=[], help='RULE=VARIANT of a declared rule variant (e.g. reset_level=asserted_level_plus_reset_layer)')
    ap.add_argument('--json', action='store_true', help='with --match-rules: JSON output')
    a = ap.parse_args()
    os.chdir(ROOT)
    os.environ['TMPL_DEFER_COQCHK'] = '1'
    os.environ['TMPL_SKIP_DEPS'] = '1'
    sys.path.insert(0, str(TOOLS))
    cfg = None
    if a.match_rules or a.apply_rules:
        import cpu_rule_match as RM
        variants = dict(v.split('=', 1) for v in a.rule_variant)
        if a.match_rules:
            RM.report(a.design, variants, a.json, write=True)
            return 0
        lib = RM.load_library()
        _, ms = RM.match(a.design, lib)
        der = RM.derive(a.design, ms, lib, variants)
        cfg = RM.apply_cfg(a.design, der)
        RM.DERIVED.mkdir(parents=True, exist_ok=True)
        (RM.DERIVED / f'{a.design}.apply.json').write_text(json.dumps(cfg, indent=1) + '\n')
        print(f"apply-rules: rst_idle={cfg['rst_idle']} rule stages {cfg['rule_stages']} residual (hand-written) stages {cfg['residual_stages']}"
              f" hand fields kept {cfg.get('hand_fields_kept', [])}; residual obligations {[r['layer'] for r in cfg['residual_obligations']]}", flush=True)
        if not cfg['stages']:
            raise SystemExit('apply-rules: no runnable stage')
        a.tag = a.tag or 'rules'
    R = Route(a.design, a.tag, a.stages.split(',') if a.stages else None, a.resume, cfg)
    scratch = Path(os.environ.get('TMPL_ROUTE_SCRATCH', '/tmp')) / f'route-{os.getpid()}'
    scratch.mkdir(parents=True, exist_ok=True)
    t_all = time.monotonic()
    if a.dry_run:
        for i, st in enumerate(R.stages):
            if not R.selected(st):
                continue
            st['_out'] = '<out>'
            try:
                pv = [p['namespace'] for p in R.providers(st, i)]
            except SystemExit as e:
                pv = [f'? {e}']
            print(json.dumps(dict(stage=st['name'], layer=st.get('layer'), module=f"{st['namespace']}.{st['module']}", cmd=[R.sub(x, st) if '{dir:' not in x else x for x in st['cmd']],
                                  env={**R.cfg.get('env', {}), **st.get('env', {})}, providers=pv, ref=st.get('ref'))))
        return 0
    if not a.gen_only and not a.skip_deps:
        import cpu_tmpl_accept as acc
        t0 = time.monotonic()
        acc.ensure_generic_deps()
        print(f'generic libraries built/checked in {time.monotonic() - t0:.0f} s', flush=True)
    failed = None
    for i, st in enumerate(R.stages):
        if not R.selected(st) or st['name'] in R.done:
            continue
        t0 = time.monotonic()
        text, argv, gen_s, err = R.generate(st, i, scratch)
        rec = dict(name=st['name'], layer=st.get('layer'), module=f"{st['namespace']}.{st['module']}", namespace=st['namespace'],
                   dir=str(R.rdir / st['name']), provenance=st.get('provenance'), generator=st.get('generator'),
                   cmd=argv[1:], gen_seconds=round(gen_s, 1))
        if st.get('rules') or st.get('residual'):      # --apply-rules provenance of the stage fields
            rec.update(rules=st.get('rules'), residual=bool(st.get('residual')))
        if text is None:
            rec.update(status='generator_failed', error=err, wall_seconds=round(time.monotonic() - t0, 1))
            R.records.append(rec)
            print(f"[{st['name']}] GENERATOR FAILED\n{err}", flush=True)
            if st.get('optional'):
                continue
            failed = st['name']
            break
        exports = exports_of(text)
        rec['exports'] = len(exports)
        if st.get('ref'):
            rec['regression'] = compare(text, st['ref'], st['module'])
            print(f"[{st['name']}] regression vs {st['ref']}: {json.dumps({k: v for k, v in rec['regression'].items() if k != 'ref'})}", flush=True)
        if a.gen_only:
            rec.update(status='generated', wall_seconds=round(time.monotonic() - t0, 1))
            R.records.append(rec)
            continue
        import cpu_tmpl_accept as acc
        prof = json.loads((PROFILE / f'{a.design}.json').read_text())
        ast = prof['pipeline_roles']['ast']
        lp = [(ast['file'].rsplit('/', 1)[0], ast['module'].split('.')[0])]
        out = R.rdir / st['name']
        R.rdir.mkdir(parents=True, exist_ok=True)
        extra = dict(generator=st.get('generator') or argv[1], design=a.design, route=R.rname, stage=st['name'], layer=st.get('layer'))
        try:
            r = acc.accept(out, st['namespace'], st['module'], text, exports,
                           lp, providers=R.providers(st, i), extra=extra, timeout=st.get('timeout', 3600))
        except SystemExit as e:
            r = dict(accepted=False, coqc_accepted=False, error=str(e), coqc_seconds=0)
        except Exception as e:     # keep the evidence of a failed gate
            r = dict(accepted=False, coqc_accepted=False, error=repr(e), coqc_seconds=0)
        ok = bool(r.get('accepted') or r.get('coqc_accepted'))
        rec.update(status=('coqc_accepted' if ok else 'failed'), coqc_seconds=round(r.get('coqc_seconds', 0), 1), coqc_peak_rss_kb=r.get('coqc_peak_rss_kb'),
                   assumptions=r.get('assumptions'), coqchk_deferred=True, wall_seconds=round(time.monotonic() - t0, 1), error=r.get('error'),
                   source_sha256=r.get('source_sha256'))
        R.records.append(rec)
        if ok:
            R.done[st['name']] = rec
        R.write(time.monotonic() - t_all)
        print(f"[{st['name']}] {rec['status']} coqc {rec['coqc_seconds']} s wall {rec['wall_seconds']} s", flush=True)
        if not a.no_ledger:
            ledger_add(dict(id=f"{a.design}-route-{st['name']}-{R.rname}", kind='generated', generator=extra['generator'], result_dir=str(out.relative_to(ROOT)),
                            provenance=st.get('provenance', 'automatic'), accepted=False, coqc_accepted=ok, coqchk_deferred=True,
                            coqc_seconds=rec['coqc_seconds'], design=a.design, via='tools/cpu_tmpl_route.py',
                            note=(st.get('note') or '') + ' (driver regression)' if st.get('ref') else st.get('note', '')))
        if not ok and not st.get('optional'):
            failed = st['name']
            break
    R.write(time.monotonic() - t_all, failed)
    tot = sum(r.get('wall_seconds', 0) for r in R.records)
    print(f"route {R.rname}: {'FAILED at ' + failed if failed else 'ok'}; stages {len(R.records)}; summed stage wall {tot:.0f} s; elapsed {time.monotonic() - t_all:.0f} s")
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
