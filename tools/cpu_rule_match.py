#!/usr/bin/env python3
"""Rule MATCHER of the reuse library (framework/rule-library.json + tools/cpu_rule_patterns.py).

Used by the driver:  python tools/cpu_tmpl_route.py --design D --match-rules [--json]
                     python tools/cpu_tmpl_route.py --design D --apply-rules [--dry-run|--gen-only|...] [--rule-variant reset_level=...]
or directly:         python tools/cpu_rule_match.py --design D [--json] [--write]

match(D)            runs every rule's pattern on D (manifest WITHOUT its route section)
derive(D, ms)       turns the matches into route fields + stages (canonical stage order) and lists the RESIDUAL obligations
                    (layers no rule covers; for the control layers the matched engine rules are given as hints)
validate(D, der)    compares the derived route with the hand-written manifest route (or, for designs without a route
                    section, with the generators the ledger records), field by field
apply_cfg(D, der)   the route cfg the driver runs with --apply-rules: rule-covered stages take cmd/env from the rules,
                    uncovered stages stay as hand-written residual stages (flagged), rst_idle comes from the rule
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0.
"""
import argparse
import copy
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_rule_patterns as P

ROOT = P.ROOT
LIBRARY = ROOT / 'framework' / 'rule-library.json'
LEDGER = ROOT / 'framework' / 'template-route-ledger.json'
DERIVED = ROOT / 'framework' / 'rule-derived-routes'
# layers that, when no rule produces them, are residual obligations of a full route (with the reason)
RESIDUAL_LAYERS = {
    'target': 'boot/reset target (concrete reset sequence and observer of the design): design-specific',
    'cycle': 'cycle composition / register values on the driven state',
    'fetch': 'fetch link (instruction memory read = ROM word)',
    'ctl': 'per-class control and datapath facts',
    'domain': 'domain premises (misaligned / trap = 0 from check_program)',
    'lift': 'ISA lift of the provider facts',
    'closure': 'INV + rank + D step + final theorem',
}


def load_library(path=LIBRARY):
    # candidates (framework/rule-candidates/) are NOT part of the library until tools/cpu_rule_promote.py --write appends them
    return json.loads(Path(path).read_text())


def rules_by_name(lib):
    return {r['name']: r for r in lib['rules']}


def match(design, lib=None):
    lib = lib or load_library()
    names = sorted({r['pattern']['function'] for r in lib['rules']})
    ctx, res = P.run_all(design, names)
    out = []
    for r in lib['rules']:
        m = res.get(r['pattern']['function'])
        if m and 'error' not in m:
            out.append(dict(rule=r['name'], kind=r['kind'], bind=m, covers=r.get('covers', []), learned_from=r['learned_from']))
        elif m and 'error' in m:
            out.append(dict(rule=r['name'], kind=r['kind'], error=m['error']))
    return ctx, out


def _camel(design):
    return ''.join(p[:1].upper() + p[1:] for p in re.split(r'[^A-Za-z0-9]', design) if p)


def _expand(cmd, bind, gen):
    out = []
    for a in cmd:
        if a == '{args}':
            out += list(bind.get('extra_args', []))
            continue
        if a == '{gen}':
            out.append(gen)
            continue
        m = re.fullmatch(r'\{b:([a-z_]+)\}', a)
        if m:
            v = bind.get(m.group(1))
            out.append(','.join(map(str, v)) if isinstance(v, list) else str(v))
            continue
        out.append(a)
    return out


def derive(design, ms, lib=None, variants=None):
    """route fields + stages from the matches; returns dict(rst_idle, fields, stages, proposals, residual, engines, frontend, closure, lift)"""
    lib = lib or load_library()
    R = rules_by_name(lib)
    order = lib['stage_order']
    variants = dict(variants or {})
    got = {m['rule']: m for m in ms if 'bind' in m}
    der = dict(design=design, fields={}, stages=[], proposals=[], residual=[], engines=[], frontend=[], closure=None, lift=[], notes=[])
    # route fields
    if 'reset_level' in got:
        v = variants.get('reset_level', R['reset_level']['instantiate']['default_variant'])
        b = got['reset_level']['bind']
        der['fields']['rst_idle'] = b['rst_idle'] if v == 'idle_level' else 1
        der['fields']['_reset_variant'] = v
        der['fields']['_rst_rule'] = f"reset_level[{v}] ({b['evidence']})"
        if v == 'asserted_level_plus_reset_layer' and b['polarity'] == 'high' and 'reset_events_layer' not in got:
            got['reset_events_layer'] = dict(rule='reset_events_layer', bind=dict(evidence='variant asserted_level_plus_reset_layer of reset_level'))
    else:
        der['fields']['rst_idle'] = 1
        der['fields']['_rst_rule'] = 'default (no reset test recognised)'
    # stages from stage / variant_stage rules
    st = {}
    for name, m in got.items():
        ins = R[name]['instantiate']
        b = m['bind']
        if ins['type'] == 'stage':
            gen = b.get('generator') or R[name]['content'].get('generator', '').split(' ')[0]
            s = dict(name=ins['name'], layer=ins['layer'], cmd=_expand(ins['cmd'], b, gen), provenance=ins.get('provenance', 'automatic'),
                     rules=[name], runnable=ins.get('runnable', True), evidence=b['evidence'])
            if 'derived_fields' in ins:
                s['derived'] = {k: b.get('convertible') for k in ins['derived_fields']}
            for fld, key in ins.get('route_fields', {}).items():     # route fields the generator reads (re-derived by the pattern)
                der['fields'][fld] = b.get(key)
            st[ins['name']] = s
        elif ins['type'] == 'stages':
            for sp in ins['stages']:
                if sp.get('if') and not b.get(sp['if']):
                    continue
                st[sp['name']] = dict(name=sp['name'], layer=sp['layer'], cmd=_expand(sp['cmd'], b, ''), provenance=ins.get('provenance', 'automatic'),
                                      rules=[name], runnable=ins.get('runnable', True), evidence=b['evidence'])
        elif ins['type'] == 'variant_stage':
            v = b.get(ins['from'])
            arm = ins['variants'].get(v)
            if arm is None or arm.get('residual'):
                der['residual'].append(dict(layer=ins['layer'], reason=f"{name}: write shape {v} has no generic generator", hint=(arm or {}).get('hint', []), rule=name))
            else:
                st[ins['name']] = dict(name=ins['name'], layer=ins['layer'], cmd=_expand(arm['cmd'], b, ''), provenance=arm.get('provenance', 'automatic'),
                                        rules=[name], runnable=True, evidence=b['evidence'])
        elif ins['type'] == 'engine':
            der['engines'].append(dict(rule=name, layers=ins['layers'], libraries=ins['libraries'], priority=ins.get('priority', 0), evidence=b['evidence']))
        elif ins['type'] == 'frontend':
            der['frontend'].append(dict(rule=name, option=ins.get('translator_option'), evidence=b['evidence']))
        elif ins['type'] == 'closure':
            der['closure'] = dict(rule=name, shape=ins['shape'], cmd=ins['cmd'], runnable=ins.get('runnable', True), evidence=b['evidence'])
        elif ins['type'] in ('lift', 'shared_module'):
            der['lift'].append(dict(rule=name, kind=ins.get('kind', 'shared'), runnable=ins.get('runnable', True), evidence=b['evidence']))
        elif ins['type'] == 'route_field' and name != 'reset_level':
            der['fields'][ins['field']] = b.get(ins['from'])
    # modifiers
    for name, m in got.items():
        ins = R[name]['instantiate']
        if ins['type'] != 'modifier':
            continue
        tg = ins['target_stage'] if isinstance(ins['target_stage'], list) else [ins['target_stage']]
        for layer in tg:
            s = st.get(layer)     # stage name (the default names equal the layer)
            if not s:
                continue
            if 'set_generator' in ins:
                s['cmd'][0] = ins['set_generator']
            for a in ins.get('add_args', []):
                if a not in s['cmd']:
                    k = s['cmd'].index('--reset-events') if '--reset-events' in s['cmd'] else s['cmd'].index('--out')
                    s['cmd'].insert(k, a)
            s['rules'].append(name)
    # stage selection: runnable stages in canonical order; non-runnable ones are proposals
    for s in sorted(st.values(), key=lambda s: order.index(s['layer']) if s['layer'] in order else 99):
        (der['stages'] if s['runnable'] else der['proposals']).append(s)
    # residual layers
    covered = {s['layer'] for s in der['stages']} | {s['layer'] for s in der['proposals']}
    eng = sorted(der['engines'], key=lambda e: -e['priority'])
    for layer, why in RESIDUAL_LAYERS.items():
        if layer in covered:
            continue
        if layer == 'closure' and der['closure'] and der['closure']['runnable']:
            der['residual'].append(dict(layer='closure', reason='closure generator needs a clause schema (framework/closure-schemas/<D>.json) and the lower layers', hint=[der['closure']['rule']]))
            continue
        if layer == 'lift' and any(l['runnable'] and l['kind'] != 'shared' for l in der['lift']):
            der['residual'].append(dict(layer='lift', reason='lift builder needs framework/lift-roles/<D>.json (provider module, wire roles)', hint=[l['rule'] for l in der['lift']]))
            continue
        hint = [e['rule'] + ':' + '+'.join(e['libraries']) for e in eng if layer in e['layers']]
        if layer == 'lift':
            hint = [l['rule'] for l in der['lift']]
        if layer == 'closure' and der['closure']:
            hint = [der['closure']['rule'] + ' (not runnable yet)']
        der['residual'].append(dict(layer=layer, reason=why, hint=hint))
    return der


# ------------------------------------------------------------------ validation against the hand-written route / the ledger
def _script(cmd):
    return cmd[0] if cmd else None


def _norm(cmd):
    return [a for a in cmd]


def validate(design, der, man=None):
    man = man or json.loads((P.PROFILE / f'{design}.json').read_text())
    rows = []
    route = man.get('route')
    if route is None:
        return validate_ledger(design, der)
    want = route.get('rst_idle', 1)
    rows.append(dict(field='rst_idle', manifest=want, derived=der['fields']['rst_idle'], status=('match' if want == der['fields']['rst_idle'] else 'MISMATCH'),
                     detail=der['fields']['_rst_rule']))
    for k, v in der['fields'].items():
        if not k.startswith('_') and k != 'rst_idle':
            hv = route.get(k)
            rows.append(dict(field=f'route.{k}', manifest=json.dumps(hv), derived=json.dumps(v), status=('match' if hv == v else ('extra (rule derives)' if hv is None else 'MISMATCH')),
                             detail='re-derived by the rule pattern'))
    used = set()
    allst = der['stages'] + der['proposals']
    pair = {}
    for s in route['stages']:          # first pass: same layer and same generator script
        c = [t for t in allst if t['layer'] == s.get('layer') and _script(t['cmd']) == _script(s['cmd']) and id(t) not in used]
        if c:
            pair[s['name']] = c[0]; used.add(id(c[0]))
    for s in route['stages']:
        cands = [pair[s['name']]] if s['name'] in pair else []
        if not cands:
            other = [t for t in allst if t['layer'] == s.get('layer') and id(t) not in used]
            if other:
                t = other[0]; used.add(id(t))
                rows.append(dict(field=f"stage {s['name']}", manifest=' '.join(s['cmd']), derived=' '.join(t['cmd']), status='MISMATCH', detail=f"different generator (rule {t['rules']})"))
            else:
                rows.append(dict(field=f"stage {s['name']}", manifest=' '.join(s['cmd']), derived=None, status='residual',
                                 detail=f"no rule produces layer {s.get('layer')} with {_script(s['cmd'])} (provenance {s.get('provenance')})"))
            continue
        t = cands[0]
        a, b = _norm(s['cmd']), _norm(t['cmd'])
        env_m = {**route.get('env', {}), **s.get('env', {})}
        if a == b and not env_m:
            st, det = 'match', 'rules ' + ','.join(t['rules'])
        elif a != b and '--rise-procs' in a:
            k = a.index('--rise-procs')
            lst = [int(x) for x in a[k + 1].split(',')]
            rest = a[:k] + a[k + 2:]
            conv = (t.get('derived') or {}).get('rise_procs')
            if rest == b and conv == lst:
                st, det = 'match (equivalent)', f'manifest --rise-procs {a[k+1]} = rule-derived convertible set; generated text identical without the option'
            else:
                st, det = 'MISMATCH', f'rise-procs manifest {lst} vs derived {conv}'
        elif [x for x in a if x not in SPEED_ONLY] == [x for x in b if x not in SPEED_ONLY]:
            st, det = 'MISMATCH (speed option)', f"only {sorted(set(a) ^ set(b))} differs: proof-speed option with the same exported statements"
        else:
            st, det = 'MISMATCH', f"args differ: manifest-only {[x for x in a if x not in b]} derived-only {[x for x in b if x not in a]}"
        if s.get('text_sub'):
            det += f"; hand-written text_sub kept ({len(s['text_sub'])} replacement(s), documented generator gap)"
        rows.append(dict(field=f"stage {s['name']}", manifest=' '.join(a), derived=' '.join(b), status=st, detail=det))
    offd = {}
    for m in ledger_modules(design):
        if m.get('result_dir') and (m.get('accepted') or m.get('coqc_accepted')) and 'route-' not in m['id']:
            toks = gen_tokens(m.get('generator'))
            scr = next((t for t in toks if t.startswith('tools/') and t.endswith('.py')), None)
            offd.setdefault((scr, tuple(sorted(o for o in KEYOPTS if o in toks))), []).append(m['id'])
    for t in allst:
        if id(t) not in used:
            led = offd.get((_script(t['cmd']), tuple(sorted(o for o in KEYOPTS if o in t['cmd']))), [])
            rows.append(dict(field=f"stage {t['name']}", manifest=None, derived=' '.join(t['cmd']), status='extra (rule proposes)',
                             detail=f"rules {t['rules']}: {t['evidence']}" + ('' if t['runnable'] else ' [generator not text-mode runnable]') +
                             (f"; built off-driver: ledger {led[:3]}" if led else '; not built yet')))
    return rows


SPEED_ONLY = {'--fast-filter'}
KEYOPTS = ['--reset-events', '--frame', '--ram', '--rebased', '--slices', '--glue', '--reset-stage', '--reset-frame', '--reset-ram']


def ledger_modules(design):
    """accepted (or coqc-accepted) generated modules of a design from the ledger; ids without design field are attributed by prefix"""
    led = json.loads(LEDGER.read_text())
    out = []
    for m in led['modules']:
        d = m.get('design') or design_of_id(m['id'])
        if d != design:
            continue
        out.append(m)
    return out


def design_of_id(i):
    for pre, d in (('tmpl-dark', 'darkriscv'), ('tmpl-bzeeno', 'bzeeno'), ('tmpl-bz-', 'bzeeno'), ('bz-', 'bzeeno'), ('tmpl-cv', 'cv32e40p'),
                   ('steel-', 'steel'), ('srv32-', 'srv32'), ('nerv-', 'nerv'), ('angelo5fix-', 'angelo5fix')):
        if i.startswith(pre):
            return d
    return None


def gen_tokens(g):
    return (g or '').replace('(', ' ').replace(')', ' ').replace(',', ' ').split()


def validate_ledger(design, der):
    """designs without a route section: every ledger-recorded generator run whose script a rule produces is compared by script + key options"""
    rows = [dict(field='rst_idle', manifest='(no route section; generators ran with the default TMPL_RST_IDLE=1)', derived=der['fields']['rst_idle'],
                 status=('match' if der['fields']['rst_idle'] == 1 else 'MISMATCH'), detail=der['fields']['_rst_rule'])]
    allst = der['stages'] + der['proposals']
    scripts = {_script(s['cmd']): s for s in allst}
    keyopts = ['--fast-filter', '--reset-events', '--frame', '--ram', '--rebased', '--rounds', '--slices', '--glue', '--reset-stage', '--reset-frame', '--reset-ram']
    seen = set()
    for m in ledger_modules(design):
        if not m.get('result_dir') or not (m.get('accepted') or m.get('coqc_accepted')):
            continue
        toks = gen_tokens(m.get('generator'))
        scr = next((t for t in toks if t.startswith('tools/') and t.endswith('.py')), None)
        if scr not in ('tools/cpu_tmpl_edge.py', 'tools/cpu_tmpl_stage.py', 'tools/cpu_tmpl_rf.py', 'tools/cpu_tmpl_lfpnl.py', 'tools/cpu_tmpl_bzcopy.py', 'tools/cpu_tmpl_stage2.py'):
            continue
        opts = tuple(sorted(o for o in keyopts if o in toks))
        if '--variant' in toks:
            opts += ('--variant',)
        key = (scr, opts)
        if key in seen:
            continue
        seen.add(key)
        cands = [s for s in allst if _script(s['cmd']) == scr and tuple(sorted(o for o in keyopts if o in s['cmd'])) == tuple(sorted(o for o in opts if o in keyopts))]
        extra = [o for o in opts if o not in keyopts]
        if cands and not extra:
            rows.append(dict(field=f"ledger {m['id']}", manifest=m.get('generator'), derived=' '.join(cands[0]['cmd']), status='match', detail='rules ' + ','.join(cands[0]['rules'])))
        elif cands and extra:
            rows.append(dict(field=f"ledger {m['id']}", manifest=m.get('generator'), derived=' '.join(cands[0]['cmd']), status='partial',
                             detail=f"same layer generator; options {extra} are Bzeeno-route variants not modelled as rules"))
        elif [s for s in allst if _script(s['cmd']) == scr and tuple(sorted(o for o in keyopts if o in s['cmd'] and o not in SPEED_ONLY)) == tuple(sorted(o for o in opts if o in keyopts and o not in SPEED_ONLY))]:
            rows.append(dict(field=f"ledger {m['id']}", manifest=m.get('generator'), derived=None, status='MISMATCH (speed option)',
                             detail='only --fast-filter differs (same statements); below the cost threshold the rule does not add it'))
        else:
            near = [s for s in allst if _script(s['cmd']) == scr]
            rows.append(dict(field=f"ledger {m['id']}", manifest=m.get('generator'), derived=(' '.join(near[0]['cmd']) if near else None),
                             status=('MISMATCH' if near else 'residual'), detail=('options differ' if near else 'no rule derives this run')))
    return rows


# ------------------------------------------------------------------ apply: the route cfg the driver runs
def apply_cfg(design, der, man=None, keep_hand_text_sub=True):
    """cfg = manifest route with rule-derived fields; uncovered stages kept as hand-written residual stages"""
    man = man or json.loads((P.PROFILE / f'{design}.json').read_text())
    route = man.get('route')
    cfg = dict(date=(route or {}).get('date', '20261104'), rst_idle=der['fields']['rst_idle'], env={}, stages=[], rule_applied=True,
               residual_stages=[], rule_stages=[])
    for k, v in der['fields'].items():
        if not k.startswith('_') and k != 'rst_idle':
            cfg[k] = v
    if route:
        for k in route:          # non-stage hand-written data of residual generators (e.g. fetch, fetchwire, operands) stays
            if k not in ('stages', 'rst_idle', 'env', 'date', 'note') and k not in cfg:
                cfg[k] = route[k]
                cfg.setdefault('hand_fields_kept', []).append(k)
        allst = der['stages']
        used = set()
        for s in route['stages']:
            cands = [t for t in allst if t['layer'] == s.get('layer') and _script(t['cmd']) == _script(s['cmd']) and id(t) not in used]
            if cands:
                t = cands[0]; used.add(id(t))
                ns = {k: s[k] for k in ('name', 'layer', 'module', 'namespace', 'ref', 'needs', 'timeout', 'optional', 'supersedes') if k in s}
                ns.update(cmd=list(t['cmd']), provenance=t['provenance'], generator=' '.join(t['cmd'][:1]), rules=t['rules'], note=f"rule-derived ({','.join(t['rules'])})")
                if keep_hand_text_sub and s.get('text_sub'):
                    ns['text_sub'] = s['text_sub']
                    cfg.setdefault('hand_fields_kept', []).append(f"{s['name']}.text_sub")
                cfg['stages'].append(ns)
                cfg['rule_stages'].append(s['name'])
            else:
                ns = copy.deepcopy(s)
                ns['residual'] = True
                cfg['stages'].append(ns)
                cfg['residual_stages'].append(s['name'])
    else:
        P_ = _camel(design)
        for t in der['stages']:
            L = _camel(t['layer'])
            cfg['stages'].append(dict(name=t['name'], layer=t['layer'], module=f'{P_}Tmpl{L}', namespace=f'Tmpl{P_}{L}', cmd=list(t['cmd']),
                                      provenance=t['provenance'], generator=t['cmd'][0], rules=t['rules'], note=f"rule-derived ({','.join(t['rules'])})"))
            cfg['rule_stages'].append(t['name'])
    cfg['residual_obligations'] = der['residual']
    return cfg


def report(design, variants=None, as_json=False, write=False, out=sys.stdout):
    lib = load_library()
    ctx, ms = match(design, lib)
    der = derive(design, ms, lib, variants)
    rows = validate(design, der)
    res = dict(design=design, proof_author=P.AUTHOR, external_llm_api_calls=0, library=str(LIBRARY.relative_to(ROOT)),
               matched=[dict(rule=m['rule'], kind=m['kind'], evidence=m['bind']['evidence']) for m in ms if 'bind' in m],
               pattern_errors=[m for m in ms if 'error' in m], derived=der, validation=rows)
    if write:
        DERIVED.mkdir(parents=True, exist_ok=True)
        (DERIVED / f'{design}.json').write_text(json.dumps(dict(res, apply_cfg=apply_cfg(design, der)), indent=1) + '\n')
    if as_json:
        print(json.dumps(res, indent=1), file=out)
        return res
    p = lambda *a: print(*a, file=out)
    p(f'== rule match: {design}  ({len(res["matched"])} of {len(lib["rules"])} rules match)')
    by = {}
    for m in res['matched']:
        by.setdefault(m['kind'], []).append(m)
    for k in ('normalization', 'layer_generator', 'generic_lemma', 'proof_strategy'):
        for m in by.get(k, []):
            p(f'  [{k[:5]}] {m["rule"]:24s} {m["evidence"][:110]}')
    for e in res['pattern_errors']:
        p(f'  [ERROR] {e["rule"]}: {e["error"]}')
    p(f'-- route fields: rst_idle={der["fields"]["rst_idle"]}  ({der["fields"]["_rst_rule"][:100]})' +
      ''.join(f'  {k}={json.dumps(v)[:80]}' for k, v in der['fields'].items() if not k.startswith('_') and k != 'rst_idle'))
    p('-- stages covered by rules:')
    for s in der['stages']:
        p(f'  {s["layer"]:7s} {" ".join(s["cmd"])}   <- {",".join(s["rules"])}')
    for s in der['proposals']:
        p(f'  {s["layer"]:7s} {" ".join(s["cmd"])}   <- {",".join(s["rules"])}  [proposal: generator not text-mode runnable on the driver]')
    p('-- residual obligations (for the LLM):')
    for r in der['residual']:
        p(f'  {r["layer"]:7s} {r["reason"]}' + (f'   hints: {", ".join(r["hint"])}' if r.get('hint') else ''))
    if der['frontend']:
        p('-- frontend normalizations the import needed: ' + ', '.join(f['rule'] for f in der['frontend']))
    p('-- validation against the hand-written route' + (' (manifest route)' if json.loads((P.PROFILE / f'{design}.json').read_text()).get('route') else ' (ledger generator records)') + ':')
    for r in rows:
        p(f'  {r["status"]:22s} {r["field"]:28s} {r["detail"][:150]}')
        if r['status'].startswith('MISMATCH'):
            p(f'      manifest: {r["manifest"]}\n      derived : {r["derived"]}')
    return res


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--design', required=True)
    ap.add_argument('--json', action='store_true')
    ap.add_argument('--write', action='store_true', help='write framework/rule-derived-routes/<D>.json')
    ap.add_argument('--rule-variant', action='append', default=[], help='rule=variant (e.g. reset_level=asserted_level_plus_reset_layer)')
    a = ap.parse_args()
    report(a.design, dict(v.split('=', 1) for v in a.rule_variant), a.json, a.write)


if __name__ == '__main__':
    main()
