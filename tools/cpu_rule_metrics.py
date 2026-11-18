#!/usr/bin/env python3
"""REUSE METRICS of the rule library, per design, from route.json + the ledger.

    python tools/cpu_rule_metrics.py --design D [--library historical|full|empty] [--json]
    python tools/cpu_rule_metrics.py --table [--order bzeeno,darkriscv,steel,srv32,nerv,angelo5fix] [--markdown]
    python tools/cpu_rule_metrics.py --check-reuse        (library `reused_by` claims vs. what the modules show)

Inventory of a design = its accepted modules (coqc + audit; coqchk may be deferred): the stages of its accepted provider route
(results/route-<D>-*/route.json, all stages coqc_accepted) plus the ledger's accepted generated modules, deduplicated by module
name (failed/killed/superseded attempts and libraries excluded).  Each module is attributed to rules through the rules' `match`
specs: a rule PRODUCES a module when the module's generator (script + options + env) is the rule's generator; a rule ASSISTS a
module when the module Requires the rule's library.
Library modes:
  historical  a rule counts only if it was learned on this design or published (learned_at) before the module was built
  full        every rule of today's library counts (what the library would cover if the design were done again now)
  empty       ablation: no rule; every module is residual (the list shows which modules the rules took away)
Classes: reused_rule (produced by a rule learned on another design), new_rule (produced by a rule learned on this design),
residual_assisted (design-specific generator / LLM text that Requires rule libraries), residual.
reuse rate = reused_rule / modules.  Wall = coqc/driver seconds recorded for the modules (route wall_seconds, else ledger coqc_seconds).
proof_author: LLM-generated: Claude Code (claude-opus-5-5); external_llm_api_calls=0.
"""
import argparse
import json
import os
import re
import sys
import time
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cpu_rule_match as RM

ROOT = RM.ROOT
ORDER = ['bzeeno', 'darkriscv', 'steel', 'srv32', 'nerv', 'angelo5fix']
NONMODULE_KINDS = {'generic_library', 'library', 'tool', 'tooling', 'manifest', 'generic_library_hand_written', 'hand_written_source', 'simulation'}
LAYER_WORDS = [('closure', 'closure'), ('lfp', 'lfp'), ('target', 'target'), ('edger', 'reset'), ('reset', 'reset'), ('edge', 'edge'), ('stage2', 'stage2'), ('rise', 'stage'),
               ('stage', 'stage'), ('frame', 'frame'), ('cyc', 'cycle'), ('cycle', 'cycle'), ('base', 'cycle'), ('val', 'value'), ('fetch', 'fetch'),
               ('fw', 'fetch'), ('rffall', 'rf'), ('rf', 'rf'), ('op-closure', 'closure'), ('op', 'rf'), ('ram', 'ram'), ('mis', 'domain'), ('immj', 'imm'),
               ('imm', 'imm'), ('wire', 'wire'), ('nx', 'next'), ('next', 'next'), ('fwd', 'fwd'), ('copy', 'copy'), ('lift', 'lift'), ('ctl', 'ctl'),
               ('dec', 'ctl'), ('alu', 'ctl'), ('ovl', 'ctl'), ('ex', 'ctl'), ('cap', 'ctl'), ('controls', 'ctl'), ('bubble', 'ctl'), ('step', 'closure'),
               ('final', 'closure'), ('inv', 'closure'), ('rank', 'closure'), ('boot', 'closure'), ('closure', 'closure'), ('arch', 'closure'),
               ('cursor', 'closure'), ('valid', 'closure'), ('trans', 'closure'), ('disp', 'closure'), ('none', 'closure'), ('env', 'closure'),
               ('phase', 'closure'), ('shape', 'closure'), ('nstate', 'closure'), ('xfer', 'closure'), ('ifid', 'closure'), ('front', 'closure'),
               ('flow', 'closure'), ('sel', 'closure'), ('id', 'closure'), ('defs', 'closure'), ('isa', 'lift'), ('link', 'fetch'), ('pre', 'closure'),
               ('mem', 'closure'), ('csr', 'ctl')]


def ts(s):
    return datetime.fromisoformat(s).timestamp() if s else 0.0


def requires(vfile):
    t = Path(vfile).read_text(errors='replace')
    out = set()
    for m in re.finditer(r'\bRequire\s+(?:Import\s+|Export\s+)?(.*?)\.(?=\s|$)', t, flags=re.S):
        for tok in m.group(1).split():
            out.add(tok.split('.')[-1])
    return out


def layer_of(name):
    n = name.lower()
    n = re.sub(r'^(r-tmpl-|route-)', '', n)
    for w, l in LAYER_WORDS:
        if re.search(r'(^|[-_/])' + re.escape(w) + r'($|[-_/0-9a])', n):
            return l
    return 'other'


def provider_route(design):
    best = None
    for rj in sorted((ROOT / 'results').glob(f'route-{design}-*/route.json')):
        j = json.loads(rj.read_text())
        if j.get('failed') or re.search(r'-(gen|rules)', j['route']):
            continue
        if not j['stages'] or not all(s.get('status') == 'coqc_accepted' for s in j['stages']):
            continue
        if best is None or rj.stat().st_mtime > best[0]:
            best = (rj.stat().st_mtime, rj, j)
    return (best[1], best[2]) if best else (None, None)


def _route_versions(design, rst_idle):
    out = []
    for rj in sorted((ROOT / 'results').glob(f'route-{design}-*/route.json')):
        j = json.loads(rj.read_text())
        if re.search(r'-(gen|rules)', j['route']):
            continue
        for s in j['stages']:
            if s.get('status') != 'coqc_accepted':
                continue
            d = Path(s['dir'])
            d = d if d.is_absolute() else ROOT / d
            mod = s['module'].split('.')[-1]
            vf = d / f'{mod}.v'
            if not vf.exists():
                continue
            env = {'TMPL_RST_IDLE': '0'} if s.get('layer') in ('edge', 'reset', 'stage', 'frame') and rst_idle == 0 else {}
            out.append(dict(module=mod, source='route', route=str(rj.relative_to(ROOT)), dir=str(d.relative_to(ROOT)), layer=s.get('layer') or layer_of(s['name']),
                            tokens=list(s.get('cmd', [])) + [s.get('generator') or ''], generator=' '.join(s.get('cmd', [])), env=env,
                            provenance=s.get('provenance'), wall=s.get('wall_seconds', 0) or 0, mtime=vf.stat().st_mtime, vfile=str(vf), accepted=True))
    return out


def _ledger_versions(design):
    out = []
    for m in RM.ledger_modules(design):
        if m.get('kind') in NONMODULE_KINDS or not m.get('result_dir') or '-route-' in m['id']:
            continue
        if not (m.get('accepted') or m.get('coqc_accepted')):
            continue
        d = ROOT / m['result_dir']
        if re.search(r'failed|killed|slow', d.name) or not d.is_dir():
            continue
        vs = sorted(v for v in d.glob('*.v') if not v.name.startswith('Probe'))
        if not vs:
            continue
        vf = vs[0]
        g = ' '.join(str(x) for x in ([m.get('generator')] if m.get('generator') else []) + [m.get('note', '')])
        out.append(dict(module=vf.stem, source='ledger', dir=m['result_dir'], layer=layer_of(Path(m['result_dir']).name), tokens=RM.gen_tokens(m.get('generator')),
                        generator=m.get('generator') or '', gen_text=g, env=({'TMPL_RST_IDLE': '0'} if 'TMPL_RST_IDLE=0' in g else {}),
                        provenance=m.get('provenance'), wall=m.get('coqc_seconds') or m.get('wall_s') or 0, mtime=vf.stat().st_mtime,
                        vfile=str(vf), ledger_ids=[m['id']], accepted=bool(m.get('accepted'))))
    return out


_INV = {}


def inventory(design):
    """module name -> primary version (provider route stage, else the accepted ledger version, else the latest) with
    `first` = time of the first accepted version of that module and `versions` = every accepted version"""
    if design in _INV:
        return _INV[design]
    rj, route = provider_route(design)
    man = json.loads((RM.P.PROFILE / f'{design}.json').read_text()) if (RM.P.PROFILE / f'{design}.json').exists() else {}
    rst_idle = (man.get('route') or {}).get('rst_idle', 1)
    vers = _route_versions(design, rst_idle) + _ledger_versions(design)
    for v in vers:
        v['requires'] = sorted(requires(v['vfile']))
    by = {}
    for v in vers:
        by.setdefault(v['module'], []).append(v)
    mods = {}
    prov = str(rj.relative_to(ROOT)) if rj else None
    for name, vs in by.items():
        prim = ([v for v in vs if v.get('route') == prov] or sorted([v for v in vs if v['source'] == 'ledger'], key=lambda v: (v['accepted'], v['mtime']))[-1:] or
                sorted(vs, key=lambda v: v['mtime'])[-1:])[0]
        m = dict(prim)
        m['first'] = min(v['mtime'] for v in vs)
        m['versions'] = vs
        if not m.get('wall'):
            m['wall'] = next((v['wall'] for v in sorted(vs, key=lambda v: v['mtime']) if v.get('wall')), 0)
        mods[name] = m
    _INV[design] = (mods, prov, route)
    return _INV[design]


def spec_hit(spec, m, design):
    if 'design' in spec and spec['design'] != design:
        return None
    if 'script' in spec:
        if spec['script'] not in m['tokens'] and spec['script'] not in m.get('generator', ''):
            return None
        toks = set(m['tokens']) | set((m.get('generator') or '').split())
        if any(a not in toks for a in spec.get('requires_args', [])) or any(a in toks for a in spec.get('forbids_args', [])):
            return None
        return 'produces'
    if 'library' in spec:
        return 'assists' if spec['library'] in m['requires'] else None
    if 'env' in spec:
        return 'produces_mod' if all(m['env'].get(k) == v for k, v in spec['env'].items()) else None
    if 'generator_text' in spec:
        return 'produces_mod' if spec['generator_text'] in (m.get('gen_text') or m.get('generator') or '') else None
    return None


_LEARNED = {}


def learned_ts(lib):
    """rule -> time it became available: the earliest accepted module on its learned_from design that the rule produces or
    assists (module .v mtime); the library's `learned_at` only when no such module exists"""
    key = id(lib)
    if key in _LEARNED:
        return _LEARNED[key]
    out = {}
    by = {}
    for r in lib['rules']:
        by.setdefault(r['learned_from'], []).append(r)
    for d, rs in by.items():
        try:
            mods, _, _ = inventory(d)
        except Exception:
            mods = {}
        for r in rs:
            t = [v['mtime'] for m in mods.values() for v in m['versions'] if any(spec_hit(s, v, d) for s in r.get('match', []))]
            la = ts(r.get('learned_at'))
            if t and (not la or min(t) <= la):
                out[r['name']] = (min(t), 'first module on ' + d)
            else:
                out[r['name']] = (la, 'learned_at (log / library file time)')
    _LEARNED[key] = out
    return out


def attribute(design, mods, lib, mode):
    rules = lib['rules'] if mode != 'empty' else []
    lt = learned_ts(lib) if mode == 'historical' else {}
    for m in mods.values():
        prod, mod_, ass = [], [], []
        for r in rules:
            hits = {spec_hit(s, m, design) for s in r.get('match', [])} - {None}
            if not hits:
                continue
            avail = mode == 'full' or r['learned_from'] == design or lt[r['name']][0] <= m['first']
            if not avail:
                continue
            if 'produces' in hits:
                prod.append(r)
            elif 'produces_mod' in hits:
                mod_.append(r)
            else:
                ass.append(r)
        if prod:
            own = [r['name'] for r in prod + mod_ if r['learned_from'] == design]
            m['class'] = 'new_rule' if own else 'reused_rule'
        elif ass:
            m['class'] = 'residual_assisted'
        else:
            m['class'] = 'residual'
        m['producing'] = [r['name'] for r in prod + mod_]
        m['assisting'] = [r['name'] for r in ass]
        m['assist_from'] = sorted({r['learned_from'] for r in ass if r['learned_from'] != design})
    return mods


def metrics(design, mode='historical', lib=None):
    lib = lib or RM.load_library()
    mods, rdir, route = inventory(design)
    attribute(design, mods, lib, mode)
    cls = {}
    for m in mods.values():
        cls.setdefault(m['class'], []).append(m['module'])
    n = len(mods)
    wall = {k: round(sum(mods[x]['wall'] for x in v), 1) for k, v in cls.items()}
    wall_known = sum(1 for m in mods.values() if m['wall'])
    new_rules = [r['name'] for r in lib['rules'] if r['learned_from'] == design]
    ctx, ms = RM.match(design, lib)
    der = RM.derive(design, ms, lib)
    have = {m['layer'] for m in mods.values()}
    open_layers = [r['layer'] for r in der['residual'] if r['layer'] not in have]
    built = {n for m in mods.values() for n in m['producing']}
    if mode != 'full':      # which rules produced a module of this design in any mode (a proposal is "not built" otherwise)
        tmp = {k: dict(v) for k, v in mods.items()}
        attribute(design, tmp, lib, 'full')
        built = {n for m in tmp.values() for n in m['producing']}
    proposals = [dict(stage=t['name'], layer=t['layer'], rule=t['rules'][0], runnable=t['runnable']) for t in der['stages'] + der['proposals'] if t['rules'][0] not in built]
    abl = sorted(x for k in ('reused_rule', 'new_rule') for x in cls.get(k, []))
    return dict(design=design, mode=mode, route=rdir, route_wall_seconds=(route or {}).get('wall_seconds_total'),
                modules=n, classes={k: len(v) for k, v in cls.items()}, reuse_rate=round(len(cls.get('reused_rule', [])) / n, 3) if n else None,
                rule_rate=round((len(cls.get('reused_rule', [])) + len(cls.get('new_rule', []))) / n, 3) if n else None,
                new_rules_added=new_rules, residual_obligations=len(cls.get('residual', [])) + len(cls.get('residual_assisted', [])),
                open_layers=open_layers, wall_seconds=wall, wall_known_modules=wall_known, wall_seconds_total=round(sum(m['wall'] for m in mods.values()), 1),
                ablation_residual_if_empty=abl, rule_proposals_not_built=proposals,
                per_module={m['module']: dict(cls=m['class'], layer=m['layer'], producing=m['producing'], assisting=m['assisting'],
                                              assist_from=m['assist_from'], wall=m['wall'], dir=m['dir'], source=m['source']) for m in mods.values()})


def check_reuse(lib=None):
    """library reused_by claims vs designs whose modules are produced/assisted by the rule (full mode)"""
    lib = lib or RM.load_library()
    seen = {r['name']: set() for r in lib['rules']}
    for d in ORDER:
        mods, _, _ = inventory(d)
        attribute(d, mods, lib, 'full')
        for m in mods.values():
            for n in m['producing'] + m['assisting']:
                seen[n].add(d)
    rows = []
    for r in lib['rules']:
        claimed = {x['design'] for x in r.get('reused_by', [])}
        shown = seen[r['name']] - {r['learned_from']}
        rows.append(dict(rule=r['name'], learned_from=r['learned_from'], claimed=sorted(claimed), shown_by_modules=sorted(shown),
                         claimed_not_shown=sorted(claimed - shown), shown_not_claimed=sorted(shown - claimed)))
    return rows


def table(order, mode='historical', lib=None):
    lib = lib or RM.load_library()
    rows, flow = [], {}
    for d in order:
        r = metrics(d, mode, lib)
        rows.append(r)
        for m in r['per_module'].values():
            if m['cls'] == 'reused_rule':
                for n in m['producing']:
                    src = next(x['learned_from'] for x in lib['rules'] if x['name'] == n)
                    if src != d:
                        flow[(src, d)] = flow.get((src, d), 0) + 1
    return rows, flow


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--design')
    ap.add_argument('--library', choices=['historical', 'full', 'empty'], default='historical')
    ap.add_argument('--table', action='store_true')
    ap.add_argument('--order', default=','.join(ORDER))
    ap.add_argument('--json', action='store_true')
    ap.add_argument('--modules', action='store_true', help='print the per-module attribution')
    ap.add_argument('--check-reuse', action='store_true')
    a = ap.parse_args()
    os.chdir(ROOT)
    if a.check_reuse:
        rows = check_reuse()
        if a.json:
            print(json.dumps(rows, indent=1)); return
        for r in rows:
            flag = '' if not (r['claimed_not_shown'] or r['shown_not_claimed']) else f"  claimed-not-shown {r['claimed_not_shown']} shown-not-claimed {r['shown_not_claimed']}"
            print(f"{r['rule']:24s} from {r['learned_from']:10s} claimed {r['claimed']} shown {r['shown_by_modules']}{flag}")
        return
    if a.table:
        rows, flow = table(a.order.split(','), a.library)
        if a.json:
            print(json.dumps(dict(rows=[{k: v for k, v in r.items() if k != 'per_module'} for r in rows], flow={f'{k[0]}->{k[1]}': v for k, v in flow.items()}), indent=1)); return
        print(f'| design | modules | reused_rule | new_rule | residual_assisted | residual | reuse rate | rule rate | new rules | open layers | wall s (rule / residual) | today\'s library proposes (not built) |')
        print('|---|---|---|---|---|---|---|---|---|---|---|---|')
        for r in rows:
            c = r['classes']; w = r['wall_seconds']
            print(f"| {r['design']} | {r['modules']} | {c.get('reused_rule', 0)} | {c.get('new_rule', 0)} | {c.get('residual_assisted', 0)} | {c.get('residual', 0)} | "
                  f"{r['reuse_rate']} | {r['rule_rate']} | {len(r['new_rules_added'])} | {', '.join(r['open_layers']) or '-'} | "
                  f"{round(w.get('reused_rule', 0) + w.get('new_rule', 0))} / {round(w.get('residual', 0) + w.get('residual_assisted', 0))} ({r['wall_known_modules']}/{r['modules']} timed) | {', '.join(p['stage'] + ('' if p['runnable'] else '*') for p in r['rule_proposals_not_built']) or '-'} |")
        print('\nrule-produced modules by (learned_from -> reused on):', ', '.join(f'{k[0]}->{k[1]}: {v}' for k, v in sorted(flow.items())))
        return
    if not a.design:
        raise SystemExit('--design or --table')
    r = metrics(a.design, a.library)
    if a.json:
        print(json.dumps(r, indent=1)); return
    print(f"== reuse metrics {a.design} (library {a.library}); route {r['route']} (driver wall {r['route_wall_seconds']} s)")
    print(f"modules {r['modules']}: {r['classes']}  reuse rate {r['reuse_rate']}  rule rate {r['rule_rate']}")
    print(f"new rules learned on {a.design}: {len(r['new_rules_added'])} {r['new_rules_added']}")
    print(f"residual obligations (modules done by LLM/design-specific generators): {r['residual_obligations']}; open layers (no module yet): {r['open_layers']}")
    print(f"wall s by class: {r['wall_seconds']} (total {r['wall_seconds_total']})")
    print(f"ablation (empty library): these {len(r['ablation_residual_if_empty'])} modules would also be residual: {r['ablation_residual_if_empty']}")
    print(f"stages today's library proposes that are not built (* = generator not text-mode runnable): {[p['stage'] + ('' if p['runnable'] else '*') for p in r['rule_proposals_not_built']]}")
    if a.modules:
        for k, m in sorted(r['per_module'].items(), key=lambda t: (t[1]['cls'], t[0])):
            print(f"  {m['cls']:18s} {k:28s} {m['layer']:8s} prod {m['producing']} assist {m['assisting']} ({m['source']} {m['dir']})")


if __name__ == '__main__':
    main()
