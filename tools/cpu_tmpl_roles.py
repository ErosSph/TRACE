"""Template-route roles: discovery from the AST plus the pipeline_roles manifest.

Additive manifest section `template_roles` in framework/auto-contract-profiles/<design>.json.
Every entry records provenance ('discovered' with the structural rule, or 'manual').
Roles are generator data, never a proof premise.
"""
import json
from pathlib import Path
import cpu_tmpl_ast as T

PROFILE = Path('framework/auto-contract-profiles')


def sigrow(ast, i):
    r = ast.sig[i]
    return {'id': i, 'width': r['width'], 'path': r['path']}


def flat(s):
    if s[0] == 'SSeq':
        return [x for c in s[1] for x in flat(c)]
    return [s]


def discover(ast, pr):
    out = {}
    reset_in = pr['events']['reset']['id']
    for i, p in enumerate(ast.procs):
        if p['kind'] != 'Sequential':
            continue
        for s in flat(p['body']):
            if s[0] == 'SAssign' and s[1] and s[2] == ('EVar', 1, reset_in) and s[3][0] == 'LVar':
                out['reset_reg'] = dict(sigrow(ast, s[3][2]), provenance={
                    'source': 'discovered', 'rule': 'sequential register assigned directly from the reset input',
                    'process': ast.names[i]})
    stall = pr['fetch_slot']['stall']['id']
    cap = int(pr['fetch_slot']['capture_process'].split('_')[1])
    flags = []
    for s in flat(ast.procs[cap]['body']):
        if s[0] != 'SAssign' or s[3][0] != 'LVar' or s[3][1] != 1:
            continue
        F = s[3][2]
        r = s[2]
        if (r[0] == 'ECond' and r[2] == ('EVar', 1, stall) and r[3] == ('EVar', 1, F) and r[4][0] == 'EBinary'
                and r[4][2] == 'BEq' and r[4][3][0] == 'EConst' and r[4][3][1] == 7 and r[4][4][0] == 'ESel'
                and r[4][4][1] == 7 and r[4][4][3] == ('EConst', 5, 0)):
            flags.append(dict(opcode=r[4][3][2], reg=sigrow(ast, F)))
    out['class_flags'] = dict(flags=flags, provenance={
        'source': 'discovered', 'rule': 'capture-process register F <= stall ? F : (opcode-constant == word[6:0])',
        'process': pr['fetch_slot']['capture_process']})
    bank = pr['rf_write']['bank']['id']
    ports = []
    for root, c in ast.comb.items():
        r = c['rhs']
        if r[0] == 'ESel' and r[2] == ('EVar', 1024, bank) and r[3][0] == 'EBinary' and r[3][2] == 'BMul' \
                and r[3][3][0] == 'EVar':
            ports.append(dict(sigrow(ast, root), index=r[3][3][2]))
    out['rf_read_ports'] = dict(ports=ports, provenance={
        'source': 'discovered', 'rule': 'comb wire = bank[index * 32 +: 32]'})
    pcp = int(pr['pc']['process'].split('_')[1])
    rfp = int(pr['rf_write']['process'].split('_')[1])
    tg = {}
    for name, proc, root in [('rf_value', rfp, bank), ('next_flush', pcp, pr['controller']['flush']['id']),
                             ('next_fetch_pc', pcp, pr['pc']['fetch_pc']['id']),
                             ('next_exec_pc', pcp, pr['pc']['register']['id']),
                             ('next_slot_pc', pcp, pr['fetch_slot']['pc']['id'])]:
        path, st = ast.find_assign(proc, root)
        tg[name] = dict(process=f'process_{proc}', path=path, root=root, width=ast.sig[root]['width'])
    out['targets'] = dict(tg, provenance={'source': 'discovered',
                          'rule': 'unique assignment to the role register inside the role process'})
    wr, rd = pr['data_bus']['write']['id'], pr['data_bus']['read']['id']
    gates = {ast.comb[wr]['rhs'], ast.comb[rd]['rhs']}
    for root, c in ast.comb.items():
        r = c['rhs']
        if r[0] == 'EBinary' and r[2] == 'BOr' and {r[3], r[4]} == gates:
            out['data_request'] = dict(sigrow(ast, root), provenance={
                'source': 'discovered', 'rule': 'comb wire = OR of the read and write gate wires'})
    return out


def load_all(design):
    prof = json.loads((PROFILE / (design + '.json')).read_text())
    pr = prof['pipeline_roles']
    ast = T.Ast(pr['ast']['file'], pr['ast']['signal_table'])
    tr = prof.get('template_roles') or (discover(ast, pr) if 'stall' in pr['fetch_slot'] else {})
    return ast, pr, tr


def write(design):
    path = PROFILE / (design + '.json')
    prof = json.loads(path.read_text())
    ast = T.Ast(prof['pipeline_roles']['ast']['file'], prof['pipeline_roles']['ast']['signal_table'])
    prof['template_roles'] = discover(ast, prof['pipeline_roles'])
    path.write_text(json.dumps(prof, indent=1) + '\n')
    return path


if __name__ == '__main__':
    import sys
    d = sys.argv[1]
    ast = T.Ast(*[json.loads((PROFILE / (d + '.json')).read_text())['pipeline_roles']['ast'][k] for k in ('file', 'signal_table')])
    r = discover(ast, json.loads((PROFILE / (d + '.json')).read_text())['pipeline_roles'])
    print(json.dumps(r, indent=1)[:3000])
    if '--write' in sys.argv:
        print(write(d))
