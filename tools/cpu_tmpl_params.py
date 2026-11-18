#!/usr/bin/env python3
"""Role parameters of the hand-written template cores (additive; part of the template route).

The manifest section `template_roles.core_ids` of framework/auto-contract-profiles/<design>.json binds the role names used
in framework/template-sources/param/Tmpl*Core.v.in to the design:
  signals  ROLE -> RTL signal path (resolved to the signal-table id; pipeline_roles values are cross-checked)
  procs    NAME -> {process, writes: ROLE}  (checked against the AST)
  idlists  KEY  -> [ROLE, ...]
  names    KEY  -> Coq name of a design-specific module/symbol
Placeholders: @id:ROLE@  @proc:NAME@  @k:ROLE@ (index of the comb process driving ROLE)  @idlist:KEY@  @name:KEY@
              @cohlo@ @cohhi@ @cohcount@ @cohrw@ (the contiguous coherent-field register range)
Untrusted tooling. proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0.
"""
import json
import re
from pathlib import Path
import cpu_tmpl_roles as roles
import cpu_tmpl_inv as inv

TEMPLATES = Path('framework/template-sources/param')


class Params:
    def __init__(self, design):
        self.design = design
        self.ast, self.pr, self.tr = roles.load_all(design)
        ci = self.tr['core_ids']
        by_path = {v['path']: i for i, v in self.ast.sig.items()}
        self.id = {}
        for role, path in ci['signals'].items():
            if path not in by_path:
                raise KeyError(f'role {role}: signal {path} not in signal table')
            self.id[role] = by_path[path]
        self.proc = {}
        for name, e in ci['procs'].items():
            self.proc[name] = e['process']
            n = int(e['process'].split('_')[1])
            root = self.id[e['writes']]
            if root not in self._written(n):
                raise ValueError(f'proc {name}: {e["process"]} does not write {e["writes"]}')
        self.idlists = {k: [self.id[r] for r in v] for k, v in ci['idlists'].items()}
        self.names = ci['names']
        self._cross_check()
        fields, inword = inv.captured_fields(self.ast, self.pr)
        word = self.pr['fetch_slot']['word']['id']
        coh = sorted({word} | {R for R, w, g in fields})
        if coh != list(range(coh[0], coh[-1] + 1)):
            raise ValueError('coherent registers are not a contiguous id range; the range form of the cursor core does not apply')
        self.coh = coh

    def _written(self, n):
        out = set()
        for s in roles.flat(self.ast.procs[n]['body']):
            if s[0] == 'SAssign':
                lv = s[3]
                while lv[0] == 'LSel':
                    lv = lv[2]
                out.add(lv[2])
        return out

    def _cross_check(self):
        """role ids that are also named by pipeline_roles must agree"""
        pr, i = self.pr, self.id
        pairs = [('CLK', pr['events']['clock']['id']), ('RESIN', pr['events']['reset']['id']),
                 ('STALL', pr['fetch_slot']['stall']['id']), ('RESET_REG', self.tr['reset_reg']['id']),
                 ('VALID_CTR', pr['controller']['flush']['id']), ('FETCH_PC', pr['pc']['fetch_pc']['id']),
                 ('EXEC_PC', pr['pc']['register']['id']), ('SLOT_PC', pr['fetch_slot']['pc']['id']),
                 ('SLOT_WORD', pr['fetch_slot']['word']['id']), ('JREQ', pr['pc']['branch_request']['id']),
                 ('JVAL', pr['pc']['branch_target']['id']), ('BANK', pr['rf_write']['bank']['id'])]
        ib = pr.get('instruction_bus')
        if ib:
            pairs += [('IBUS_ADDR', ib['address']['id']), ('IBUS_DATA', ib['data']['id']), ('IBUS_ACK', ib['ack']['id']),
                      ('IBUS_REQ', ib['request']['id'])]
        for role, v in pairs:
            if role in i and i[role] != v:
                raise ValueError(f'role {role}: core_ids says {i[role]}, pipeline_roles says {v}')

    def render(self, text):
        i = self.id

        def sub(m):
            kind, arg = m.group(1), m.group(2)
            if kind == 'id':
                return str(i[arg])
            if kind == 'proc':
                return self.proc[arg]
            if kind == 'k':
                return str(self.ast.comb[i[arg]]['k'])
            if kind == 'idlist':
                return '[' + ';'.join(map(str, self.idlists[arg])) + ']'
            if kind == 'name':
                return self.names[arg]
            raise KeyError(kind)
        text = re.sub(r'@(id|proc|k|idlist|name):([A-Za-z0-9_.]+)@', sub, text)
        rw = ', '.join(f'?(A {r}%nat ltac:(lia))' for r in self.coh)
        text = text.replace('@cohrw@', f'repeat (rewrite {rw})')
        return (text.replace('@cohlo@', str(self.coh[0])).replace('@cohhi@', str(self.coh[-1]))
                .replace('@cohcount@', str(len(self.coh))))

    def core(self, name):
        return self.render((TEMPLATES / name).read_text())


def write_core_ids(design, core_ids):
    path = roles.PROFILE / (design + '.json')
    prof = json.loads(path.read_text())
    prof['template_roles']['core_ids'] = core_ids
    path.write_text(json.dumps(prof, indent=1) + '\n')
