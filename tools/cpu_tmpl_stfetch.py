#!/usr/bin/env python3
"""Fetch link generator (unified instruction/data memory, registered read): read_data after one cycle = ROM word at the word index.
Ids come from the manifest `route.fetch` = {ram, read_data, hold_cond, invalid, word_index, words, ast, ast_ns}; the module text is
framework/template-sources/SteelFetchCore.v.in.  The pack lemma (ram_pack word i) depends on the TG.ram_pack of the target layer.
proof_author: LLM-generated: Claude Code (claude-sonnet-5-5); external_llm_api_calls=0."""
import argparse, json
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('--design', default='steel'); ap.add_argument('--module', required=True); ap.add_argument('--out', required=True)
a = ap.parse_args()
f = json.loads((ROOT / f'framework/auto-contract-profiles/{a.design}.json').read_text())['route']['fetch']
t = (ROOT / 'framework/template-sources/SteelFetchCore.v.in').read_text()
for k, v in dict(MOD=a.module, AST=f['ast'], C=f['hold_cond'], INV=f['invalid'], IDX=f['word_index'], RAM=f['ram'], RD=f['read_data'], WORDS=f['words']).items():
    t = t.replace(f'@{k}@', str(v))
t += ''.join(f'Print Assumptions {a.module}.{n}.\n' for n in ('pack_word', 'fetch_link'))
Path(a.out).write_text(t)
