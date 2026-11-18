#!/usr/bin/env python3
"""Generate an obligation record and checked final assembly from a closure ABI.

The schema names the unchanged conclusion, obligation types, and existing proof
providers. It contains no proof tactics. This automates assembly only, not the
proofs of obligations, the invariant, or the closure skeleton itself.
"""
import argparse
import json
import re
from pathlib import Path

IDENT=re.compile(r'[A-Za-z_][A-Za-z0-9_]*')

def render(c):
    names=[r['name'] for r in c['obligations']]
    if not names or len(set(names))!=len(names) or any(not IDENT.fullmatch(n) for n in names):
        raise ValueError('unique obligation identifiers required')
    mod=c['module']; bind=c['binders']; args=c['arguments']
    props=' '.join('P_'+n for n in names)
    types=' '.join('('+r['type']+')' for r in c['obligations'])
    text=f'''(** Generated obligation assembly. proof_author: LLM-generated: OpenAI Codex; external_llm_api_calls=0. *)
{c['preamble']}
Module {mod}.
Record ObligationPack ({props} : Prop) : Prop := {{
'''
    text+=';\n'.join(f"  ob_{r['name']} : P_{r['name']}" for r in c['obligations'])+'\n}.\n'
    text+=f"Definition Obligations {bind} : Prop := @ObligationPack {types}.\n"
    text+=f"Definition obligations {bind} : Obligations {args} :=\n  @Build_ObligationPack {types} "+' '.join('('+r['provider']+')' for r in c['obligations'])+'.\n'
    text+=f"Theorem from_obligations {bind} (ob:Obligations {args}) :\n {c['conclusion']}.\nProof. exact ({c['assemble']} "+' '.join(f'(@ob_{n} {types} ob)' for n in names)+' '+c.get('assemble_suffix','')+'). Qed.\n'
    text+=f"Theorem refinement {bind} :\n {c['conclusion']}.\nProof. exact (from_obligations {args} (obligations {args})). Qed.\nEnd {mod}.\n"
    text+=''.join(f'Print Assumptions {mod}.{n}.\n' for n in ['obligations','from_obligations','refinement'])
    return text

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('schema',type=Path);ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args(); text=render(json.loads(a.schema.read_text()))
    with a.out.open('x') as f:f.write(text)
