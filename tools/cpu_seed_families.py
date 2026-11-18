#!/usr/bin/env python3
"""Fixed framework renderer for complete instruction families.

Each seed is one specific Coq proof, generalized only through named ISA fields
and scalar role encodings. Design inputs cannot supply executable Python or
per-class tactic snippets. Coq remains the checker of every instantiated claim.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from cpu_isa_classes import classes, IMM

ROWS={r['name']:r for r in classes()}
TOKEN=re.compile(r'@([A-Z_]+)@')
SYMBOL=re.compile(r'[A-Za-z_][A-Za-z0-9_.]*')
BIN={'Add':'BAdd','Sub':'BSub','Xor':'BXor','Or':'BOr','And':'BAnd'}
SHIFT={'Sll':('BShiftL','sll'),'Srl':('BShiftR','srl'),'Sra':('BShiftRS','sra')}
COND={'Slt':'SLT','Sltu':'SLTU','Beq':'EQ','Bne':'NE','Blt':'SLT','Bge':'GE','Bltu':'SLTU','Bgeu':'GEU'}

def parameters(name):
    r=ROWS[name]; base=IMM.get(name,(name,None))[0]
    p=dict(CLASS=name,ARGS='a0 a1' if name in ('Lui','Auipc','Jal') else 'a0 a1 a2')
    if base in BIN:p['BINOP']=BIN[base]
    if base in SHIFT:p['SHIFT_OP'],p['SHIFT_LOWER']=SHIFT[base]
    if base in COND:p['COND_SHAPE']=COND[base];p['COND_LOWER']=COND[base].lower()
    if r['funct7'] is not None:p['FUNCT_SEVEN']=str(r['funct7'])
    return p

def render(c, directory):
    expected=c['expected_classes']
    if len(expected)!=len(set(expected)) or set(expected)-ROWS.keys():raise ValueError('invalid expected class set')
    covered=[n for family in c['families'] for n in family['classes']]
    if len(covered)!=len(set(covered)) or set(covered)!=set(expected):raise ValueError('family partition has missing or duplicate classes')
    module=c['module']; bodies=[]; ledger=[]
    for family in c['families']:
        if family['origin'] not in ('legacy_adapted','llm_written'):
            raise ValueError('seed origin must be explicitly legacy_adapted or llm_written')
        seed=(directory/family['seed']).read_text()
        if len(re.findall(r'\bTheorem\s+',seed))!=1 or re.search(r'\b(Admitted|Axiom|Abort)\b',seed):raise ValueError('seed must contain one complete theorem')
        if family['representative'] not in family['classes']:raise ValueError('seed representative absent')
        for name in family['classes']:
            p=parameters(name)
            for key,value in c.get('roles',{}).get(name,{}).items():
                if not key.startswith('ROLE_') or not (type(value) is int or isinstance(value,str) and SYMBOL.fullmatch(value)):
                    raise ValueError('role values must be scalar encodings or qualified names')
                p[key]=str(value)
            missing=set(TOKEN.findall(seed))-p.keys()
            if missing:raise ValueError(f'{name}: missing parameters {sorted(missing)}')
            text=TOKEN.sub(lambda m:p[m[1]],seed)
            export=c['export'].replace('@CLASS@',name)
            if not re.search(r'\bTheorem\s+'+re.escape(export)+r'\b',text):raise ValueError('export mismatch')
            bodies.append(text)
            representative=name==family['representative']
            handwritten=representative and family['origin']=='llm_written'
            ledger.append(dict(theorem=module+'.'+export,instruction=name,seed=family['seed'],
                seed_sha256=hashlib.sha256(seed.encode()).hexdigest(),seed_origin=family['origin'],
                origin=('llm_written' if handwritten else 'adapted_seed') if representative else 'framework_instantiated',
                narrow_llm_written=handwritten,proof_author=family.get('proof_author','OpenAI Codex adapting existing evidence') if representative else 'framework: cpu_seed_families'))
    preamble=(directory/c['preamble']).read_text()
    text='(** Framework seed instances; generator author: OpenAI Codex; external_llm_api_calls=0. *)\n'+preamble+'\nModule '+module+'.\n'+'\n'.join(bodies)+'\nEnd '+module+'.\n'
    text+=''.join('Print Assumptions '+r['theorem']+'.\n' for r in ledger)
    return text,ledger

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('schema',type=Path);ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();c=json.loads(a.schema.read_text());text,ledger=render(c,a.schema.parent)
    a.out.mkdir(parents=True,exist_ok=False)
    (a.out/(c['module']+'.v')).write_text(text)
    (a.out/'provenance.json').write_text(json.dumps(ledger,indent=2)+'\n')
