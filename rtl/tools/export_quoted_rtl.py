#!/usr/bin/env python3
"""Auditable export of the supported module-quotation subset to SystemVerilog.

VerilRocq named connections use logical vid names, not necessarily child
declaration spellings. Resolve them through existing notation tables, never
by stripping prefixes or guessing from CPU signal names. This exporter is
not a mechanized Coq AST/SystemVerilog equivalence proof.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

QUOTATION = re.compile(r"#\[\s*(module\s+(\w+)\b[\s\S]*?\bendmodule)\s*\]\.")
NOTATION = re.compile(r'Notation\s+"\'([A-Za-z_][A-Za-z_0-9]*)\'"\s*:=\s*([A-Za-z_][A-Za-z_0-9]*)\s*\(in custom (ce_expr|ce_portconnid|ce_top)\)\.')

def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()

def remove_coq_comments(text: str) -> str:
    """Preserve source offsets/newlines; ignore nested comments and strings."""
    out=list(text); depth=0; quoted=False; i=0
    while i<len(text):
        pair=text[i:i+2]
        if not depth and text[i]=='"': quoted=not quoted; i+=1; continue
        if not quoted and pair=='(*':
            depth+=1; out[i:i+2]=[' ',' ']; i+=2; continue
        if depth and pair=='*)':
            depth-=1; out[i:i+2]=[' ',' ']; i+=2; continue
        if depth and text[i]!='\n': out[i]=' '
        i+=1
    if depth: raise ValueError('unterminated Coq comment')
    return ''.join(out)

def split_arguments(text: str) -> list[str]:
    result, start, stack = [], 0, []
    closers = {')':'(', ']':'[', '}':'{'}
    for i, char in enumerate(text):
        if char in '([{': stack.append(char)
        elif char in ')]}':
            if not stack or stack.pop() != closers[char]:
                raise ValueError('unbalanced connection expression')
        elif char == ',' and not stack:
            result.append(text[start:i].strip()); start=i+1
    if stack: raise ValueError('unbalanced connection expression')
    if text[start:].strip(): result.append(text[start:].strip())
    return result

def collect(paths: list[Path]) -> dict:
    modules = {}
    for path in paths:
        text = path.read_text()
        scanned=remove_coq_comments(text)
        for match in QUOTATION.finditer(scanned):
            body, name = match.group(1), match.group(2)
            if name in modules: raise ValueError(f'duplicate module {name}')
            # Every supplied quotation belongs to its own Module M section.
            section = scanned.rfind('Module M.', 0, match.start())
            if section < 0: raise ValueError(f'{name}: missing quotation namespace')
            tables = {'ce_expr':{}, 'ce_portconnid':{}, 'ce_top':{}}
            for alias, vid, category in NOTATION.findall(scanned[section:match.start()]):
                if alias in tables[category] and tables[category][alias] != vid:
                    raise ValueError(f'{name}: ambiguous notation {alias}')
                tables[category][alias]=vid
            header = body[:body.index(';')]
            port_ids = {}
            for alias in re.findall(r'\b(?:input|output)\s+logic\s*(?:\[[^\]]+\]\s*)*(\w+)', header):
                if alias not in tables['ce_expr']:
                    raise ValueError(f'{name}: port {alias} has no declared vid notation')
                vid=tables['ce_expr'][alias]
                if vid in port_ids: raise ValueError(f'{name}: duplicate vid {vid}')
                port_ids[vid]=alias
            if not port_ids: raise ValueError(f'{name}: no supported logic ports')
            modules[name]={'body':body, 'source':str(path.resolve()),
                'source_sha256':digest(text), 'line':text[:match.start(1)].count('\n')+1,
                'quotation_sha256':digest(text[match.start(1):match.end(1)]),
                'comment_stripped_sha256':digest(body), 'port_ids':port_ids,
                'port_notations':tables['ce_portconnid']}
    if not modules: raise ValueError('no supported module quotations')
    return modules

def convert(modules: dict) -> dict:
    outputs = {}
    for name, info in modules.items():
        connections=[]
        pattern=re.compile(r'(?m)^([ \t]*)(\w+)\s+(\w+)\s*\(([\s\S]*?)\);')
        def instance(match):
            indent, child, label, args=match.groups()
            if child == 'module': return match.group(0)
            if child not in modules:
                raise ValueError(f'{name}.{label}: child {child} not supplied')
            rendered, seen=[],set()
            for argument in split_arguments(args):
                arg=re.fullmatch(r'(\w+)\s*\(([\s\S]*)\)',argument)
                if not arg: raise ValueError(f'{name}.{label}: unsupported connection {argument}')
                alias, expr=arg.groups()
                vid=info['port_notations'].get(alias)
                if vid is None: raise ValueError(f'{name}.{label}: unresolved parent port {alias}')
                port=modules[child]['port_ids'].get(vid)
                if port is None: raise ValueError(f'{name}.{label}: {vid} not in child {child}')
                if vid in seen: raise ValueError(f'{name}.{label}: repeated port {vid}')
                seen.add(vid)
                rendered.append(f'.{port}({expr})')
                connections.append({'instance':label,'child':child,'vid':vid,
                    'quotation_port':alias,'rtl_port':port,'expression':expr})
            return f'{indent}{child} {label}('+', '.join(rendered)+');'
        rtl=pattern.sub(instance,info['body'])+'\n'
        # Semantics.v:178-183 fixes unsized based decimal numbers to32 bits.
        # SV concatenations reject the unsized spelling even for zero.
        rtl,zero_concat_count=re.subn(r"\{\s*'d0\s*\}","{32'd0}",rtl)
        outputs[name]={**info,'rtl':rtl,'rtl_sha256':digest(rtl),'connections':connections,
            'literal_normalizations':{'single_unsized_zero_concat_to_32bit':zero_concat_count}}
    return outputs

def replace_modules(modules: dict, replacements: dict) -> dict:
    result=dict(modules)
    for name,new in replacements.items():
        if name not in result: raise ValueError(f'replacement {name} has no original module')
        old=result[name]
        header=lambda x: re.sub(r'\s+',' ',x['body'][:x['body'].index(';')]).strip()
        if old['port_ids'] != new['port_ids'] or header(old) != header(new):
            raise ValueError(f'replacement {name} changes the declaration/vid interface')
        result[name]={**new,'replaces_source':old['source'],
            'replaces_quotation_sha256':old['quotation_sha256']}
    return result

def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',type=Path,action='append',required=True)
    parser.add_argument('--replacement',type=Path,action='append',default=[],
        help='explicit same-interface corrected quotation; recorded, never silently overrides')
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    # Finish every validation before writing a partial module set.
    modules=collect(args.source)
    if args.replacement: modules=replace_modules(modules,collect(args.replacement))
    exported=convert(modules)
    args.output.mkdir(parents=True,exist_ok=True)
    manifest={'status':'quotation_export_not_semantics_equivalence_proved',
        'scope':'existing derived design, not original upstream source',
        'modules':[]}
    for name, info in exported.items():
        (args.output/(name+'.sv')).write_text(info['rtl'])
        manifest['modules'].append({k:v for k,v in info.items() if k not in
            {'body','rtl','port_notations'}} | {'module':name})
    (args.output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({'modules':len(exported),'connections':sum(len(x['connections'])
        for x in exported.values()),'status':manifest['status']}))
    return 0

if __name__=='__main__': raise SystemExit(main())
