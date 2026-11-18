#!/usr/bin/env python3
"""Build a fresh dependency-ordered proof bundle from an explicit manifest.

Framework renderers produce theorem instances; inherited helper/consumer sources
are labelled separately. Every checked node gets immediate coqc, own-module
coqchk, and an assumptions audit. Existing outputs are never reused or rewritten.
External generic libraries and design providers must already be built.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import cpu_seed_families
import cpu_generalized_assembly
import cpu_initial_view
from cpu_generalization_check import ROOT, check, run
from cpu_rule_promote import strip_coq_comments

def plan(manifest, selected=None):
    stages=manifest['stages'];nodes={s['id']:s for s in stages}
    if len(nodes)!=len(stages):raise ValueError('duplicate stage id')
    if set(nodes)&{n+'-source' for n in nodes}:raise ValueError('stage name collides with a generated-source directory')
    namespaces=[s['namespace'] for s in stages]
    if len(namespaces)!=len(set(namespaces)):raise ValueError('duplicate stage namespace')
    for name,s in nodes.items():
        if not re.fullmatch(r'[a-zA-Z0-9_-]+',name):raise ValueError('invalid stage id')
        if s['namespace'] in manifest.get('forbidden_namespaces',[]):raise ValueError('forbidden stage namespace')
        if set(s.get('needs',[]))-nodes.keys():raise ValueError('unknown dependency in '+name)
    ordered=[];visiting=set();visited=set()
    def visit(name):
        if name not in nodes:raise ValueError('unknown selected stage '+name)
        if name in visiting:raise ValueError('dependency cycle at '+name)
        if name in visited:return
        visiting.add(name)
        for dep in nodes[name].get('needs',[]):visit(dep)
        visiting.remove(name);visited.add(name);ordered.append(nodes[name])
    for name in selected or nodes:visit(name)
    return ordered

def external_providers(stage, manifest):
    controlled={s['namespace'] for s in manifest['stages']}
    forbidden=set(manifest.get('forbidden_namespaces',[]))
    rows=json.loads((ROOT/stage['providers']).read_text()) if stage.get('providers') else []
    result={}
    for p in rows:
        if p['namespace'] in controlled|forbidden:continue
        directory=Path(p['directory'])
        if not directory.is_absolute():directory=ROOT/directory
        if p['namespace'] in result and result[p['namespace']]!=str(directory):
            raise ValueError('conflicting external provider '+p['namespace'])
        result[p['namespace']]=str(directory)
    return result

def checked_loadpaths(stage,manifest,providers):
    reserved={s['namespace'] for s in manifest['stages']}|set(manifest.get('forbidden_namespaces',[]))
    known={k:str(Path(v).resolve()) for k,v in providers.items()};rows=[]
    for row in stage.get('loadpaths',[]):
        ns=row['namespace'];directory=str((ROOT/row['directory']).resolve())
        if ns in reserved:raise ValueError('explicit loadpath shadows a reserved namespace '+ns)
        if ns in known and known[ns]!=directory:raise ValueError('conflicting explicit loadpath '+ns)
        known[ns]=directory;rows.append(dict(namespace=ns,directory=directory))
    return rows

def uses_namespace(code,namespace):
    name=re.escape(namespace)
    return bool(re.search(r'\b'+name+r'\.',code) or re.search(r'\bFrom\s+'+name+r'(?=[.\s])',code))

def render_stage(stage, generated):
    kind=stage['kind'];ledger=[];start=time.monotonic();generation=None
    if kind=='seed_family':
        schema=ROOT/stage['schema'];config=json.loads(schema.read_text())
        text,ledger=cpu_seed_families.render(config,schema.parent)
        name=config['module']+'.v'
    elif kind=='obligation_record':
        config=json.loads((ROOT/stage['schema']).read_text())
        text=cpu_generalized_assembly.render(config);name=config['module']+'.v'
    elif kind=='source':
        source=ROOT/stage['source'];text=source.read_text();name=source.name
    elif kind=='command':
        name=stage['module']+'.v';target=generated/name
        cmd=[arg.replace('{source}',str(target)).replace('{generated}',str(generated)) for arg in stage['argv']]
        generation=run(cmd,generated/'generator.log')
        if generation['exit']:raise ValueError('generator exited '+str(generation['exit']))
        text=target.read_text()
    else:raise ValueError('unknown stage kind '+kind)
    initial_view_started=time.monotonic()
    text,initial_view_ledger=cpu_initial_view.instantiate(text,Path(name).stem,stage.get('initial_view_lemma',cpu_initial_view.DEFAULT_LEMMA),stage.get('initial_view_import'))
    initial_view_seconds=time.monotonic()-initial_view_started if initial_view_ledger else 0.0
    target=generated/name
    if kind!='command' or initial_view_ledger:target.write_text(text)
    metadata=dict(kind=kind,origin=stage['origin'],narrow_llm_written=stage.get('narrow_llm_written',False),
        seconds=time.monotonic()-start,source_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
        exports=ledger,generator_measurement=generation,initial_view_proof_instances=initial_view_ledger,initial_view_generation_seconds=initial_view_seconds)
    (generated/'generation.json').write_text(json.dumps(metadata,indent=2)+'\n')
    return target,metadata

def build(manifest, manifest_path, out, jobs, selected=None, generate_only=False):
    stages=plan(manifest,selected);nodes={s['id']:s for s in stages}
    out.mkdir(parents=True,exist_ok=False)
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    results={};pending=set(nodes);running={};started=time.monotonic()
    def dependencies(name):
        found=set()
        def visit(n):
            for d in nodes[n].get('needs',[]):
                if d not in found:found.add(d);visit(d)
        visit(name)
        return found
    def one(stage):
        name=stage['id'];generated=out/(name+'-source');generated.mkdir()
        try:
            source,generation=render_stage(stage,generated)
            code=strip_coq_comments(source.read_text())
            forbidden=manifest.get('forbidden_namespaces',[])
            if any(uses_namespace(code,ns) for ns in forbidden):
                raise ValueError('source still references a forbidden legacy provider')
            providers=external_providers(stage,manifest)
            loadpaths=checked_loadpaths(stage,manifest,providers)
            for dep in dependencies(name):providers[nodes[dep]['namespace']]=str(out/dep)
            rows=[dict(namespace=k,directory=v) for k,v in sorted(providers.items())]
            if generate_only:return dict(id=name,status='generated_not_checked',generation=generation)
            gate=check(source,out/name,stage['namespace'],rows,loadpaths)
            return dict(id=name,status='accepted' if gate['accepted'] else 'failed',generation=generation,
                        evidence=str((out/name).relative_to(ROOT)) if out.is_relative_to(ROOT) else str(out/name),gate=gate)
        except Exception as error:
            failure=dict(id=name,status='failed',error=repr(error))
            (generated/'failure.json').write_text(json.dumps(failure,indent=2)+'\n')
            return failure
    def snapshot():
        report=dict(manifest=str(manifest_path),generate_only=generate_only,jobs=jobs,
            elapsed_seconds=time.monotonic()-started,results=[results[s['id']] for s in stages if s['id'] in results],
            pending=sorted(pending),running=sorted(running.values()))
        temporary=out/'bundle.tmp';temporary.write_text(json.dumps(report,indent=2)+'\n');temporary.replace(out/'bundle.json')
        return report
    snapshot()
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            for stage in stages:
                name=stage['id']
                if name not in pending:continue
                needs=stage.get('needs',[])
                if not all(d in results for d in needs):continue
                pending.remove(name)
                if any(results[d]['status'] in ('failed','blocked') for d in needs):
                    results[name]=dict(id=name,status='blocked',reason='a required dependency failed')
                else:running[pool.submit(one,stage)]=name
            snapshot()
            if running:
                # Long kernel checks may produce no completed future for many
                # minutes. Refresh the live snapshot without delaying checks.
                finished,_=wait(running,timeout=5,return_when=FIRST_COMPLETED)
                for future in finished:
                    name=running.pop(future);results[name]=future.result()
            elif pending:raise ValueError('unschedulable dependency graph')
    report=snapshot()
    report['accepted']=not generate_only and all(r['status']=='accepted' for r in results.values())
    report['complete']=all(r['status'] in ('accepted','generated_not_checked') for r in results.values())
    (out/'bundle.json').write_text(json.dumps(report,indent=2)+'\n')
    return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('manifest',type=Path);parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--jobs',type=int,default=4);parser.add_argument('--only',nargs='+')
    parser.add_argument('--generate-only',action='store_true');a=parser.parse_args()
    if a.jobs<1:parser.error('jobs must be positive')
    os.chdir(ROOT);manifest=json.loads(a.manifest.read_text())
    report=build(manifest,a.manifest,a.out.resolve(),a.jobs,a.only,a.generate_only)
    print(json.dumps({k:v for k,v in report.items() if k!='results'},indent=2))
    raise SystemExit(0 if report['complete'] else 1)
