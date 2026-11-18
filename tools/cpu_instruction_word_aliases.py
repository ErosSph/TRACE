"""Trace field-source word aliases and prove them at the actual CombLFP.

Only unique, direct, full 32-bit blocking aliases are traversed. Sequential
carriers and mux/computed sources are reported as boundaries, never bypassed.
The boundary is NOT automatically identified with the ISA's current word.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_auto_adapter as adapter
import cpu_comb_scalar_bindings as comb
import cpu_instruction_fields as fields
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def sources(ast):
    selected=fields.discover(ast);result=set()
    for proc in ast['processes']:
        if proc['kind'] not in selected:continue
        for st in adapter.walk(proc['body']):
            if st.name!='SAssign' or st.args[2].name!='LVar':continue
            width,root=map(lambda x:int(x.name),st.args[2].args)
            if root not in selected[proc['kind']]:continue
            for _,leaf in fields.paths.leaf_paths(st.args[1],width):
                item=fields.match_field(leaf,width)
                if item:result.add(item['source'])
    return sorted(result)


def trace(ast,source,budget=256):
    edges=[];seen=set();current=source
    for _ in range(budget):
        if current in seen:raise ValueError('word alias cycle')
        seen.add(current)
        writers=[p for p in ast['processes'] if current in p['writers']]
        if len(writers)!=1:return dict(source=source,terminal=current,edges=edges,boundary='non_unique_or_external_source')
        proc=writers[0]
        if proc['kind']=='Sequential':return dict(source=source,terminal=current,edges=edges,boundary='sequential_carrier')
        body=proc['body']
        if proc['kind']!='Combinational' or body.name!='SAssign':
            return dict(source=source,terminal=current,edges=edges,boundary='non_alias_process')
        nba,rhs,lhs=body.args
        if nba.name!='false' or rhs.name!='EVar' or rhs.args[0].name!='32' or \
           lhs.name!='LVar' or lhs.args[0].name!='32':
            return dict(source=source,terminal=current,edges=edges,boundary='conditional_or_computed_source')
        parent=int(rhs.args[1].name)
        edges.append(dict(root=current,parent=parent,process=proc['name']))
        current=parent
    raise ValueError('word alias depth budget exhausted')


def proposal(profile):
    ast=adapter.load_ast(adapter.ROOT/profile['ast']['file'])
    chains=[];residuals=[]
    for source in sources(ast):
        try:chains.append(trace(ast,source))
        except ValueError as exc:residuals.append(dict(source=source,reason=str(exc)))
    roots=sorted({edge['root'] for item in chains for edge in item['edges']})
    if roots:
        _,analysis,prefix=comb.proposal(profile,roots)
        residuals+=analysis['residuals']
        prefix=re.sub(r'RF_PORT_ASSUMPTIONS_(\d+)',lambda m:'AUTO_ADAPTER_ASSUMPTIONS_'+m.group(1),prefix)
        count=prefix.count('Print Assumptions ')
        port_for={item['output_root']:n for n,item in enumerate(analysis['ports'])}
    else:
        imports=[profile['ast']['module'],*profile['ast'].get('program_imports',[])]
        prefix='From Coq Require Import List ZArith.\nRequire Import Lang.ExtendedSV '+ ' '.join(imports)+'.\nImport ExtendedSV.\n'
        count=0;port_for={}
    lines=['Require Import Ex.External.CPUInstructionFields Ex.External.CPUInstructionFieldAlias',
        ' Lang.ExtendedSVWordInvariant.',
        'Import CPUInstructionFields CPUInstructionFieldAlias ExtendedSVWordInvariant.']
    program=profile['ast']['program']
    for chain in chains:
        source,terminal=chain['source'],chain['terminal'];term='eq_refl'
        for edge in reversed(chain['edges']):
            root,parent=edge['root'],edge['parent'];index=port_for[root]
            step=f'(eq_trans (port_{index}_lfp seed fixed HL) (norm_idempotent 32 (read_signal fixed {parent}%nat)))'
            term=f'(eq_trans {step} {term})'
        lines += [f'Theorem source_{source}_word_origin seed fixed : CombLFP {program} seed fixed ->',
            f' norm 32 (read_signal fixed {source}%nat)=norm 32 (read_signal fixed {terminal}%nat).',
            f'Proof. intro HL. exact {term}. Qed.',
            f'Theorem source_{source}_field_origin seed fixed field : CombLFP {program} seed fixed ->',
            f' field_reference (read_signal fixed {source}%nat) field=',
            f' field_reference (read_signal fixed {terminal}%nat) field.',
            f'Proof. intro HL. exact (field_reference_alias _ _ field (source_{source}_word_origin seed fixed HL)). Qed.']
        for suffix in ['word_origin','field_origin']:
            lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions source_{source}_{suffix}.']
            count+=1
    return ast,residuals,chains,prefix+'\n'.join(lines)+'\n',count


def emit_library(profile,destination,check=False):
    """Emit the exact word-origin library; source matching is not a proof."""
    _,residuals,chains,source,count=proposal(profile)
    if residuals or not chains:raise ValueError('unsupported word alias selection')
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent word alias source differs from generation')
    elif path.exists():raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        chains=len(chains),audited_exports=count,source_matches_generator=True,coq_checked=False,
        current_isa_token_identity_proved=False)


def check_profile(profile,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,chains,source,count=proposal(profile)
    file=output/'InstructionWordAliases.v';file.write_text(source)
    report=dict(accepted=False,ast_sha256=ast['source_sha256'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),actual_program=profile['ast']['program'],
        chains=chains,nontrivial_alias_edges=len({e['root'] for c in chains for e in c['edges']}),
        residuals=residuals,audited_exports=count,llm_calls=0,
        current_isa_token_identity_proved=False,global_invariant_synthesized=False)
    if residuals or not chains:report['status']='unsupported_word_alias_selection'
    else:
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedInstructionWordAliases']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedInstructionWordAliases.InstructionWordAliases'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True);p.add_argument('--output',type=Path)
    p.add_argument('--emit-source',type=Path);p.add_argument('--check-source',action='store_true')
    p.add_argument('--timeout',type=float,default=1200);a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    if bool(a.output)==bool(a.emit_source):p.error('choose exactly one of --output and --emit-source')
    if a.check_source and not a.emit_source:p.error('--check-source requires --emit-source')
    profile=json.loads(a.profile.read_text())
    if a.emit_source:
        print(json.dumps(emit_library(profile,a.emit_source,a.check_source),indent=2));return 0
    r=check_profile(profile,a.output,a.timeout)
    print(json.dumps(r,indent=2));return 0 if r['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
