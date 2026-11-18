"""Discover original selector-input provenance, preserving sampling boundaries.

Only equal-width whole scalar copies are traversed. Computed terminals and
sequential terminals are explicit; neither is assumed to be an ISA token.
"""
import argparse
import json
from pathlib import Path
import cpu_blocking_selector as selectors
rtl=selectors.rtl


def trace(ast,width,root):
    start=root;edges=[];seen=set()
    while root not in seen:
        seen.add(root)
        writers=[p for p in ast['processes'] if p['kind']!='Initial' and root in p['writers']]
        if not writers:return dict(input=start,width=width,terminal=root,kind='external',edges=edges)
        if len(writers)!=1:return dict(input=start,width=width,terminal=root,kind='multiple_writers',edges=edges)
        proc=writers[0]
        if proc['kind']=='Sequential':
            return dict(input=start,width=width,terminal=root,kind='sequential',process=proc['name'],events=proc['events'],edges=edges)
        body=selectors.branches.cases.unwrap(proc['body'])
        if body.name!='SAssign' or body.args[0].name!='false' or \
           body.args[2]!=rtl.Term('LVar',(rtl.Term(str(width)),rtl.Term(str(root)))) or \
           body.args[1].name!='EVar' or body.args[1].args[0].name!=str(width):
            return dict(input=start,width=width,terminal=root,kind='computed',process=proc['name'],edges=edges)
        parent=int(body.args[1].args[1].name)
        edges.append(dict(root=root,parent=parent,width=width,process=proc['name']))
        root=parent
    return dict(input=start,width=width,terminal=root,kind='cycle',edges=edges)


def discover(ast):
    plan=selectors.discover(ast);sources=[]
    for row in plan['selected']:
        expr=rtl.Parser(row['expression']).complete()
        inputs=sorted({tuple(int(a.name) for a in n.args) for n in rtl.walk(expr) if n.name=='EVar'})
        for width,root in inputs:
            sources.append(dict(selector=row['root'],**trace(ast,width,root)))
    return dict(sources=sources,selector_residuals=plan['residuals'],
        upstream_route_residuals=plan['upstream_route_residuals'],
        old_inv_read=False,token_ownership_proved=False,complete_R_generated=False)


def render(ast_path,ast_module):
    ast,profile,paths=selectors.origin.raw_binding(ast_path,ast_module)
    plan=discover(ast)
    from cpu_rf_read_ports import render as render_ports
    combs=[p for p in ast['processes'] if p['kind']=='Combinational']
    edges={e['root']:e for row in plan['sources'] for e in row['edges']}
    blocks=[];ports=[]
    for root,edge in sorted(edges.items()):
        proc=next(p for p in combs if p['name']==edge['process'])
        st=selectors.branches.cases.unwrap(proc['body'])
        blocks.append(dict(process=proc['name'],comb_index=combs.index(proc),assignments=[st]))
        ports.append(dict(block_index=len(blocks)-1,assignment_index=0,process=proc['name'],
            width=edge['width'],output_root=root,rhs=st.args[1]))
    source=render_ports(profile['ast'],ast,dict(blocks=blocks,ports=ports,residuals=[]),opaque_single=True)
    lines=['Require Import Lang.ExtendedSVWordInvariant.','Import ExtendedSVWordInvariant.']
    indices={p['output_root']:i for i,p in enumerate(ports)}
    unique={(r['width'],r['input']):r for r in plan['sources'] if r['edges']}
    program=profile['ast']['program'];count=len(ports)
    for i,row in enumerate(unique.values()):
        width=row['width'];term='eq_refl'
        for edge in reversed(row['edges']):
            n=indices[edge['root']]
            step=f'(eq_trans (port_{n}_lfp seed fixed HL) (norm_idempotent {width} (read_signal fixed {edge["parent"]})))'
            term=f'(eq_trans {step} {term})'
        lines += [f'Theorem selector_source_{i} seed fixed : CombLFP {program} seed fixed ->',
            f' norm {width}(read_signal fixed {row["input"]})=norm {width}(read_signal fixed {row["terminal"]}).',
            f'Proof. intro HL. exact {term}. Qed.',
            f'Goal True. idtac "RF_PORT_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions selector_source_{i}.']
        count+=1
    return plan,source+'\n'.join(lines)+'\n',paths,count


def check(ast_path,ast_module,output):
    import hashlib,time
    import cpu_rf_read_ports as ports
    from cpu_certificate_acceptance import run_stage
    plan,source,paths,count=render(ast_path,ast_module)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    report=dict(accepted=False,equation_count=count,token_ownership_proved=False,
        complete_R_generated=False,old_inv_read=False,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if count:
        path=output/'SelectorSources.v';path.write_text(source)
        flags=list(rtl.framework.FLAGS)
        for row in paths:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedSelectorSources']
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(selectors.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
        report.update(coqc_exit=c.returncode,coqc_timed_out=t)
        if c.returncode==0 and time.monotonic()<deadline:
            report['assumptions_closed']=ports.audit_output(c.stdout,count)
            k,t=run_stage([str(selectors.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedSelectorSources.SelectorSources'],output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
        report['seconds']=time.monotonic()-start
    else:report['status']='no_copy_edges_not_a_completeness_claim'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
