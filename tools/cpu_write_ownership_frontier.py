"""Per-write address/data/control sampling boundaries from raw RTL only.

Unlike a bank-wide dependency union, this retains individual writes and order.
Shared sampling boundaries are evidence for a candidate, NOT token identity.
"""
import argparse
import json
from pathlib import Path
import cpu_bank_adapter as bank
import cpu_pending_origins as origin
rtl=bank.adapter


def leaves(plan, path=(), guards=()):
    if plan.name=='BPEmpty':return
    if plan.name in ('BPWord','BPReset'):
        yield path,guards,plan
    elif plan.name=='BPSeq':
        for i,child in enumerate(plan.args[0].args):
            yield from leaves(child,path+(i,),guards)
    elif plan.name=='BPIf':
        guard,yes,no=plan.args
        yield from leaves(yes,path+(0,),guards+((guard,True),))
        yield from leaves(no,path+(1,),guards+((guard,False),))
    else:raise ValueError('unknown bank plan; no silently missing writes')


def frontier(ast, seeds):
    writers={}
    for proc in ast['processes']:
        for root in proc['writers']:writers.setdefault(root,[]).append(proc)
    todo=list(seeds);seen=set();boundaries={};external=[];edges=[]
    while todo:
        root=todo.pop()
        if root in seen:continue
        seen.add(root);ps=writers.get(root,[])
        if not ps:external.append(root);continue
        if any(p['kind']!='Combinational' for p in ps):
            boundaries[root]=[dict(process=p['name'],kind=p['kind'],events=p['events'])for p in ps]
            continue
        for p in ps:
            reads=origin.pending.roots(p['body'])
            edges.append(dict(root=root,process=p['name'],reads=reads))
            todo.extend(reads)
    return dict(seeds=sorted(set(seeds)),boundaries={str(k):v for k,v in sorted(boundaries.items())},
                external_inputs=sorted(external),combinational_edges=edges,
                process_wide_reads_are_overapproximate=True)


def analyze(ast):
    analysis=bank.analyze(ast);writes=[]
    for b in analysis['banks']:
        for writer_index,(proc,_,plan) in enumerate(b['plans']):
            for path,guards,leaf in leaves(plan):
                reset=leaf.name=='BPReset'
                address=None if reset else leaf.args[0]
                data=leaf.args[0]if reset else leaf.args[1]
                constant=None if reset else bank.literal(address)
                if reset:
                    destination=dict(kind='whole_bank',obligation='establish all affected architectural lanes; do not assume reset')
                elif constant is not None:
                    if constant%32:raise ValueError('unaligned constant lane; checked bank plan required')
                    destination=dict(kind='fixed_lane',lane=constant//32,
                        obligation='selected guard implies this lane is the instruction destination or a permitted x0 write')
                else:
                    destination=dict(kind='dynamic_offset',
                        obligation='sampled normalized offset / 32 equals the instruction destination')
                control=set().union(*(set(origin.pending.roots(g))for g,_ in guards))
                parts=dict(data=frontier(ast,origin.pending.roots(data)),
                    address=frontier(ast,[] if reset else origin.pending.roots(address)),
                    control=frontier(ast,control))
                shared=set(parts['data']['boundaries'])&set(parts['address']['boundaries'])
                writes.append(dict(bank=b['root'],writer_index=writer_index,process=proc['name'],
                    events=proc['events'],path=list(path),kind='whole_bank_write'if reset else 'lane_write',
                    offset=None if reset else rtl.render(address),data=rtl.render(data),
                    destination=destination,
                    guards=[dict(expression=rtl.render(g),taken=t)for g,t in guards],frontiers=parts,
                    shared_data_address_boundaries=sorted(map(int,shared)),
                    shared_boundary_proves_identity=False,token_ownership_proved=False,
                    obligations=['actual selected branch','same instruction instance for address and data',
                        'sampled instruction corresponds to pending token','retirement/flush eligibility']))
    return dict(ast_sha256=ast['source_sha256'],writes=writes,residuals=analysis['residuals'],
        old_inv_read=False,source_of_analysis='complete structural bank plans',
        semantic_slice_proved=False,token_ownership_proved=False,complete_R_generated=False)


def run(ast_path,ast_module,output):
    ast,_,_=origin.raw_binding(ast_path,ast_module)
    plan=analyze(ast);out=Path(output);out.mkdir(parents=True,exist_ok=False)
    (out/'ownership-frontier.json').write_text(json.dumps(plan,indent=2)+'\n')
    return dict(writes=len(plan['writes']),whole_bank_writes=sum(w['kind']=='whole_bank_write'for w in plan['writes']),
        no_shared_data_address_boundary=sum(not w['shared_data_address_boundaries']for w in plan['writes']),
        residuals=plan['residuals'],token_ownership_proved=False,complete_R_generated=False)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();print(json.dumps(run(a.ast,a.ast_module,a.output),indent=2))
