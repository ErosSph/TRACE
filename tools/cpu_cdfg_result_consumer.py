"""Use a CDFG query to select, then independently prove, a Coq result cone.

Dependency agreement is an admission check, NOT an expression equivalence proof.
The theorem is about the original Coq Program and its original expressions.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
from cpu_pyslang_cdfg import backward_slice
import cpu_result_cone as cone
from cpu_pending_origins import raw_binding, ROOT
from cpu_certificate_acceptance import run_stage
from cpu_pyslang_binding import analyze


def validate_replay(graph, replayed):
    if graph != replayed:
        raise ValueError('graph differs from fresh pinned-source elaboration')


def checked_graph(graph_path, ast, replay_directory):
    graph=json.loads(Path(graph_path).read_text())
    binding=json.loads(Path(graph_path).with_name('binding.json').read_text())
    if hashlib.sha256(Path(ast).read_bytes()).hexdigest()!=binding['ast_sha256']:
        raise ValueError('configured AST changed since binding')
    if hashlib.sha256(Path(binding['import_report']).read_bytes()).hexdigest()!=binding['report_sha256']:
        raise ValueError('import report changed since binding')
    analyze(binding['import_report'], ast, replay_directory)
    validate_replay(graph,json.loads((Path(replay_directory)/'cdfg.json').read_text()))
    if graph['obligations']:raise ValueError('unresolved graph obligations')
    return graph


def agree(graph, query, plan):
    if graph['obligations']: raise ValueError('unresolved elaboration graph obligations')
    by_path={s['path']:s for s in graph['symbols']}
    nodes={n['symbol']['coq_root']:n for n in query['nodes']}
    if set(nodes)!={n['root'] for n in plan['nodes']}:
        raise ValueError('graph/Coq node coverage mismatch')
    for n in plan['nodes']:
        g=nodes[n['root']]
        deps=sorted((by_path[p]['width'],by_path[p]['coq_root']) for p in g['dependencies'])
        if g['symbol']['width']!=n['width'] or deps!=sorted(map(tuple,n['dependencies'])):
            raise ValueError('graph/Coq dependency or width mismatch')
    gb={(by_path[p]['width'],by_path[p]['coq_root'],why) for p,why in query['boundaries'].items()}
    cb={(n['width'],n['root'],n['reason']) for n in plan['boundaries']}
    if gb!=cb: raise ValueError('graph/Coq state boundary mismatch')


def check(graph_path, ast, module, target, output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    graph=checked_graph(graph_path,ast,output/'replayed')
    query=backward_slice(graph,target)
    symbol=next(s for s in graph['symbols'] if s['path']==target)
    raw,profile,paths=raw_binding(ast,module)
    plan=cone.cone(raw,symbol['width'],symbol['coq_root'])
    agree(graph,query,plan)
    profile['coq_load_paths']=paths
    source=cone.render(ast,module,raw,profile,plan)
    file=output/'CDFGResult.v';file.write_text(source)
    (output/'query.json').write_text(json.dumps(query,indent=2)+'\n')
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    flags=list(cone.rtl.framework.FLAGS)
    for p in paths:flags+=['-R',p['directory'],p['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedCDFGResult']
    start=time.monotonic()
    c,t=run_stage(['/usr/bin/time','-v','-o',str((output/'coqc.resources').resolve()),
                  str(ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        graph_sha256=hashlib.sha256(Path(graph_path).read_bytes()).hexdigest(),
        dependency_agreement=True,translation_equivalence_proved=False,
        isa_result_proved=False,complete_R_generated=False,itree_refinement_proved=False)
    if c.returncode==0:
        tail=c.stdout.split('RESULT_CONE_AUDIT')[-1]
        closed=tail.count('Closed under the global context')==len(plan['nodes']) and 'Axioms:' not in tail
        remaining=1200-(time.monotonic()-start)
        if remaining>0:
            k,t=run_stage(['/usr/bin/time','-v','-o',str((output/'coqchk.resources').resolve()),
                          str(ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCDFGResult.CDFGResult'],output/'coqchk.log',remaining)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,
                          accepted=closed and k.returncode==0)
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['graph','ast','module','target','output']:p.add_argument('--'+arg,required=True)
    a=p.parse_args();r=check(a.graph,a.ast,a.module,a.target,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
