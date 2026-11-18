"""Rebuild original-budget LFP certificates from raw RTL dependency rows.

No existing CPU invariant, theorem profile or searched replacement fuel is an
input. A separately checked data-only configuration binding can supply the
actual configured AST. Full-state results retain shape/event obligations.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_dependency_catalog as catalog
import cpu_bounded_catalog_phase as phase
import cpu_known_producers as producers
import cpu_phase_from_known as ordered
ROOT=origin.ROOT


def proposal(ast_path,ast_module,cache_rows=False):
    if type(cache_rows)is not bool:raise ValueError('catalog cache mode must be boolean')
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);profile['coq_load_paths']=paths
    actual,rows,unsupported,source=catalog.proposal(profile,cache_rows)
    if actual['source_sha256']!=ast['source_sha256']:raise ValueError('raw AST changed while generating runtime catalog')
    data=dict(ast_sha256=ast['source_sha256'],program=profile['ast']['program'],coq_load_paths=paths,
        processes=rows,unsupported_slices=unsupported,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        fuel_changed=False,cache_rows=cache_rows,original_runtime_ready_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    return profile,json.loads(json.dumps(data)),source


def check(ast_path,ast_module,output,timeout=1200,cache_rows=False,shard_size=0):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    if type(cache_rows)is not bool:raise ValueError('catalog cache mode must be boolean')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    profile,data,source=proposal(ast_path,ast_module,cache_rows)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    result=dict(accepted=False,scope='raw original-budget full-state phase under explicit shape/event predicates; not runtime Ready or ISA',
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,fuel_changed=False,cache_rows=cache_rows,
        ast_sha256=data['ast_sha256'],actual_program=data['program'],catalog_accepted=False,
        full_phase_under_shape_proved=False,full_phase_without_shape_proved=False,shape_initialization_proved=False,
        original_runtime_ready_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    start=time.monotonic();deadline=start+timeout
    c=catalog.check(profile,output/'catalog',timeout,cache_rows,shard_size);result['catalog']=c;result['catalog_accepted']=c['accepted']
    if c['accepted']:
        path=output/'catalog'/'Catalog.v';obj=path.with_suffix('.vo')
        if path.read_text()!=source or c['source_sha256']!=hashlib.sha256(source.encode()).hexdigest():
            raise ValueError('native catalog differs from raw proposal')
        result['catalog_object_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest()
        metadata=c['metadata'];result['original_budget']=metadata['budget']
        if metadata['converges']and metadata['covers_writers']:
            remaining=deadline-time.monotonic()
            if remaining>0:
                p=phase.check(profile,output/'catalog',output/'phase',remaining)
                result['phase']=p;result['accepted']=p['accepted'];result['full_phase_under_shape_proved']=p['accepted']
                if p['accepted']:result['phase_object_sha256']=hashlib.sha256((output/'phase'/'Phase.vo').read_bytes()).hexdigest()
            else:result['residual']='point budget exhausted before full phase; retain catalog only'
        else:result['residual']='original-budget convergence or complete writer coverage is unproved; do not deepen fuel'
    else:result['residual']='raw dependency catalog failed native validation; no old CPU proof fallback'
    # A different checked proof rule, not a replacement Program or a fuel
    # increase. Producer idempotence can cover outputs absent from this catalog.
    if c['accepted']and not result['accepted']and time.monotonic()<deadline:
        remaining=deadline-time.monotonic()
        k=producers.check_profile(profile,output/'producers',remaining)
        result['producers']=k
        if k.get('accepted')and k.get('complete_original_producer_list_proved')and time.monotonic()<deadline:
            o=ordered.check(profile,output/'producers',output/'ordered-phase',deadline-time.monotonic())
            result['ordered_phase']=o
            if o['accepted']:
                result.update(accepted=True,strategy='checked_ordered_producers',full_phase_without_shape_proved=True,
                    phase_object_sha256=hashlib.sha256((output/'ordered-phase'/'Phase.vo').read_bytes()).hexdigest())
                result.pop('residual',None)
    result['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--shard-size',type=int,default=0,help='default-off: shard the dependency catalog (same final statements)')
    p.add_argument('--cache-rows',action='store_true',help='explicit checked static-value experiment; not enabled by default');a=p.parse_args()
    result=check(a.ast,a.ast_module,a.output,cache_rows=a.cache_rows,shard_size=a.shard_size)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
