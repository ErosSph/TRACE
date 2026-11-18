"""Follow real selector fields backwards through scalar capture candidates.

Retain every capture/hold condition and sampling boundary. Producer equations
are checked separately; their existence is not a token-history proof.
"""
import argparse,json
from pathlib import Path
import cpu_selector_sources as sources
import cpu_pending_connected_projections as captures
import cpu_scalar_expression_paths as paths
rtl=sources.rtl


def discover(ast):
    front=sources.discover(ast)
    todo={r['terminal'] for r in front['sources'] if r['kind']=='sequential'}
    scalars={r['root']:r for r in captures.scalar_candidates(ast)}
    producers={};steps=[];residuals=[];seen=set();fields=[];transforms=[]
    while todo:
        root=min(todo);todo.remove(root)
        if root in seen:continue
        seen.add(root)
        row=scalars.get(root)
        if row is None:
            residuals.append(dict(root=root,reason='no supported scalar phase expression'));continue
        w=row['width']
        fields.append(dict(root=root,width=w,process=row['process'],expression=rtl.render(row['expression'])))
        for choices,leaf in paths.leaf_paths(row['expression'],w):
            if captures.direct.is_hold(leaf,w,root) or leaf.name=='EConst':continue
            if leaf.name!='EVar' or leaf.args[0].name!=str(w):
                inputs=sorted({(int(n.args[0].name),int(n.args[1].name))
                    for n in rtl.walk(leaf) if n.name=='EVar'})
                dependencies=[dict(width=iw,root=ir,route=sources.trace(ast,iw,ir)) for iw,ir in inputs]
                transforms.append(dict(root=root,width=w,process=row['process'],
                    conditions=choices,expression=rtl.render(leaf),dependencies=dependencies,
                    identity_copy=False,reference_relation_proved=False))
                # A truncation or arithmetic transform must not disappear from
                # the capture frontier or be relabelled as an identity edge.
                for d in dependencies:
                    chain=d['route']
                    if chain['kind']=='sequential' and chain['terminal'] not in seen:
                        todo.add(chain['terminal'])
                residuals.append(dict(root=root,reason='transformed capture needs reference-function relation',
                    expression=rtl.render(leaf)));continue
            chain=sources.trace(ast,w,int(leaf.args[1].name))
            steps.append(dict(root=root,width=w,process=row['process'],
                expression=rtl.render(row['expression']),conditions=choices,source=chain))
            if chain['kind']=='sequential':
                if chain['terminal'] not in seen:todo.add(chain['terminal'])
            elif chain['kind']=='computed':
                proc=next(p for p in ast['processes'] if p['name']==chain['process'])
                try:
                    _,_,width,inputs,expr=sources.selectors.proposal(proc,chain['terminal'])
                    if width!=w:raise ValueError('producer/capture width mismatch')
                    key=(proc['name'],chain['terminal'])
                    producers[key]=dict(process=proc['name'],root=chain['terminal'],width=w,
                        inputs=inputs,expression=rtl.render(expr))
                except ValueError as exc:
                    residuals.append(dict(root=root,producer=chain['terminal'],reason=str(exc)))
            else:residuals.append(dict(root=root,reason=chain['kind'],source=chain['terminal']))
    return dict(captures=steps,capture_fields=fields,transformed_captures=transforms,
        producers=list(producers.values()),residuals=residuals,
        old_inv_read=False,token_history_proved=False,complete_R_generated=False)


def selected_fallbacks(ast,plan,report):
    if report.get('ast_sha256')!=ast['source_sha256'] or report.get('llm',{}).get('status')!='accepted_unproved':
        raise ValueError('current AST and explicit unproved LLM proposal required')
    result=[]
    for row in plan['residuals']:
        root=row.get('producer')
        if root is None:continue
        strategy=report.get('proposals',{}).get('producer_'+str(root))
        if strategy is None:continue
        if strategy!='state_threaded_dependency_slice':raise ValueError('strategy has no checked backend')
        writers=[p for p in ast['processes'] if root in p['writers'] and p['kind']!='Initial']
        if len(writers)!=1 or writers[0]['kind']!='Combinational':raise ValueError('ambiguous original producer')
        result.append(dict(root=root,process=writers[0]['name'],strategy=strategy))
    return result


def check_histories(ast_path,ast_module,output):
    """Generate phase-history certificates for the discovered control storage.

    These retain observed inputs, rather than assuming instruction ownership.
    Each field has its own deadline and report; no repeated full-CPU unfolding.
    """
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    origin=sources.selectors.origin
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    profile['coq_load_paths']=paths
    plan=discover(ast)
    roots=sorted({row['root'] for row in plan.get('capture_fields',plan['captures'])})
    (output/'plan.json').write_text(json.dumps(dict(roots=roots,discovery=plan),indent=2)+'\n')
    report=dict(accepted=False,roots=roots,fields=[],old_inv_read=False,
        complete_R_generated=False,token_history_proved=False,
        scope='control-field phase histories with observed sampled inputs')
    for root in roots:
        checked=origin.histories.check_profile(profile,output/('field_'+str(root)),[root],timeout=1200)
        report['fields'].append(dict(root=root,check=checked))
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    report['accepted']=bool(roots) and all(r['check']['accepted'] for r in report['fields'])
    if not roots:report['status']='no_control_storage_discovered_not_a_completeness_claim'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def check_transforms(ast_path,ast_module,output):
    """Check discovered reference functions, preserving uncovered paths."""
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    direct=captures.direct
    ast,_,_=sources.selectors.origin.raw_binding(ast_path,ast_module)
    frontier=discover(ast)
    plan=direct.discover_control_transforms(ast)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        upstream_identity_proved=False,fields=[],residuals=plan['residuals'],
        reference_functions_checked=False)
    for root in sorted({r['root'] for r in plan['projections']}):
        result=direct.check(ast_path,ast_module,output/('field_'+str(root)),
            selected_roots=[root],source_mode='control_transform')
        report['fields'].append(dict(root=root,check=result))
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    # Unknown recipe branches are obligations, not proof failures or vacancies.
    report['unknown_paths']=[dict(root=r['root'],paths=r['unknown_paths'])
        for r in plan['projections'] if r['unknown_paths']]
    report['accepted']=bool(report['fields']) and all(r['check']['accepted'] for r in report['fields'])
    report['reference_functions_checked']=report['accepted'] and not report['residuals']
    if not frontier['transformed_captures']:
        report['status']='no_transformed_capture_discovered_not_a_completeness_claim'
    elif not report['fields']:
        report['status']='unsupported_transformed_capture'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def check(ast_path,ast_module,output,strategy_report=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=sources.selectors.origin.raw_binding(ast_path,ast_module)
    plan=discover(ast)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    results=[sources.selectors.check(ast_path,ast_module,r['process'],r['root'],
        output/('producer_'+str(r['root']))) for r in plan['producers']]
    fallbacks=[];covered=set()
    if strategy_report:
        import cpu_state_threaded_slice as threaded
        for r in selected_fallbacks(ast,plan,json.loads(Path(strategy_report).read_text())):
            native=threaded.check(ast_path,ast_module,r['process'],r['root'],output/('state_producer_'+str(r['root'])))
            fallbacks.append(dict(candidate=r,check=native))
            if native['accepted']:covered.add(r['root'])
    else:
        # Once a suggested strategy has a checked generic backend, reuse it
        # deterministically. No fresh LLM call or design-specific root table.
        import cpu_state_threaded_slice as threaded
        candidates=threaded.discover(ast)['candidates']
        needed={r.get('producer') for r in plan['residuals']}
        for r in candidates:
            if r['root'] not in needed:continue
            native=threaded.check(ast_path,ast_module,r['process'],r['root'],output/('state_producer_'+str(r['root'])))
            fallbacks.append(dict(candidate=r,origin='reusable_checked_rule',check=native))
            if native['accepted']:covered.add(r['root'])
    report=dict(accepted=bool(results or fallbacks) and all(r['accepted'] for r in results),results=results,
        residuals=plan['residuals'],token_history_proved=False,complete_R_generated=False,old_inv_read=False)
    report['fallbacks']=fallbacks
    report['remaining_producer_residuals']=[r for r in plan['residuals'] if r.get('producer') not in covered]
    if fallbacks:report['accepted']=report['accepted'] and all(r['check']['accepted'] for r in fallbacks)
    report['all_discovered_producers_checked']=report['accepted'] and not report['remaining_producer_residuals']
    if not results and not fallbacks:
        report['status']='no_supported_control_producer_not_a_completeness_claim'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    p.add_argument('--strategy-report')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output,a.strategy_report)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
