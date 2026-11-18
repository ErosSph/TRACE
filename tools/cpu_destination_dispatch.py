"""Structure-directed proof dispatch for one common ISA destination obligation.

Template success is a checked component, not discharge of retirement identity.
No CPU name, old invariant, or handwritten CPU proof selects a route.
"""
import argparse
import json
from pathlib import Path
import cpu_direct_write_destination as direct
import cpu_write_destination_history as history
import cpu_fixed_lane_enable as fixed
import cpu_r_write_strategy as strategy
import cpu_guarded_write as guarded

GOAL = 'actual enabled architectural write targets the destination of its retiring ISA instruction'
REMAINING = ['retiring instruction identity', 'write validity and token presence',
             'ISA result value', 'initialization and cycle preservation']


def select(ast, fields):
    """Nonexclusive rules: mixed structures must retain all selected routes."""
    d, dr = direct.discover(ast, fields)
    h, hr = history.discover(ast)
    f = fixed.discover(ast)
    routes = []
    if d:
        routes.append(dict(template='direct_sampled_rd', matches=d,
                           proves='actual phase write address, conditional on sampled instruction identity'))
    if h:
        routes.append(dict(template='registered_rd_history', matches=h,
                           proves='captured token destination at a registered endpoint'))
    if f['rows']:
        routes.append(dict(template='fixed_lane_decoder', matches=f['rows'],
                           proves='local decoder selection, not full LFP or ISA identity'))
    pairs = guarded.discover(ast)
    if pairs:
        routes.append(dict(template='guarded_controller_write', matches=pairs,
                           proves='actual LFP write-enable implies controller gate; not pipeline validity'))
    return dict(goal=GOAL, routes=routes,
                residuals=dict(direct=dr, history=hr, fixed_lane=f['residuals']),
                selection_is_proof=False, common_goal_proved=False,
                remaining=list(REMAINING), old_inv_read=False)


def run(ast_path, ast_module, isa_provider, output, field_provider=None,
        bank_provider=None, native=False, key=None, local_fixed=False,
        boot_provider=None,catalog_provider=None,phase_provider=None):
    if any(x is not None for x in [boot_provider,catalog_provider,phase_provider]) and not all(
        x is not None for x in [boot_provider,catalog_provider,phase_provider]):
        raise ValueError('boot initialization requires boot, catalog and phase providers together')
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=history.chain.p.origins.raw_binding(ast_path,ast_module)
    profile['coq_load_paths']=paths
    _,_,fields,_,_,_=direct.destinations.inputs.fields.proposal(profile)
    plan=select(ast,fields)
    plan['ast_sha256']=ast['source_sha256']
    (out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    result=dict(goal=GOAL, common_goal_proved=False, complete_R_generated=False,
                old_inv_read=False, checks={}, remaining=plan['remaining'],
                templates=[r['template'] for r in plan['routes']])
    if native:
        for route in plan['routes']:
            name=route['template'];folder=out/name
            if name=='direct_sampled_rd':
                if not field_provider or not bank_provider:
                    result['checks'][name]=dict(accepted=False,status='checked providers required')
                else:
                    result['checks'][name]=direct.check(ast_path,ast_module,field_provider,
                                                       isa_provider,bank_provider,folder)
            elif name=='registered_rd_history':
                result['checks'][name]=history.check(ast_path,ast_module,isa_provider,folder)
                checked=result['checks'][name]
                targets=checked.get('targets',[])
                if checked.get('accepted') is True and len(targets)==1:
                    import cpu_capture_chain_coverage
                    result['checks']['registered_rd_coverage']=cpu_capture_chain_coverage.check(
                        ast_path,ast_module,out/'registered-rd-coverage',
                        set(targets[0]['roots']))
                    if result['checks']['registered_rd_coverage'].get('accepted') is True:
                        import cpu_invalid_capture_projection
                        result['checks']['invalid_capture_projection']=cpu_invalid_capture_projection.check(
                            ast_path,ast_module,out/'registered-rd-coverage',out/'invalid-capture-projection')
                        import cpu_covered_write_destination
                        result['checks']['covered_actual_destination']=cpu_covered_write_destination.check(
                            ast_path,ast_module,isa_provider,out/'registered-rd-coverage',
                            out/'covered-actual-destination')
            elif name=='fixed_lane_decoder':
                # Explicit local-only option prevents retrying an exhausted full-LFP point.
                result['checks'][name]=(fixed.check(ast_path,ast_module,folder) if local_fixed
                    else dict(accepted=False,status='local decoder selected; execution not requested',
                              full_lfp_bit_connection_proved=False))
            elif name=='guarded_controller_write':
                result['checks'][name]=guarded.check(ast_path,ast_module,folder)
                if result['checks'][name].get('accepted') is True and 'registered_rd_history' in result['templates']:
                    import cpu_write_validity_chain
                    result['checks']['write_validity_chain']=cpu_write_validity_chain.check(
                        ast_path,ast_module,out/'write-validity-chain')
                    if (boot_provider is not None and result['checks']['write_validity_chain'].get('accepted') is True
                        and result['checks']['write_validity_chain'].get('entry_relation_proved') is True):
                        import cpu_write_validity_boot
                        result['checks']['write_validity_boot']=cpu_write_validity_boot.check(
                            ast_path,ast_module,out/'write-validity-chain',boot_provider,
                            catalog_provider,phase_provider,out/'write-validity-boot')
                        if (result['checks']['write_validity_boot'].get('accepted') is True
                            and result['checks'].get('registered_rd_coverage',{}).get('accepted') is True):
                            import cpu_captured_history_boot
                            result['checks']['captured_history_boot']=cpu_captured_history_boot.check(
                                ast_path,ast_module,out/'registered-rd-coverage',out/'write-validity-boot',
                                out/'captured-history-boot')
                            if result['checks']['captured_history_boot'].get('accepted') is True:
                                import cpu_capture_provenance
                                result['checks']['capture_provenance']=cpu_capture_provenance.check(
                                    ast_path,ast_module,out/'captured-history-boot',out/'capture-provenance')
                    if (result['checks']['write_validity_chain'].get('accepted') is True
                        and result['checks']['write_validity_chain'].get('entry_relation_proved') is True
                        and result['checks'].get('registered_rd_coverage',{}).get('accepted') is True):
                        import cpu_covered_write_destination
                        extra=([out/'captured-history-boot'] if result['checks'].get('captured_history_boot',{}).get('accepted') is True else [])
                        result['checks']['derived_actual_destination']=cpu_covered_write_destination.check(
                            ast_path,ast_module,isa_provider,out/'registered-rd-coverage',
                            out/'derived-actual-destination',out/'write-validity-chain',*extra)
    if not plan['routes'] and key:
        result['llm_gap']=strategy.run(ast_path,ast_module,out/'llm-gap',key)
        # A proposed strategy cannot add a route or certify its preconditions.
    result['checked_components']=sum(r.get('accepted') is True for r in result['checks'].values())
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','isa-provider','output']:
        p.add_argument('--'+name,required=True)
    for name in ['field-provider','bank-provider']:p.add_argument('--'+name)
    p.add_argument('--native',action='store_true')
    p.add_argument('--local-fixed',action='store_true')
    p.add_argument('--llm',action='store_true')
    for name in ['boot-provider','catalog-provider','phase-provider']:p.add_argument('--'+name)
    a=p.parse_args()
    key=strategy.llm.transport.key_from_note() if a.llm else None
    print(json.dumps(run(a.ast,a.ast_module,a.isa_provider,a.output,
                         a.field_provider,a.bank_provider,a.native,key,a.local_fixed,
                         a.boot_provider,a.catalog_provider,a.phase_provider),indent=2))
