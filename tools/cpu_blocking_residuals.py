"""Route raw field-origin residuals to the checked sequential blocking backend.

Discovery is not proof acceptance. Unhandled residuals are never discarded.
"""
import argparse,json
from pathlib import Path
import cpu_field_selector_origin as fields
import cpu_blocking_observation as observation
import cpu_blocking_observation_connection as connection

def discover(ast):
    residuals=fields.discover(ast,projected=True)['residuals']
    processes={p['name']:p for p in ast['processes']}
    candidates=[];unsupported=[]
    for r in residuals:
        p=processes[r['process']];root=r['root']
        widths={int(n.args[2].args[0].name) for n in observation.rtl.walk(p['body'])
          if n.name=='SAssign' and n.args[2].name=='LVar' and int(n.args[2].args[1].name)==root}
        try:
            if p['kind']!='Combinational' or len(widths)!=1:
                raise ValueError('requires one scalar output width in a combinational process')
            width=next(iter(widths));c=observation.Compiler(width)
            result=c.compile(p['body'],f'(EVar {width} {root})',{(width,root)})
            candidates.append(dict(**r,width=width,rules=c.serial,
              dependencies=sorted(result[3]),proof_checked=False))
        except ValueError as error:
            unsupported.append(dict(**r,blocking_backend_reason=str(error)))
    return dict(candidates=candidates,unsupported=unsupported,old_inv_read=False,
      complete_R_generated=False,discovery_only=True)

def run(ast_path,module,output,analysis_only=False):
    ast,_,_=observation.origin.raw_binding(ast_path,module)
    plan=discover(ast);out=Path(output);out.mkdir(parents=True,exist_ok=False)
    (out/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    results=[]
    if not analysis_only:
        for row in plan['candidates']:
            prefix=row['process']+'_'+str(row['root'])
            upstream=out/(prefix+'-observation')
            local=observation.check(ast_path,module,row['process'],row['root'],row['width'],upstream)
            result=dict(process=row['process'],root=row['root'],observation=local)
            if local['accepted']:
                result['connection']=connection.check(ast_path,module,upstream,out/(prefix+'-connection'))
            results.append(result)
    accepted=bool(results) and not plan['unsupported'] and all(r.get('connection',{}).get('accepted') for r in results)
    report=dict(accepted=accepted,complete_R_generated=False,isa_identity_proved=False,
      old_inv_read=False,analysis_only=analysis_only,results=results,unsupported=plan['unsupported'],
      status='analysis_only' if analysis_only else ('checked_field_residual_connections' if accepted else
        ('no_matching_residuals_not_a_completeness_claim' if not plan['candidates'] and not plan['unsupported'] else 'unclosed_residuals')))
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    p.add_argument('--analysis-only',action='store_true')
    a=p.parse_args();print(json.dumps(run(a.ast,a.ast_module,a.output,a.analysis_only),indent=2))
