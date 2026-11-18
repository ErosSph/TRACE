"""Real, untrusted LLM strategy proposals for exact raw-selector residuals."""
import argparse,hashlib,json
from pathlib import Path
import cpu_field_selector_origin as selector
import cpu_pending_llm as llm

STRATEGIES=[
 dict(id='derive_guarded_projection_reference',requires='prove source word identity and equality of branch references; preserve all guards'),
 dict(id='prove_constant_branch_inactive',requires='prove actual validity is false on the constant branch; never erase a real instruction'),
 dict(id='preserve_blocking_substitution',requires='prove earlier blocking writes are substituted before subsequent reads; retain write order')]

def proposal(ast):
    plan=selector.discover(ast);facts=[];slots={}
    byname={p['name']:p for p in ast['processes']}
    for r in plan['residuals']:
        proc=byname[r['process']]
        facts.append(dict(**r,actual_process=selector.chain.p.rtl.render(proc['body'])))
        slots['field_'+str(r['root'])]=STRATEGIES
    if len(json.dumps(facts))>60000:raise ValueError('full process evidence exceeds request limit; no truncation')
    return slots,facts

def run(ast_path,ast_module,output,key):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=selector.chain.p.origins.raw_binding(ast_path,ast_module)
    slots,facts=proposal(ast);request=llm.prompt(slots,facts,'field_selector_gap')
    raw=json.dumps(request,indent=2)+'\n';(output/'request.json').write_text(raw)
    audit,answer=llm.query(slots,facts,key,'field_selector_gap')if slots else({'status':'no_selector_residuals','attempts':0},None)
    result=dict(accepted=False,complete_R_generated=False,proof_generated=False,old_inv_read=False,
        ast_sha256=ast['source_sha256'],request_sha256=hashlib.sha256(raw.encode()).hexdigest(),llm=audit,
        proposals=answer,scope='unproved rule proposals; no branch validity or identity assumed')
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    a=parser.parse_args();print(json.dumps(run(a.ast,a.ast_module,a.output,llm.transport.key_from_note()),indent=2))
