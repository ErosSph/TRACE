"""Raw-RTL write-relation gaps for bounded, untrusted real LLM proposals.

Never imports an old CPU invariant or treats a strategy choice as a proof.
Full bank plans are retained; the request explicitly labels representative data.
"""
import argparse
import hashlib
import json
from pathlib import Path
import cpu_zero_instruction_rf as rf
import cpu_pending_llm as llm

STRATEGIES=[
 dict(id='connect_sampled_value_and_address',requires='prove combinational connections from sampled operands and instruction to actual write value/address'),
 dict(id='connect_sequential_token_history',requires='prove which earlier accepted instruction owns the registered destination and result, including stalls/flush'),
 dict(id='connect_per_lane_enables',requires='prove decoded lane enables and port priority implement the same ISA destination and value'),
 dict(id='separate_reset_from_normal_write',requires='prove actual reset history and initialization before using a normal writeback relation')]

def proposal(ast):
    analysis=rf.banks.analyze(ast);slots={};facts=[];full=[]
    for bank in analysis['banks']:
        plans=[dict(process=p['name'],events=p['events'],plan=rf.rtl.render(bp))for p,_,bp in bank['plans']]
        full.append(dict(root=bank['root'],plans=plans))
        chosen=sorted(set([0,len(plans)-1]))if plans else []
        facts.append(dict(root=bank['root'],total=bank['total'],writer_count=len(plans),
            representative_indices=chosen,representative_plans=[plans[i]for i in chosen],
            evidence_scope='representative first/last writers, not exhaustive; full plans retained separately',
            unresolved=['instruction ownership','destination identity','value equals ISA result','reset/control history']))
        slots['bank_'+str(bank['root'])]=STRATEGIES
    if len(json.dumps(facts))>60000:raise ValueError('request budget exceeded; no silent truncation')
    return slots,facts,dict(banks=full,residuals=analysis['residuals'])

def run(ast_path,ast_module,output,key):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=rf.origin.raw_binding(ast_path,ast_module)
    slots,facts,full=proposal(ast)
    request=llm.prompt(slots,facts,'register_write_relation')
    raw=json.dumps(request,indent=2)+'\n'
    (output/'request.json').write_text(raw)
    (output/'full-plans.json').write_text(json.dumps(full,indent=2)+'\n')
    audit,answer=llm.query(slots,facts,key,'register_write_relation')if slots else ({'status':'no_bank_candidates','attempts':0},None)
    result=dict(accepted=False,complete_R_generated=False,proof_generated=False,old_inv_read=False,
        ast_sha256=ast['source_sha256'],request_sha256=hashlib.sha256(raw.encode()).hexdigest(),
        llm=audit,proposals=answer,scope='unproved strategy selection; no ISA relation assumed')
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    a=p.parse_args()
    print(json.dumps(run(a.ast,a.ast_module,a.output,llm.transport.key_from_note()),indent=2))
