"""Untrusted, bounded ID-only proposals for *raw RTL* pending-role slots.

No CPU proof catalog, INV source or theorem declaration is an input. Candidates
are not accepted as semantics: the selected new rule must still compile/check.
"""
import json,time,urllib.request,urllib.error
import cpu_auto_roles as transport


def validate(value,slots):
    if not isinstance(value,dict)or set(value)!={'bindings'}or not isinstance(value['bindings'],dict):
        raise ValueError('only a bindings object is accepted')
    if set(value['bindings'])!=set(slots):raise ValueError('all requested roles must be answered or abstained')
    for role,ident in value['bindings'].items():
        if ident is not None and(type(ident)is not str or ident not in {c['id']for c in slots[role]}):
            raise ValueError('unknown candidate, code or unlisted field')
    return value['bindings']


def prompt(slots,facts,role_kind='pc'):
    rules={
        'operand_freshness':('Choose a reusable construction to connect raw operand routes to the latest older ISA writer, or null.',
            'Actual source identity, source value, token age, validity and capture-time alignment are separate proof obligations. No case selector found does NOT mean there is no forwarding or no pending write. Preserve all branches, stalls, resets and sampling boundaries. The ISA batch must be exactly the older pending prefix, excluding the consumer and younger tokens. Choose only a listed strategy; never assume the physical RF equals the speculative ISA state or infer age from signal names.'),
        'field_selector_gap':('Choose a reusable proof construction for each unsupported field selector, or null.',
            'Preserve every branch, width, guard and blocking-write order. A word slice is not automatically an ISA field. A constant branch is not automatically invalid. Never assume source identity, validity or that a branch is unreachable. Select a listed strategy only; this is an unproved proposal, not a proof.'),
        'register_write_relation':('Choose the next reusable proof construction for actual RTL register writes versus an ISA register write, or null to abstain.',
            'A structural write is not necessarily retirement. Preserve reset, clock triggers, write priority, rd=x0 and writes before commitment. Select only a listed strategy. Do not assume instruction identity, operand freshness, address/value agreement or invariant preservation. Representative examples are not exhaustive evidence. A strategy choice is NOT a proof.'),
        'capture_validity':('Choose a reusable validity-proof strategy from raw capture/control evidence, or null to abstain.',
            'Missing a separate valid bit does not justify assuming every capture is an ISA instruction. An injected constant is only a candidate inactive encoding: prove its actual downstream effects are inactive and prove all real instructions are covered. Do not discard reset, stalls, unknown words or wrong-path captures. This choice is NOT a proof.'),
        'pc':('Choose pending PC-role candidates from raw RTL structural evidence, or null to abstain.',
            'The PC paired with an instruction capture must equal the original ROM read address under the actual same capture guards. PC+4 is not the fetched address.'),
        'retirement_cut':('Choose a physical retirement-cut candidate from raw RTL evidence, or null to abstain.',
            'Use actual process firing and terminal instruction validity, not RF write-enable alone: branch, store and rd=x0 need not write RF. A chosen cut is only a candidate; ISA commit identity, ordering, cancellation and progress still need proofs.'),
        'blocking_dependency':('Choose a reusable proof construction for the retained blocking dependencies, or null to abstain.',
            'Earlier blocking writes are visible to later guards. Never discard internal writes, use their old values, or assume the final overwrite is inactive. Choose only a supplied strategy; a choice is NOT a proof or a verified rewrite.')}
    if role_kind not in rules:raise ValueError('unsupported closed role kind')
    task,requirement=rules[role_kind]
    return dict(task=task,
        slots=slots,facts=facts,
        requirement=requirement,
        output_schema={'bindings':{role:'one listed ID or null'for role in slots}},
        proof_policy='No previous CPU INV, pending or proof is provided. This is an unproved proposal; original RTL semantics will check it.')


def query(slots,facts,key,role_kind='pc'):
    payload=prompt(slots,facts,role_kind)
    body=dict(model=transport.MODEL,temperature=0,max_tokens=512,enable_thinking=False,response_format={'type':'json_object'},
        messages=[dict(role='system',content='Return only the requested JSON bindings. No code, tactics, proof names or new assumptions. Use listed IDs or null.'),
            dict(role='user',content=json.dumps(payload,separators=(',',':')))])
    encoded=json.dumps(body).encode();audit=dict(model=transport.MODEL,attempts=1,status='failed',
        usage={},request_bytes=len(encoded),enable_thinking=False,role_kind=role_kind,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False)
    start=time.monotonic();answer=None
    try:
        if not key:raise ValueError('explicit credential required')
        if urllib.request.proxy_bypass('dashscope.aliyuncs.com'):raise RuntimeError('proxy bypass forbidden')
        opener=urllib.request.build_opener(urllib.request.ProxyHandler({'http':transport.PROXY,'https':transport.PROXY}))
        request=urllib.request.Request(transport.ENDPOINT,data=encoded,method='POST',
            headers={'Authorization':'Bearer '+key,'Content-Type':'application/json'})
        with opener.open(request,timeout=60)as response:
            audit['http_status']=response.status
            audit['headers_seconds']=time.monotonic()-start
            raw=response.read(transport.MAX_RESPONSE_BYTES+1)
        if len(raw)>transport.MAX_RESPONSE_BYTES:raise ValueError('response budget exceeded')
        doc=json.loads(raw);audit['usage']=transport._usage(doc.get('usage'));choices=doc['choices']
        if len(choices)!=1 or choices[0].get('finish_reason')!='stop':raise ValueError('incomplete model response')
        answer=validate(json.loads(choices[0]['message']['content']),slots)
        audit.update(status='accepted_unproved',bindings=answer)
    except urllib.error.HTTPError as error:audit.update(http_status=error.code,error='http_error')
    except Exception as error:audit['error']=type(error).__name__
    audit['elapsed_seconds']=time.monotonic()-start
    return audit,answer


if __name__=='__main__':
    import argparse,hashlib
    from pathlib import Path
    parser=argparse.ArgumentParser(description='Replay a saved bounded proposal request; no proof is accepted here.')
    parser.add_argument('--request',type=Path,required=True)
    parser.add_argument('--role-kind',choices=['pc','retirement_cut','blocking_dependency','capture_validity','register_write_relation','field_selector_gap','operand_freshness'],required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--key-from-note',action='store_true',required=True)
    args=parser.parse_args()
    raw=args.request.read_bytes();saved=json.loads(raw)
    if saved!=prompt(saved['slots'],saved['facts'],args.role_kind):
        raise ValueError('request must match the closed proposal schema exactly')
    args.output.mkdir(parents=True,exist_ok=False)
    (args.output/'request.json').write_bytes(raw)
    audit,answer=query(saved['slots'],saved['facts'],transport.key_from_note(),args.role_kind)
    report=dict(accepted=False,request_sha256=hashlib.sha256(raw).hexdigest(),llm=audit,
        proposals=answer,proof_generated=False,complete_R_generated=False)
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
