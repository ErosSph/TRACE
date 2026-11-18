"""Ask for untrusted strategy IDs for raw capture-validity residuals only."""
import argparse,json,hashlib
from pathlib import Path
import cpu_pending_validity as validity
import cpu_pending_llm as llm
import cpu_auto_roles as roles
import cpu_pending_recipe_coverage as coverage


def proposal(ast):
    data=validity.discover(ast)
    raw=validity.origins.pending.analyze(ast)
    missing={r['carrier'] for r in data['residuals'] if not r.get('candidates')}
    slots={};facts=[]
    for row in raw['slots']:
        root=row['carrier']
        if root not in missing:continue
        expr=validity.origins.pending.rtl.Parser(row['capture']['next_expression']).complete()
        inputs=validity.origins.pending.roots(expr)
        writers=[p for p in ast['processes'] if p['kind']=='Combinational' and set(p['writers'])&set(inputs)]
        facts.append(dict(carrier=root,capture=row['capture'],input_writers=[
            dict(process=p['name'],body=validity.origins.pending.rtl.render(p['body'])) for p in writers]))
        slots['carrier_'+str(root)]=[
            dict(id='derive_inactive_encoding_predicate',requires='prove injected encoding has no downstream architectural effect and does not hide a real instruction'),
            dict(id='derive_control_history_validity',requires='prove capture/hold/flush control history and correspondence to actual consumption'),
            dict(id='find_separate_validity_field',requires='identify and prove actual valid-field companion rather than guessing by name')]
    if len(json.dumps(facts))>60000:raise ValueError('raw evidence budget exceeded; no silently truncated request')
    return slots,facts


def metadata_proposal(ast):
    data=coverage.discover(ast);slots={};facts=[]
    for root in data['unresolved_fields']:
        gaps=[g for g in data['coverage_gaps']if g['root']==root]
        if not gaps:continue
        # Keep one explicitly identified example per failed rule, not a silent
        # claim that these examples exhaust all branches or all indicators.
        examples={}
        for row in gaps:
            gap=row['gap']
            if gap is not None:examples.setdefault(gap['reason'],row)
        facts.append(dict(root=root,candidate_failure_count=len(gaps),
            representative_failures=list(examples.values()),
            scope='representative syntactic failures; neither reachability nor a counterexample is proved'))
        slots['metadata_'+str(root)]=[
            dict(id='prove_guard_implication',requires='prove actual control guard and source validity implication from RTL, preserving all paths'),
            dict(id='synthesize_control_history_predicate',requires='derive and prove a ghost predicate from actual capture/hold/flush history; physical control flags alone may not denote instruction validity'),
            dict(id='reject_physical_valid_candidate',requires='reject unsupported bindings, retaining the original instruction coverage obligation')]
    if len(json.dumps(facts))>60000:raise ValueError('raw evidence budget exceeded; no silently truncated request')
    return slots,facts


def apply_proposals(ast_path,ast_module,output,answer):
    """Dispatch only implemented, closed strategy IDs to raw-RTL checkers.

    Inactive encoding needs an architectural-effect proof AFTER the word/field
    relation; a successful prerequisite must never mark that obligation closed.
    """
    import cpu_synchronized_values as synchronized
    import cpu_nonzero_projection_history as history
    import cpu_zero_instruction_rf as zero_rf
    handlers={'derive_inactive_encoding_predicate':synchronized.check,
              'synthesize_control_history_predicate':history.check}
    results=[]
    for strategy in sorted({v for v in(answer or {}).values()if v is not None}):
        roles=[k for k,v in answer.items()if v==strategy]
        item=dict(strategy=strategy,requested_roles=roles,architectural_obligation_closed=False)
        if strategy not in handlers:
            item.update(status='no_registered_checker',local_certificate_accepted=False)
        else:
            result=handlers[strategy](ast_path,ast_module,Path(output)/strategy)
            item.update(status='checked_prerequisite',local_certificate_accepted=result.get('accepted')is True,
                        result=result)
            key,field=('coupled_pairs','carrier')if strategy=='derive_inactive_encoding_predicate'else('connections','target')
            roots={r[field]for r in result.get(key,[])}if result.get('accepted')is True else set()
            covered=[role for role in roles if role.rsplit('_',1)[-1].isdigit()
                     and int(role.rsplit('_',1)[-1])in roots]
            item.update(covered_roles=covered,uncovered_roles=[role for role in roles if role not in covered])
            if strategy=='derive_inactive_encoding_predicate'and result.get('accepted')is True:
                rf=zero_rf.check(ast_path,ast_module,Path(output)/'zero-word-rf-effect')
                item['rf_effect_check']=rf
                rf_words={r['word']for r in rf.get('rows',[])}if rf.get('accepted')is True else set()
                item['rf_effect_covered_roles']=[role for role in roles if role.rsplit('_',1)[-1].isdigit()
                    and int(role.rsplit('_',1)[-1])in rf_words]
        results.append(item)
    return results


def reuse_proposal(report_path,slots,facts):
    report_path=Path(report_path);report=json.loads(report_path.read_text())
    request_path=report_path.parent/'request.json';raw=request_path.read_bytes()
    if json.loads(raw)!=llm.prompt(slots,facts,'capture_validity'):
        raise ValueError('saved proposal does not describe the current raw request')
    if report.get('request_sha256',hashlib.sha256(raw).hexdigest())!=hashlib.sha256(raw).hexdigest():
        raise ValueError('saved request digest mismatch')
    if report['llm']['status']!='accepted_unproved':raise ValueError('no successful proposal to reuse')
    answer=llm.validate(dict(bindings=report['proposals']),slots)
    if report['llm'].get('bindings')!=answer:raise ValueError('saved bindings mismatch')
    return dict(status='reused_unproved',new_attempts=0,origin=str(report_path),
                original_call=report['llm']),answer


def run(ast_path,ast_module,output,key,metadata=False,check_proposals=False,proposal_report=None):
    ast,_,_=validity.origins.raw_binding(ast_path,ast_module)
    slots,facts=metadata_proposal(ast)if metadata else proposal(ast)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    (output/'request.json').write_text(json.dumps(llm.prompt(slots,facts,'capture_validity'),indent=2)+'\n')
    if proposal_report:audit,answer=reuse_proposal(proposal_report,slots,facts)
    elif slots:audit,answer=llm.query(slots,facts,key,'capture_validity')
    else:audit,answer=dict(status='no_missing_companion_no_request',attempts=0),None
    result=dict(accepted=False,ast_sha256=ast['source_sha256'],llm=audit,proposals=answer,
        evidence_kind='metadata_coverage'if metadata else'capture_validity',
        old_inv_read=False,proof_generated=False,complete_R_generated=False)
    if check_proposals:
        result['applications']=apply_proposals(ast_path,ast_module,output,answer)
        result['local_proof_generated']=any(r['local_certificate_accepted']for r in result['applications'])
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    p.add_argument('--metadata',action='store_true')
    p.add_argument('--check-proposals',action='store_true')
    p.add_argument('--proposal-report',type=Path)
    a=p.parse_args();result=run(a.ast,a.ast_module,a.output,
        None if a.proposal_report else roles.key_from_note(),a.metadata,a.check_proposals,a.proposal_report)
    print(json.dumps(result,indent=2))
