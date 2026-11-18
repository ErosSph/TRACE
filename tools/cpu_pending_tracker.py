"""Executable sideband pending tracker proposed from RTL carrier expressions.

Input frames/events MUST come from the actual phase observer. This module does
not prove that admission/retirement bindings are correct or reachable. Its
finite records are checkable queue certificates, never a substitute for that
universal correspondence proof. It never writes or replaces DUT state.
"""
from __future__ import annotations
from copy import deepcopy
import cpu_pending_from_rtl as pending


def norm(width,value):
    if not 0<=width<=1048576:raise ValueError('unsupported width; do not truncate')
    return value&((1<<width)-1)


def read(state,root):return state[root]if 0<=root<len(state)else 0


def signed(width,value):
    value=norm(width,value)
    return value-(1<<width)if width and value&(1<<(width-1))else value


def evaluate(e,state):
    """Proposal evaluator matching ExtendedSV.eval_expr; Coq remains authority."""
    a=e.args;w=int(a[0].name);name=e.name
    if name=='EConst':value=int(a[1].name)
    elif name=='EVar':value=read(state,int(a[1].name))
    elif name=='ESel':
        base=evaluate(a[1],state);shift=evaluate(a[2],state)
        value=0 if shift>=int(a[1].args[0].name)else base>>shift
    elif name=='EConcat':
        low_width=int(a[2].args[0].name)
        value=evaluate(a[2],state)
        if low_width<w:value|=evaluate(a[1],state)<<low_width
    elif name=='EReplicate':
        count=int(a[1].name);body=a[2];bw=int(body.args[0].name);value=0
        if bw:
            for _ in range(min(count,(w+bw-1)//bw)):value=(value<<bw)|evaluate(body,state)
    elif name=='EExtend':
        value=evaluate(a[2],state)
        if a[1].name=='true':value=signed(int(a[2].args[0].name),value)
    elif name=='EUnary':
        v=evaluate(a[2],state);op=a[1].name
        if op=='UNot':value=~v
        elif op=='UNegate':value=-v
        elif op=='URedOr':value=int(v!=0)
        else:raise ValueError('unknown unary operator')
    elif name=='EBinary':
        op=a[1].name;l=evaluate(a[2],state);r=evaluate(a[3],state)
        if op=='BAnd':value=l&r
        elif op=='BOr':value=l|r
        elif op=='BXor':value=l^r
        elif op=='BAdd':value=l+r
        elif op=='BSub':value=l-r
        elif op=='BMul':value=l*r
        elif op=='BEq':value=int(l==r)
        elif op=='BNeq':value=int(l!=r)
        elif op=='BLtU':value=int(l<r)
        elif op=='BGtU':value=int(l>r)
        elif op=='BGtS':value=int(signed(int(a[2].args[0].name),l)>signed(int(a[3].args[0].name),r))
        elif op=='BShiftL':value=0 if r>=w else l<<r
        elif op=='BShiftR':value=0 if r>=int(a[2].args[0].name)else l>>r
        elif op=='BShiftRS':value=signed(int(a[2].args[0].name),l)>>min(r,int(a[2].args[0].name))
        else:raise ValueError('unknown binary operator')
    elif name=='ECond':value=evaluate(a[2]if evaluate(a[1],state)!=0 else a[3],state)
    else:raise ValueError('unsupported expression; never assume a guard value')
    return norm(w,value)


def copy_source(expression,sampled):
    if expression.name=='EVar'and expression.args[0].name=='32':return int(expression.args[1].name)
    if expression.name=='ECond'and expression.args[0].name=='32':
        return copy_source(expression.args[2]if evaluate(expression.args[1],sampled)!=0 else expression.args[3],sampled)
    return None


def empty_tracker():
    # Empty is allowed here only as the initial *ghost ledger*, not inferred
    # from an unknown hardware slot. Reset/validity coverage is still required.
    return dict(next_id=0,registry={},pending=[],origins={})


def advance(plan,tracker,sampled,fired,admissions=(),retirements=(),cancelled_ids=(),frame_origins=None,
            valid_after=None):
    """One observed phase; failure is atomic and never repaired by dropping data.

    Admissions: {source,pc,instruction}. Retirements: {owner,side,pc,instruction}.
    side pre/post is explicit: an RF falling-edge write may observe old token
    metadata, while another event can observe the post-capture slot.
    """
    old=deepcopy(tracker);result=deepcopy(tracker);registry=result['registry']
    slots={s['carrier']:s for s in plan['slots']};known_processes={s['capture']['process']for s in slots.values()}
    if not slots:raise ValueError('no carrier coverage; never synthesize an empty pending')
    if not isinstance(valid_after,dict)or set(valid_after)!=set(slots)or any(type(v)is not bool for v in valid_after.values()):
        raise ValueError('every candidate slot needs explicit observed post-validity')
    if not set(fired)<=known_processes:raise ValueError('unrecognized carrier process')
    expressions={r:pending.rtl.Parser(s['capture']['next_expression']).complete()for r,s in slots.items()}
    frontier={int(leaf.args[1].name)for e in expressions.values()for leaf in pending.data_leaves(e)
        if leaf.name=='EVar'and leaf.args[0].name=='32'}-slots.keys()
    sampled_origins={r:uid for r,uid in old['origins'].items()if r in slots}
    for root,uid in (frame_origins or {}).items():
        if root not in frontier or uid not in registry:raise ValueError('unregistered frame origin')
        sampled_origins[root]=uid
    admitted=[]
    for event in admissions:
        if set(event)!={'source','pc','instruction'}or event['source']not in frontier:
            raise ValueError('admission outside structural source frontier')
        source=event['source']
        if source in [e['source']for e in admitted]:raise ValueError('multiple admissions on one source in a phase')
        uid=result['next_id'];result['next_id']+=1
        token=dict(id=uid,pc=norm(32,event['pc']),instruction=norm(32,event['instruction']))
        registry[uid]=token;sampled_origins[source]=uid;admitted.append(dict(source=source,token=token))
    for root,uid in sampled_origins.items():
        if uid is None:continue
        if uid not in registry or norm(32,read(sampled,root))!=registry[uid]['instruction']:
            raise ValueError('sampled origin contradicts actual instruction word')
    updates={}
    for root,slot in slots.items():
        if slot['capture']['process']not in fired:updates[root]=old['origins'].get(root)
        else:
            source=copy_source(expressions[root],sampled)
            updates[root]=sampled_origins.get(source)if source is not None else None
    result['origins'].update(updates)
    retiring=[]
    for event in retirements:
        if set(event)!={'owner','side','pc','instruction'}or event['owner']not in slots:
            raise ValueError('retirement outside structural owner whitelist')
        if event['side']not in ('pre','post'):raise ValueError('retirement sampling side must be explicit')
        source=old if event['side']=='pre'else result
        uid=source['origins'].get(event['owner'])
        if uid is None:raise ValueError('unknown owner is not an empty slot or a proved commit')
        token=registry[uid]
        if (norm(32,event['pc']),norm(32,event['instruction']))!=(token['pc'],token['instruction']):
            raise ValueError('observed commit disagrees with admission identity')
        retiring.append(token)
    old_queue=[registry[uid]for uid in old['pending']];new_tokens=[row['token']for row in admitted]
    checked=pending.checked_queue_step(old_queue,new_tokens,retiring,len(cancelled_ids))
    if checked is None:raise ValueError('commit is not an in-order admitted prefix')
    if [t['id']for t in checked['cancelled']]!=list(cancelled_ids):raise ValueError('cancellation must be the exact youngest suffix')
    result['pending']=[t['id']for t in checked['pending']]
    for root,valid in valid_after.items():
        if valid and result['origins'].get(root)not in result['pending']:
            raise ValueError('valid unretired slot has unknown, cancelled, or already retired origin')
    certificate=dict(old=old['pending'],admitted=[t['id']for t in new_tokens],
        retired=[t['id']for t in retiring],kept=result['pending'],cancelled=list(cancelled_ids),
        instruction_origins=updates,validity_coverage_checked=True,actual_rtl_correspondence_proved=False)
    return result,certificate


def render_queue_certificate(certificate):
    """Concrete Coq check of queue algebra only; no CPU correctness assumption."""
    def seq(key):
        values=certificate[key]
        if not isinstance(values,list)or any(type(v)is not int or v<0 for v in values):raise ValueError('invalid token IDs')
        return '['+';'.join(str(v)+'%nat'for v in values)+']'
    q,a,r,k,d=[seq(key)for key in ('old','admitted','retired','kept','cancelled')]
    return '\n'.join(['From Coq Require Import List Arith.',
        'Require Import Lib.CheckedPendingQueue.', 'Import ListNotations CheckedPendingQueue.',
        f'Example queue_algorithm_checked : step Nat.eq_dec {q} {a} {r} {len(certificate["cancelled"])}%nat = Some ({k},{d}).',
        'Proof. vm_compute. reflexivity. Qed.',
        f'Theorem queue_conservation : {q}++{a}={r}++({k}++{d}).',
        'Proof. exact (step_partition Nat.eq_dec _ _ _ _ _ _ queue_algorithm_checked). Qed.',
        'Print Assumptions queue_conservation.'])+'\n'
