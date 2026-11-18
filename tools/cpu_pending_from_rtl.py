"""Pending candidates from constructor RTL alone, never from a previous INV.

The analysis is conservative: structural capture is not ISA identity. Missing
PC/valid/age or decoded-token transport is a residual, not an empty queue.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as rtl
import cpu_scalar_captures as captures
import cpu_scalar_expressions as expressions
import cpu_plan_slices as slices
from cpu_certificate_acceptance import run_stage

ISA_FIELDS={(7,0):'opcode',(5,7):'rd',(3,12):'funct3',
            (5,15):'rs1',(5,20):'rs2',(7,25):'funct7'}


def roots(term):
    return sorted({int(n.args[1].name)for n in rtl.walk(term)if n.name=='EVar'})


def data_leaves(term):
    """Do not confuse a mux selector dependency with instruction transport."""
    if term.name=='ECond':
        return data_leaves(term.args[2])+data_leaves(term.args[3])
    return [term]


def paths(term,prefix=()):
    """Preserve guards, branch order, and default-case priority verbatim."""
    if term.name=='SAssign':yield prefix,term
    elif term.name=='SSeq':
        for child in term.args[0].args:yield from paths(child,prefix)
    elif term.name=='SIf':
        guard,yes,no=term.args
        yield from paths(yes,prefix+(('if_true',rtl.render(guard)),))
        yield from paths(no,prefix+(('if_false',rtl.render(guard)),))
    elif term.name=='SCase':
        selector,arms=term.args
        previous=[]
        for key,body in (arm.args for arm in arms.args):
            path=('case',rtl.render(selector),rtl.render(key),tuple(previous))
            yield from paths(body,prefix+(path,))
            previous.append(rtl.render(key))
    elif term.name!='SSkip':raise ValueError('unsupported statement, no partial extraction')


def analyze(ast):
    widths={};writes={};copies=[];fields={};unsupported=[]
    for proc in ast['processes']:
        # Decode uses also occur in IF/CASE selectors, not only RHS values.
        for n in rtl.walk(proc['body']):
            if n.name!='ESel':continue
            width,base,lsb=n.args
            if base.name!='EVar'or base.args[0].name!='32'or lsb.name!='EConst':continue
            key=(int(width.name),int(lsb.args[1].name))
            if key in ISA_FIELDS:
                root=int(base.args[1].name)
                fields.setdefault(root,set()).add(ISA_FIELDS[key])
        for path,node in paths(proc['body']):
            nba,rhs,lhs=node.args;dest=rtl.root_of(lhs)
            if lhs.name=='LVar':widths.setdefault(dest,set()).add(int(lhs.args[0].name))
            row=dict(process=proc['name'],kind=proc['kind'],events=proc['events'],
                source_line=proc['line'],nba=nba.name=='true',path=list(path),
                rhs=rtl.render(rhs),read_roots=roots(rhs),whole=lhs.name=='LVar')
            writes.setdefault(dest,[]).append(row)
            if lhs.name=='LVar'and lhs.args[0].name=='32':
                for leaf in data_leaves(rhs):
                    if leaf.name=='EVar'and leaf.args[0].name=='32':
                        copies.append(dict(source=int(leaf.args[1].name),destination=dest,
                            process=proc['name'],sequential=proc['kind']=='Sequential',
                            event=proc['events'],path=list(path),expression=rtl.render(rhs)))
    # Follow only content copies, never arbitrary arithmetic or mux controls.
    decoded={root for root,uses in fields.items()if 'opcode'in uses and len(uses)>=2}
    transport=set(decoded)
    changed=True
    while changed:
        changed=False
        for edge in copies:
            if edge['destination']in transport and edge['source']not in transport:
                transport.add(edge['source']);changed=True
    found=captures.analyze(ast);scalar={}
    for root in found['analysis']['roots']:
        writer=[(p,plan)for p,plan in found['analysis']['plans']if root in p['writers']]
        if len(writer)!=1:
            unsupported.append(dict(root=root,reason='multiple writers need ordered composition'));continue
        proc,plan=writer[0];ws=widths.get(root,set())
        if len(ws)!=1:continue
        width=next(iter(ws))
        if width not in (1,32):continue
        seed=rtl.Term('EVar',(rtl.Term(str(width)),rtl.Term(str(root))))
        expr=expressions.compile_expression(slices.slice_plan(plan,root),root,width,seed)
        if expr is None:continue
        scalar[root]=dict(root=root,width=width,process=proc['name'],events=proc['events'],
            next_expression=rtl.render(expr),sampled_dependencies=roots(expr))
    slots=[]
    for root in sorted(transport&scalar.keys()):
        if scalar[root]['width']!=32:continue
        slot=scalar[root]
        controls={rtl.render(n.args[1])for n in rtl.walk(rtl.Parser(slot['next_expression']).complete())if n.name=='ECond'}
        peers=[s for r,s in scalar.items()if r!=root and s['process']==slot['process']and s['events']==slot['events']]
        pc=[p['root']for p in peers if p['width']==32]
        valid=[p['root']for p in peers if p['width']==1]
        slots.append(dict(id='slot_'+str(root),carrier=root,decode_fields=sorted(fields.get(root,set())),
            capture=slot,guards=sorted(controls),pc_candidates=pc,valid_candidates=valid,
            producer_edges=[e for e in copies if e['destination']==root and e['source']!=root],
            status='unproved_structural_candidate'))
    sequential_edges=[e for e in copies if e['sequential']and e['source']in transport and e['destination']in transport
        and e['source']!=e['destination']]
    residuals=[dict(obligation='instruction_identity',reason='decode-shaped bit use is not a proof of accepted ISA identity'),
        dict(obligation='retirement_identity',reason='must derive actual retiring token and boundary from RTL'),
        dict(obligation='flush_rollback',reason='physical wrong-path tokens cannot be silently erased from an ISA effect chain'),
        dict(obligation='cycle_correspondence',reason='must prove actual phases generate a successful checked queue update'),
        dict(obligation='isa_effects',reason='accepted token effects and RF/RAM/PC relation must be proved against original run1')]
    if not slots:residuals.append(dict(obligation='slots',reason='no supported full-word capture; decoded metadata or FIFO requires another transport rule'))
    for s in slots:
        if len(s['pc_candidates'])!=1 or len(s['valid_candidates'])!=1:
            residuals.append(dict(obligation='slot_binding',slot=s['id'],reason='PC/valid pairing absent or ambiguous; no empty fallback'))
    return dict(schema_version=1,ast_sha256=ast['source_sha256'],input_boundary='constructor RTL only',
        old_inv_read=False,old_pending_read=False,old_theorems_read=False,
        sequential_state_roots=sorted({r for p in ast['processes']if p['kind']=='Sequential'for r in p['writers']}),
        instruction_word_candidates=sorted(decoded),copy_edges=sequential_edges,slots=slots,
        scalar_transitions=list(scalar.values()),unsupported=unsupported,residuals=residuals,
        pending_synthesized=False,global_inv_proved=False,itree_refinement_proved=False)


def checked_queue_step(queue,admitted,retiring,cancel_youngest=0):
    """Executable reference algorithm, not an assertion that RTL obeys it.

    Tokens include unique admission IDs, not just PCs (loops repeat PCs).
    Cancellation is returned explicitly and never presented as retirement.
    """
    if type(cancel_youngest)is not int or cancel_youngest<0:raise ValueError('invalid cancellation count')
    if len({t['id']for t in queue+admitted})!=len(queue+admitted):return None
    whole=queue+admitted
    if whole[:len(retiring)]!=retiring or len(retiring)>len(whole):return None
    rest=whole[len(retiring):]
    if cancel_youngest>len(rest):return None
    kept=rest if cancel_youngest==0 else rest[:-cancel_youngest]
    killed=[]if cancel_youngest==0 else rest[-cancel_youngest:]
    return dict(pending=kept,cancelled=killed,retired=retiring)


def candidate_order(report):
    """A unique full-word chain only; never guess ages by numeric root ID."""
    slots={s['carrier']:s for s in report['slots']}
    if not slots or any(len(s['pc_candidates'])!=1 or len(s['valid_candidates'])!=1 for s in slots.values()):
        return None
    edges={(e['source'],e['destination'])for e in report['copy_edges']
        if e['source']in slots and e['destination']in slots}
    remaining=set(slots);young_to_old=[]
    while remaining:
        ready=sorted(r for r in remaining if not any(b==r and a in remaining for a,b in edges))
        if len(ready)!=1:return None
        root=ready[0];young_to_old.append(root);remaining.remove(root)
    return list(reversed(young_to_old))


def render_candidate(report):
    order=candidate_order(report)
    if order is None:return None
    slots={s['carrier']:s for s in report['slots']}
    # No old Program, runtime, pending or theorem symbol is imported here.
    lines=['(** UNPROVED architectural binding candidate derived only from RTL. *)',
        'From Coq Require Import List ZArith.',
        'Require Import Lang.ExtendedSV Lib.CheckedPendingQueue.',
        'Import ListNotations ExtendedSV CheckedPendingQueue.',
        'Definition candidate_slot (slot:nat) (s:State) : option (Z*Z) :=',
        ' match slot with']
    for index,root in enumerate(order):
        pc=slots[root]['pc_candidates'][0];valid=slots[root]['valid_candidates'][0]
        lines.append(f' | {index}%nat => if Z.eqb (eval_expr s (EVar 1 {valid})) 0 then None else Some')
        lines.append(f'   (eval_expr s (EVar 32 {pc}),eval_expr s (EVar 32 {root}))')
    lines+=[' | _ => None end.',
        'Definition candidate_pending (s:State) := snapshot candidate_slot ['+
            ';'.join(str(i)+'%nat'for i in range(len(order)))+'] s.',
        'Theorem candidate_capacity s : List.length(candidate_pending s)<='+str(len(order))+'%nat.',
        'Proof. apply snapshot_capacity. Qed.',
        'Print Assumptions candidate_capacity.']
    return '\n'.join(lines)+'\n'


def run(ast_path,output):
    ast=rtl.load_ast(Path(ast_path));report=analyze(ast)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    source=render_candidate(report)
    report['candidate_pending_generated']=source is not None
    report['candidate_order']=candidate_order(report)
    if source is not None:
        (output/'PendingCandidate.v').write_text(source)
        report['candidate_source_sha256']=hashlib.sha256(source.encode()).hexdigest()
    (output/'plan.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def check_captures(ast_path,ast_module,output,timeout=1200):
    """Check new carrier transition expressions against actual process bodies.

    This checks a necessary local part of synthesis, NOT queue correspondence.
    No proof-profile, INV source, old pending, or CPU theorem is an input.
    """
    if not rtl.SYMBOL.fullmatch(ast_module):raise ValueError('invalid AST import')
    if not 0<timeout<=1200:raise ValueError('invalid native budget')
    ast_path=Path(ast_path).resolve();ast=rtl.load_ast(ast_path);report=run(ast_path,output)
    output=Path(output);raw=ast_path.read_text()
    programs=re.findall(r'Definition\s+(\w+)\s*:\s*Program\s*:=',raw)
    if len(programs)!=1:raise ValueError('unique raw frontend Program required')
    program=ast['module']+'.'+programs[0]
    all_plans={p['name']:(p,plan)for p,plan in rtl.analyze(ast)['plans']}
    used=sorted({slot['capture']['process']for slot in report['slots']})
    if not used:raise ValueError('no supported capture; never substitute an empty queue')
    lines=['From Coq Require Import List ZArith.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterPlan',
        ' Lang.ExtendedSVScalarExpression Lang.ExtendedSVPlanRootSlice '+ast_module+'.',
        'Import ListNotations ExtendedSV ExtendedSVAutoAdapterPlan ExtendedSVScalarExpression ExtendedSVPlanRootSlice.']
    for name in used:
        proc,plan=all_plans[name]
        lines += [f'Definition proposed_{name} : NbPlan := {rtl.render(plan)}.',
            f'Lemma checked_{name} : compile_nb (statement_fuel {program})',
            f' (process_body {ast["module"]}.{name})=Some proposed_{name}.',
            'Proof. vm_compute. reflexivity. Qed.']
    for slot in report['slots']:
        row=slot['capture'];root=row['root'];name=row['process'];width=row['width']
        lines += [f'Definition next_{root} : Expr := {row["next_expression"]}.',
            f'Lemma checked_expression_{root} : compile_scalar 512 {root} {width}',
            f' (slice_plan 512 {root} proposed_{name}) (EVar {width} {root})=Some next_{root}.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem actual_capture_{root} s : norm {width} (read_signal',
            f' (run_process {program} s {ast["module"]}.{name}) {root})=',
            f' norm {width} (eval_expr s next_{root}).',
            f'Proof. exact (checked_sliced_scalar_process {program} {ast["module"]}.{name}',
            f' proposed_{name} {root} {width} 512 512 next_{root}',
            f' checked_{name} checked_expression_{root} s). Qed.',
            f'Print Assumptions actual_capture_{root}.']
    source='\n'.join(lines)+'\n';path=output/'CarrierTransitions.v';path.write_text(source)
    flags=list(rtl.framework.FLAGS)
    if not ast_path.is_relative_to(rtl.ROOT/'src'):
        flags+=['-R',str(ast_path.parent),ast_module.rsplit('.',1)[0]]
    flags+=['-R',str(output.resolve()),'GeneratedPending']
    result=dict(accepted=False,old_inv_read=False,old_pending_read=False,old_theorems_read=False,
        scope='actual individual carrier process equations only',
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=ast['source_sha256'],
        capture_count=len(report['slots']),queue_correspondence_proved=False,global_inv_proved=False,
        itree_refinement_proved=False,llm_calls=0)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==len(report['slots'])and 'Axioms:'not in c.stdout
        result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedPending.CarrierTransitions'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--check-captures',action='store_true')
    p.add_argument('--ast-module');a=p.parse_args()
    if a.check_captures:
        if not a.ast_module:p.error('--ast-module required for actual capture checks')
        r=check_captures(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
    r=run(a.ast,a.output)
    print(json.dumps({k:r[k]for k in ('old_inv_read','old_pending_read','instruction_word_candidates',
        'pending_synthesized','global_inv_proved','itree_refinement_proved')},indent=2))
