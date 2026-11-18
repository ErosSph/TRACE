"""Discover forwarded result registers and prove their shared token recipe.

Capture-value correctness remains an explicit obligation, not an assumed CPU INV.
"""
import argparse, hashlib, json, time, re
from pathlib import Path
import cpu_pc_companion_chain as companion
import cpu_selected_candidate_tokens as selected
import cpu_selected_data_paths as data
from cpu_certificate_acceptance import run_stage
rtl=companion.rtl

def match(expression,recipe,width,root):
    if recipe.name=='Unknown':return [],'apply MatchesUnknown.'
    if recipe.name=='Capture':return [expression],'apply MatchesCapture.'
    if recipe.name=='Hold':
        return ([], 'apply MatchesHold.') if expression==rtl.Parser(f'(EVar {width} {root})').complete() else None
    if recipe.name=='Select' and expression.name=='ECond' and expression.args[0].name==str(width) and expression.args[1]==recipe.args[0]:
        a=match(expression.args[2],recipe.args[1],width,root)
        b=match(expression.args[3],recipe.args[2],width,root)
        if a is not None and b is not None:
            return a[0]+b[0],f'apply MatchesSelect. {{ {a[1]} }} {{ {b[1]} }}'
    return None

def discover(raw,chain,paths,operand_captures=False):
    scalars=companion.pc.fetch.origin.pending.analyze(raw)['scalar_transitions']
    roots=set() if operand_captures else {p['data']['terminal'] for p in paths if p['data']['kind']=='sequential'}
    candidates=[]
    for s in scalars:
        stages=[(i,r)for i,r in enumerate(chain['rows'])if r['process']==s['process']]
        if len(stages)!=1:continue
        i,stage=stages[0]
        m=match(rtl.Parser(s['next_expression']).complete(),companion.RecipeParser(stage['recipe']).complete(),s['width'],s['root'])
        if m is None or len(set(m[0]))!=1:continue
        capture=m[0][0]
        route=data.wires.trace(raw,s['width'],int(capture.args[1].name)) if capture.name=='EVar'and capture.args[0].name==str(s['width'])else None
        candidates.append(dict(**s,stage=i,recipe=stage['recipe'],capture=rtl.render(capture),proof=m[1],route=route))
    if operand_captures:
        outputs={p['output'] for p in paths}
        roots={r['root'] for r in candidates if r['stage']==0 and r['route'] and r['route']['terminal'] in outputs}
    # Extend only across genuine alias-connected sequential result registers.
    while True:
        more={r['root']for r in candidates if r['route']and r['route']['terminal']in roots}
        if more<=roots:break
        roots|=more
    return [r for r in candidates if r['root']in roots]

def capture_graph_evidence(graph,raw,rows):
    from cpu_pyslang_cdfg import dependencies
    symbols={s['path']:s for s in graph['symbols']}
    by_root={s['coq_root']:s for s in graph['symbols']}
    result=[]
    for row in rows:
        symbol=by_root[row['root']]
        edges=[e for e in graph['edges'] if e['target']==symbol['path']]
        if not edges or len({e['process'] for e in edges})!=1 or any(e['assignment']!='nonblocking' for e in edges):
            raise ValueError('capture is not a unique NBA process')
        actual=sorted((symbols[p]['width'],symbols[p]['coq_root']) for p in set().union(*(dependencies(e) for e in edges)))
        expression=rtl.Parser(row['next_expression']).complete()
        expected=sorted({tuple(int(a.name) for a in n.args) for n in rtl.walk(expression) if n.name=='EVar'})
        if symbol['width']!=row['width'] or actual!=expected:
            raise ValueError('capture data/control dependency mismatch')
        gp=next(p for p in graph['processes'] if p['id']==edges[0]['process'])
        events=[]
        def visit(value):
            if isinstance(value,dict):
                if value.get('kind')=='SignalEventControl':
                    if value['iff'] is not None or value['expr']['kind']!='NamedValueExpression':
                        raise ValueError('unsupported capture event expression')
                    edge={'EdgeKind.PosEdge':'Posedge','EdgeKind.NegEdge':'Negedge'}.get(value['edge'])
                    if edge is None:raise ValueError('unsupported capture edge')
                    events.append((edge,symbols[value['expr']['symbol']]['coq_root']))
                for v in value.values():visit(v)
            elif isinstance(value,list):
                for v in value:visit(v)
        visit(gp)
        proc=next(p for p in raw['processes'] if p['name']==row['process'])
        expected_events=[(e,int(x)) for e,x in re.findall(r'event_edge := (\w+); event_signal := (\d+)',proc['events'])]
        if not events or events!=expected_events:raise ValueError('capture phase mismatch')
        result.append(dict(root=row['root'],dependencies=actual,events=events,
                           graph_edges=[e['id'] for e in edges],recipe=row['recipe']))
    return result


def check(ast,module,history,output,operand_captures=False,graph_path=None,namespace='GeneratedResultCompanions'):
    if not rtl.SYMBOL.fullmatch(namespace):raise ValueError('invalid generated Coq namespace')
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=companion.pc.fetch.origin.raw_binding(ast,module)
    _,validity=companion.pc.provenance.hb.boot.chain.render(ast,module)
    chain=companion.pc.provenance.hb.coverage.capture.discover(raw,{r['rd']for r in validity['rows']})['chain']
    selected_rows=selected.discover(raw,validity['rows'])
    paths=data.discover(raw,selected_rows)
    rows=discover(raw,chain,paths,operand_captures)
    if not rows:raise ValueError('no result companion identified')
    if graph_path:
        from cpu_cdfg_result_consumer import checked_graph
        graph=checked_graph(graph_path,ast,out/'replayed')
        evidence=capture_graph_evidence(graph,raw,rows)
        (out/'capture-graph.json').write_text(json.dumps(evidence,indent=2)+'\n')
    loads=json.loads((Path(history)/'plan.json').read_text())['paths']
    profile['coq_load_paths']=loads
    _,remaining,_,source,_=companion.pc.fetch.origin.expressions.proposal(profile,{r['root']for r in rows})
    if remaining:raise ValueError('unproved scalar expressions')
    alias_roots={e['root']for r in rows if r['route']for e in r['route']['edges']}
    _,wire_plan,wire_source=companion.pc.fetch.rom.comb.proposal(profile,alias_roots)
    if wire_plan['residuals']:raise ValueError('unproved result aliases')
    ports={r['output_root']:i for i,r in enumerate(wire_plan['ports'])}
    p=profile['ast']['program'];am=p.rsplit('.',1)[0]
    source='Module S.\n'+source+'\nEnd S.\nModule ResultWires.\n'+wire_source+'\nEnd ResultWires.\n'+f'''From Coq Require Import ZArith.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVCompanionField Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarExpression GeneratedCoveredCapture.CoveredCapture.
Import ExtendedSV ExtendedSVScalarHistory ExtendedSVProjectionOrigin ExtendedSVCompanionField ExtendedSVWordInvariant ExtendedSVScalarExpression.
Module C:=GeneratedCoveredCapture.CoveredCapture.C.
Local Opaque {p} PhaseSemantics.
'''
    for r in rows:
        x=r['root'];w=r['width'];i=r['stage']
        source+=f'''Lemma self_{x}:self_widthb {w} {x} S.root_{x}_expression=true.
Proof. vm_compute;reflexivity. Qed.
Definition scalar_{x}:ScalarCertificate {p} {x} {w} {am}.{r['process']} S.root_{x}_expression:=
 Build_ScalarCertificate _ _ _ _ _ S.root_{x}_comb_frame self_{x} S.root_{x}_expression_phase.
Lemma match_{x}:RecipeMatches {w} {x} {r['capture']} S.root_{x}_expression C.projection_{i}_recipe.
Proof. unfold S.root_{x}_expression,C.projection_{i}_recipe. {r['proof']} Qed.
Theorem result_{x}_actual {{Label:Type}} (value:Label->option Z) ev pre old incoming:
 changed_signal ev<>{x}%nat ->FieldRelated value {w} {x} pre old ->
 ExpressionRelated value {w} {r['capture']}(phase_driven_state {p} ev pre) incoming ->
 FieldRelated value {w} {x}(PhaseSemantics {p} ev pre)
 (projection_phase_origin {p} {am}.{r['process']} C.projection_{i}_recipe ev pre old incoming).
Proof. exact(actual_expression_phase value _ _ _ _ _ _ _ scalar_{x} match_{x} ev pre old incoming). Qed.
'''
    exports=[f'result_{r["root"]}_actual'for r in rows]
    for r in rows:
        if not r['route']:continue
        x=r['root'];w=r['width'];i=r['stage'];parent=r['route']['terminal']
        sampled=f'(phase_driven_state {p} ev pre)'
        parent_is_register=parent in {q['root']for q in rows}
        location='pre'if parent_is_register else sampled
        source+=f'''Theorem result_{x}_connected {{Label:Type}} (value:Label->option Z) seed ev pre old incoming:
 CombLFP {p} seed {sampled} ->changed_signal ev<>{x}%nat ->
'''
        if parent_is_register:source+=f' changed_signal ev<>{parent}%nat ->\n'
        source+=f''' FieldRelated value {w} {x} pre old ->FieldRelated value {w} {parent} {location} incoming ->
 FieldRelated value {w} {x}(PhaseSemantics {p} ev pre)
 (projection_phase_origin {p} {am}.{r['process']} C.projection_{i}_recipe ev pre old incoming).
Proof. intros HL HE {'HP 'if parent_is_register else ''}HO HI.
 apply(result_{x}_actual value ev pre old incoming HE HO).
 intros label HT;cbn[eval_expr];rewrite norm_idempotent.
'''
        for e in r['route']['edges']:
            k=ports[e['root']]
            source+=f'rewrite(ResultWires.port_{k}_lfp seed _ HL);unfold ResultWires.port_{k}_rhs;cbn[eval_expr];rewrite norm_idempotent.\n'
        if parent_is_register:
            source+=f'rewrite(sampled_root_preserved {p} ev pre {parent}(history_comb_frame _ _ _ _ _ scalar_{parent})HP).\n'
        source+='exact(HI label HT). Qed.\n'
        exports.append(f'result_{x}_connected')
    source+='Goal True. idtac "RESULT_COMPANION_AUDIT". exact I. Qed.\n'
    if operand_captures:
        selected_source,selected_paths=data.render(ast,module,selected_rows)
        source+=f'Module SelectedOperands.\nLocal Transparent {p} PhaseSemantics.\n'+selected_source+'\nEnd SelectedOperands.\n'
        for r in rows:
            if not r['route'] or r['stage']!=0:continue
            x,w=r['root'],r['width']
            for j,path in enumerate(selected_paths):
                if path['output']!=r['route']['terminal']:continue
                controller=path['control']['terminal']; sw=path['sw']; code=path['code']; endpoint=path['data']['terminal']
                source+=f'''Theorem operand_{x}_selected_{j} {{Label:Type}} (value:Label->option Z) seed ev pre old incoming:
 CombLFP {p} seed (phase_driven_state {p} ev pre) ->changed_signal ev<>{x}%nat ->
 norm {sw}(read_signal(phase_driven_state {p} ev pre){controller})={code}%Z ->
 FieldRelated value {w} {x} pre old ->
 FieldRelated value {w} {endpoint}(phase_driven_state {p} ev pre) incoming ->
 FieldRelated value {w} {x}(PhaseSemantics {p} ev pre)
 (projection_phase_origin {p} {am}.{r['process']} C.projection_0_recipe ev pre old incoming).
Proof. intros HL HE HS HO HI;apply(result_{x}_connected value seed ev pre old incoming HL HE HO).
 intros label HT;rewrite(SelectedOperands.data_{j}_lfp seed _ HL HS);exact(HI label HT). Qed.
'''
                exports.append(f'operand_{x}_selected_{j}')
        source+='Goal True. idtac "RESULT_COMPANION_AUDIT". exact I. Qed.\n'
    source+=''.join(f'Print Assumptions {name}.\n'for name in exports)
    file=out/'ResultCompanions.v';file.write_text(source)
    (out/'plan.json').write_text(json.dumps(dict(rows=rows,paths=paths,ast_sha256=raw['source_sha256']),indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in loads:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(out.resolve()),namespace]
    start=time.monotonic()
    c,t=run_stage([str(companion.pc.fetch.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),complete_R_generated=False,capture_value_correctness_proved=False,old_inv_read=False)
    if c.returncode==0 and time.monotonic()-start<1200:
        tail=c.stdout.split('RESULT_COMPANION_AUDIT')[-1]
        closed=tail.count('Closed under the global context')==len(exports) and 'Axioms:'not in tail
        k,t=run_stage([str(companion.pc.fetch.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',namespace+'.ResultCompanions'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result.update(seconds=time.monotonic()-start,roots=[r['root']for r in rows],operand_captures=operand_captures,
                  operand_freshness_proved=False)
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history','output']:p.add_argument('--'+key,required=True)
    p.add_argument('--operand-captures',action='store_true')
    p.add_argument('--graph')
    p.add_argument('--namespace',default='GeneratedResultCompanions')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.history,a.output,a.operand_captures,a.graph,a.namespace)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
