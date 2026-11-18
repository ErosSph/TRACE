"""Raw field inputs -> actual blocking mux equations -> guarded origin.
Every branch must be a same-width source or conditional source selection.
No constant/unsupported branch is silently replaced by a missing token.
"""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_field_chain_history as chain
import cpu_blocking_selector as selector
from cpu_certificate_acceptance import run_stage

def reduce_bit_case(e):
    """Recognize exactly the shape proved by exhaustive_bit_case."""
    if e.name!='ECond':return e,False
    width,guard,yes,tail=e.args
    if tail.name!='ECond'or tail.args[0]!=width:return e,False
    def guard_root(g,constant):
        if g.name!='EBinary'or g.args[0].name!='1'or g.args[1].name!='BEq':return None
        a,b=g.args[2:]
        if a.name!='EVar'or a.args[0].name!='1':return None
        if b.name!='EConst'or b.args[0].name!='1'or b.args[1].name!=str(constant):return None
        return a
    root=guard_root(guard,1)
    if root is not None and guard_root(tail.args[1],0)==root:
        return chain.p.rtl.Term('ECond',(width,root,yes,tail.args[2])),True
    root=guard_root(guard,0)
    if root is not None and guard_root(tail.args[1],1)==root:
        return chain.p.rtl.Term('ECond',(width,root,tail.args[2],yes)),True
    return e,False

def route(e,width,projected=False):
    if not projected and e.name=='EVar'and e.args[0].name==str(width):
        return f'(Source {e.args[1].name})','apply MatchSource.',[int(e.args[1].name)]
    if e.name=='ECond'and e.args[0].name==str(width):
        yes=route(e.args[2],width,projected);no=route(e.args[3],width,projected)
        return f'(Choice {chain.p.rtl.render(e.args[1])} {yes[0]} {no[0]})','apply MatchChoice.\n'+yes[1]+'\n'+no[1],sorted(set(yes[2]+no[2]))
    if projected:
        if e.name=='EConst':return f'(Literal {e.args[0].name} {e.args[1].name})','apply MatchLiteral.',[]
        inputs={(int(t.args[0].name),int(t.args[1].name))for t in chain.p.rtl.walk(e)if t.name=='EVar'}
        if len(inputs)==1:
            sw,root=next(iter(inputs))
            return f'(Project {sw} {root} {chain.p.rtl.render(e)})','apply MatchProject;vm_compute;reflexivity.',[root]
    raise ValueError('non-source selection leaf: '+chain.p.rtl.render(e))

def literal_leaves(e,width):
    if e.name=='ECond'and e.args[0].name==str(width):
        return literal_leaves(e.args[2],width)+literal_leaves(e.args[3],width)
    if e.name=='EConst':return [f'(Literal {e.args[0].name} {e.args[1].name})']
    return []

def discover(ast,projected=False):
    fields=chain.p.discover_narrow_fields(ast)['projections'];rows=[];residuals=[]
    for root in sorted({r['source']for r in fields}):
        writers=[p for p in ast['processes']if root in p['writers']]
        if len(writers)!=1 or writers[0]['kind']!='Combinational':continue
        proc=writers[0]
        try:
            _,_,width,inputs,expr=selector.proposal(proc,root)
            original=expr
            expr,reduced=reduce_bit_case(expr)if projected else(expr,False)
            tree,proof,leaves=route(expr,width,projected)
            literals=literal_leaves(expr,width)if projected else[]
            if len(leaves)<2 and not(projected and literals):continue
            rows.append(dict(root=root,process=proc['name'],width=width,expression=chain.p.rtl.render(expr),
                original_expression=chain.p.rtl.render(original),exhaustive_bit_case=reduced,
                reduction_lemma=('exhaustive_bit_case_zero'if reduced and original.args[1].args[3].args[1].name=='0'else'exhaustive_bit_case'),
                literal_sources=literals,
                route=tree,proof=proof,sources=leaves,self_source=root in leaves))
        except ValueError as error:residuals.append(dict(root=root,process=proc['name'],reason=str(error)))
    return dict(selectors=rows,residuals=residuals)

def render(ast_path,ast_module,projected=False):
    ast,profile,paths=chain.p.origins.raw_binding(ast_path,ast_module);data=discover(ast,projected);parts=[]
    p=profile['ast']['program']
    for i,r in enumerate(data['selectors']):
        source,_,_=selector.render(ast_path,ast_module,r['process'],r['root'])
        library='ExtendedSVProjectedSelectorOrigin'if projected else'ExtendedSVSelectorOrigin'
        parts += [f'Module M{i}.',source,
            f'Require Import Lang.{library}. Import {library}.',
            f'Definition origin_expression:Expr:={r["expression"]}.']
        if r['exhaustive_bit_case']:
            parts += ['Require Import Lang.ExtendedSVExhaustiveBitCase.',
                'Lemma origin_expression_correct s:eval_expr s selector_expression=eval_expr s origin_expression.',
                f'Proof. unfold selector_expression,origin_expression;apply ExtendedSVExhaustiveBitCase.{r["reduction_lemma"]}. Qed.']
        else:
            parts += ['Lemma origin_expression_correct s:eval_expr s selector_expression=eval_expr s origin_expression.',
                'Proof. reflexivity. Qed.']
        parts += [
            f'Definition origin_route:Route:={r["route"]}.',
            f'Lemma route_checked:Matches {r["width"]} origin_expression origin_route.',
            'Proof. unfold origin_expression,origin_route. '+r['proof']+' Qed.']
        if projected:
            parts += ['Theorem actual_selected_origin(Label:Type)(value:signal->Label->Z)(tags:signal->option Label)seed fixed choice:',
                f'CombLFP {p} seed fixed ->InputsRelated origin_route fixed tags value ->',
                'selected fixed origin_route tags=Some choice ->',
                f'norm {r["width"]}(read_signal fixed {r["root"]})=reference_value {r["width"]} value choice.',
                'Proof. intros HL HR HT;rewrite(selector_actual_lfp seed fixed HL),origin_expression_correct.',
                f'exact(selected_value {r["width"]} origin_expression origin_route route_checked fixed tags value HR choice HT). Qed.',f'End M{i}.']
            continue
        parts += [
            f'Theorem actual_selected_origin(Label:Type)(reference:Label->Z)(tags:signal->option Label)seed fixed label:',
            f'CombLFP {p} seed fixed ->',
            f'(forall root l,tags root=Some l ->norm {r["width"]}(read_signal fixed root)=reference l) ->',
            'selected fixed origin_route tags=Some label ->',
            f'norm {r["width"]}(read_signal fixed {r["root"]})=reference label.',
            'Proof. intros HL HR HT;rewrite(selector_actual_lfp seed fixed HL),origin_expression_correct.',
            f'exact(selected_value {r["width"]} origin_expression origin_route route_checked fixed tags reference HR label HT). Qed.',f'End M{i}.']
    parts+=['Goal True. idtac "FIELD_SELECTOR_ORIGIN_AUDIT". exact I. Qed.']
    parts += [f'Print Assumptions M{i}.actual_selected_origin.'for i in range(len(data['selectors']))]
    return ('\n'.join(parts)+'\n'if data['selectors']else None),dict(**data,paths=paths)

def check(ast_path,ast_module,output,projected=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=False);source,data=render(ast_path,ast_module,projected)
    report=dict(accepted=False,complete_R_generated=False,old_inv_read=False,isa_identity_proved=False,
        validity_coverage_proved=False,projected=projected,reference_is_ISA=False,selectors=[dict(root=r['root'],sources=r['sources'],self_source=r['self_source'],literal_sources=r['literal_sources'])for r in data['selectors']],residuals=data['residuals'])
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    if source is None:report['status']='no_supported_field_selector'
    else:
        file=output/'FieldSelector.v';file.write_text(source);flags=list(chain.p.rtl.framework.FLAGS)
        for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedFieldSelector'];start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(chain.p.origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            marks=list(re.finditer(r'^FIELD_SELECTOR_ORIGIN_AUDIT\s*$',c.stdout,re.M));tail=c.stdout[marks[-1].end():]if marks else ''
            closed=len(marks)==1 and tail.count('Closed under the global context')==len(data['selectors'])and'Axioms:'not in tail
            k,t=run_stage([str(chain.p.origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedFieldSelector.FieldSelector'],output/'coqchk.log',deadline-time.monotonic())
            report.update(export_assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:parser.add_argument('--'+name,required=True)
    parser.add_argument('--projected',action='store_true')
    a=parser.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.output,a.projected),indent=2))
