"""Infer validity-conditioned metadata origin coverage from raw RTL.

This proves valid -> known origin, NOT preservation of every admitted token.
No prior CPU INV/pending/theorem catalog is read. Ambiguous indicators remain
residuals; missing origins are never filtered into an empty queue.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_metadata_copies as metadata
import cpu_pending_validity as validity
from cpu_certificate_acceptance import run_stage

connected=metadata.connected;origin=connected.origin;rtl=connected.rtl


class CoverageGap(ValueError):
    def __init__(self,data):
        super().__init__('no unique metadata-validity coverage; no empty fallback')
        self.data=data


def guards(recipe):
    if recipe.name!='Select':return set()
    return set(origin.pending.roots(recipe.args[0]))|guards(recipe.args[1])|guards(recipe.args[2])


def payload_recipe(row):
    capture=rtl.Parser(row['capture']).complete();width=row['width'];root=row['root']
    def build(e):
        if connected.direct.is_hold(e,width,root):return rtl.Term('Hold')
        if e==capture:return rtl.Term('Capture')
        if e.name=='ECond'and e.args[0].name==str(width):
            return rtl.Term('Select',(e.args[1],build(e.args[2]),build(e.args[3])))
        return rtl.Term('Unknown')
    result=build(rtl.Parser(row['expression']).complete())
    if rtl.render(result)!=row['recipe']:raise ValueError('recipe does not match newly inferred payload')
    return result


class BitCones(connected.Cones):
    """Unknown factors remain actual expressions; no value is assumed for them."""
    def __init__(self,ast,stops=()):
        super().__init__(ast);self.stops=set(stops);self.eligible={}
        roots={r for p in ast['processes']if p['kind']=='Combinational'for r in p['writers']}
        for root in roots:
            writers=[p for p in ast['processes']if p['kind']!='Initial'and root in p['writers']]
            if len(writers)!=1:continue
            p=writers[0];body=p['body']
            if body.name=='SAssign'and body.args[0].name=='false'and body.args[2].name=='LVar':
                self.eligible[root]=(p,body)
        active=[];done=set();cut=set()
        def visit(root):
            if root in active:cut.update(active[active.index(root):]);return
            if root in done:return
            active.append(root)
            for child in origin.pending.roots(self.eligible[root][1].args[1]):
                if child in self.eligible:visit(child)
            active.pop();done.add(root)
        for root in self.eligible:visit(root)
        self.stops.update(cut)

    def expand(self,e,stack=(),remaining=None):
        remaining=[self.budget]if remaining is None else remaining
        remaining[0]-=1
        if remaining[0]<0:raise ValueError('bit cone budget exceeded; no partial certificate')
        if e.name=='EVar':
            width,root=int(e.args[0].name),int(e.args[1].name)
            if root in self.stops or root not in self.eligible:return e
            p,body=self.eligible[root]
            if body.args[2].args[0].name!=str(width):return e
            expanded=self.expand(body.args[1],stack+(root,),remaining)
            self.nodes[root]=dict(root=root,width=width,process=p['name'],rhs=body.args[1],expanded=expanded)
            return rtl.Term('EExtend',(rtl.Term(str(width)),rtl.Term('false'),expanded))
        return rtl.Term(e.name,tuple(self.expand(a,stack,remaining)if a.name.startswith('E')else a for a in e.args))


def requires(e,root):
    if validity.is_var(e,1,root):return 'apply RequiresSource.'
    if validity.is_const(e,1,0):return 'apply RequiresZero.'
    if e.name=='EExtend'and e.args[0].name=='1'and e.args[1].name=='false':
        proof=requires(e.args[2],root)
        return None if proof is None else'apply RequiresExtend.\n'+proof
    if e.name=='EBinary'and e.args[0].name=='1'and e.args[1].name=='BAnd':
        left=requires(e.args[2],root);right=requires(e.args[3],root)
        if left is not None:return 'apply RequiresAndLeft.\n'+left
        if right is not None:return 'apply RequiresAndRight.\n'+right
    if e.name=='ECond'and e.args[0].name=='1':
        yes=requires(e.args[2],root);no=requires(e.args[3],root)
        if yes is not None and no is not None:return 'apply RequiresChoice.\n'+yes+'\n'+no
    return None


def maybe_nonzero(e):
    if validity.is_const(e,1,0):return False
    if e.name=='EExtend'and e.args[0].name=='1'and e.args[1].name=='false':return maybe_nonzero(e.args[2])
    if e.name=='EBinary'and e.args[0].name=='1'and e.args[1].name=='BAnd':return maybe_nonzero(e.args[2])and maybe_nonzero(e.args[3])
    return True  # overapproximation only, never a completeness/satisfiability proof


def cover(recipe,valid,oldvalid,inputvalid,cones):
    if recipe.name=='Select':
        if valid.name!='ECond'or valid.args[0].name!='1'or valid.args[1]!=recipe.args[0]:return None
        yes=cover(recipe.args[1],valid.args[2],oldvalid,inputvalid,cones)
        no=cover(recipe.args[2],valid.args[3],oldvalid,inputvalid,cones)
        if yes is None or no is None:return None
        return rtl.Term('ECond',(rtl.Term('1'),valid.args[1],yes[0],no[0])), 'apply CoveredSelect.\n'+yes[1]+'\n'+no[1]
    if recipe.name=='Unknown':
        return (valid,'apply CoveredUnknown.')if validity.is_const(valid,1,0)else None
    try:expanded=cones.expand(valid)
    except ValueError:return None
    if recipe.name=='Capture'and not maybe_nonzero(expanded):return None
    proof=requires(expanded,oldvalid if recipe.name=='Hold'else inputvalid)
    if proof is None:return None
    return expanded,'apply '+('CoveredHold'if recipe.name=='Hold'else'CoveredCapture')+'.\n'+proof


def coverage_gap(recipe,valid,oldvalid,inputvalid,cones,path=()):
    """Explain a failed syntactic certificate, never claim a DUT counterexample.

    Paths are actual recipe guards, not facts assumed true for the CPU. They
    allow a rule generator or LLM to identify the missing obligation without
    consulting old CPU invariants.
    """
    context=dict(path=list(path),recipe=rtl.render(recipe),valid_expression=rtl.render(valid),
                 old_valid_root=oldvalid,source_valid_root=inputvalid)
    if recipe.name=='Select':
        guard=rtl.render(recipe.args[0])
        if valid.name!='ECond'or valid.args[0].name!='1'or valid.args[1]!=recipe.args[0]:
            return dict(context,reason='different_guard_structure',required_guard=guard)
        for branch,index in [(True,1),(False,2)]:
            gap=coverage_gap(recipe.args[index],valid.args[index+1],oldvalid,inputvalid,cones,
                             path+(dict(guard=guard,nonzero=branch),))
            if gap is not None:return gap
        return None
    if recipe.name=='Unknown':
        return None if validity.is_const(valid,1,0)else dict(context,reason='unknown_origin_not_zero_valid')
    try:expanded=cones.expand(valid)
    except ValueError as exc:return dict(context,reason='connection_expansion_limit',detail=str(exc))
    if recipe.name=='Capture'and not maybe_nonzero(expanded):
        return dict(context,reason='vacuous_capture_indicator')
    required=oldvalid if recipe.name=='Hold'else inputvalid
    if requires(expanded,required)is None:
        return dict(context,reason='missing_validity_implication',expanded=rtl.render(expanded),
                    required_nonzero_root=required)
    return None


def discover(ast,relations=None,base=None):
    base=validity.discover(ast)if base is None else base
    relations=metadata.discover(ast)if relations is None else relations
    scalars=list(connected.scalar_candidates(ast))
    known={row['carrier']:row['valid_root']for row in base['pairs']}
    rows=relations['direct_origins']+relations['connected_origins']+relations['copy_edges']
    selected=[];decisions=[];done=set();gaps={}
    while True:
        added=False
        for row in rows:
            root=row['root'];source=row['source']
            if root in known or root in done or source not in known:continue
            recipe=payload_recipe(row);candidates=[]
            for peer in scalars:
                if peer['width']!=1 or peer['process']!=row['process']or peer['root']==root:continue
                cones=BitCones(ast,guards(recipe));result=cover(recipe,peer['expression'],peer['root'],known[source],cones)
                if result is None:
                    gap=coverage_gap(recipe,peer['expression'],peer['root'],known[source],
                                     BitCones(ast,guards(recipe)))
                    gaps[(root,source,peer['root'])]=dict(root=root,source=source,
                        candidate_valid_root=peer['root'],process=row['process'],gap=gap)
                    continue
                expanded,proof=result;order=cones.closure([peer['expression']])
                candidates.append(dict(root=root,width=row['width'],source=source,source_valid=known[source],
                    valid_root=peer['root'],process=row['process'],recipe=row['recipe'],capture=row['capture'],
                    payload_expression=row['expression'],payload_proof=row['proof'],
                    valid_expression=rtl.render(peer['expression']),expanded=rtl.render(expanded),proof=proof,
                    cones=[dict(root=r,width=cones.nodes[r]['width'],rhs=rtl.render(cones.nodes[r]['rhs']),
                        children=cones.bindings(cones.nodes[r]['rhs']))for r in order]))
            if len(candidates)==1:
                selected+=candidates;known[root]=candidates[0]['valid_root'];done.add(root);added=True
            elif candidates:
                decisions.append(dict(root=root,reason='ambiguous validity-conditioned indicators',candidates=candidates));done.add(root)
        if not added:break
    return dict(seed_validity=base['pairs'],covered_fields=selected,known_validity={str(k):v for k,v in known.items()},residuals=decisions,
        coverage_gaps=[v for k,v in sorted(gaps.items())if k[0]not in known],
        coverage_gap_scope='missing syntactic proof obligations, not reachable counterexamples or assumptions',
        unresolved_fields=sorted({row['root']for row in rows}-known.keys()),old_inv_read=False,old_pending_read=False,
        validity_direction='post valid implies a known origin; not lossless token transport',
        validity_completeness_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module,relations=None):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module);data=discover(ast,relations=relations)
    if not data['covered_fields']:raise CoverageGap(data)
    # Keep proof names local to each field; different sources may leave different
    # factors opaque. Never merge these replacement environments by root alone.
    cone_roots=sorted({n['root']for row in data['covered_fields']for n in row['cones']})
    _,analysis,combsource=connected.comb.proposal(profile,cone_roots)if cone_roots else(None,dict(ports=[],residuals=[]),'')
    if analysis['residuals']:raise ValueError('actual bit-connection certificate residual')
    ports={p['output_root']:i for i,p in enumerate(analysis['ports'])}
    roots=sorted({r for row in data['covered_fields']for r in(row['root'],row['valid_root'],row['source_valid'])})
    _,remaining,outputs,source,count=origin.expressions.proposal(profile,roots)
    if remaining:raise ValueError('actual scalar validity certificate residual')
    count+=len(analysis['ports']);program=profile['ast']['program']
    lines=['Require Import Lang.ExtendedSVRecipeCoverage Lang.ExtendedSVProjectionConnection',
        ' Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVRecipeCoverage ExtendedSVProjectionConnection ExtendedSVProjectionOrigin ExtendedSVScalarHistory',
        ' ExtendedSVScalarExpression ExtendedSVWordInvariant.',f'Local Opaque {program}.']
    for out in outputs:
        r=out['root'];w=out['width'];proc=ast['module']+'.'+out['process']
        lines += [f'Lemma root_{r}_valid_self:self_widthb {w} {r} root_{r}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition root_{r}_valid_certificate:ScalarCertificate {program} {r} {w} {proc} root_{r}_expression:=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{r}_comb_frame root_{r}_valid_self root_{r}_expression_phase.']
    for index,row in enumerate(data['covered_fields']):
        stem=f'coverage_{index}';byroot={n['root']:n for n in row['cones']}
        def table(name,children):return f'Definition {name}:list Binding:=['+';'.join(
            f'Build_Binding {byroot[r]["width"]} {r} {stem}_cone_{r}'for r in children)+'].'
        def agreement(name,children):
            result=[f'Lemma {name}_agree seed fixed:CombLFP {program} seed fixed ->BindingsAgree fixed {name}.',f'Proof. intro HL. unfold {name},BindingsAgree.']
            for r in children:result += [f' constructor;[exact({stem}_cone_{r}_sound seed fixed HL)|].']
            return result+[' constructor. Qed.']
        for node in row['cones']:
            r=node['root'];w=node['width'];name=f'{stem}_bind_{r}';i=ports[r]
            lines += [table(name,node['children']),*agreement(name,node['children']),
                f'Definition {stem}_cone_{r}:=substitute(lookup_binding {name})port_{i}_rhs.',
                f'Lemma {stem}_cone_{r}_sound seed fixed:CombLFP {program} seed fixed ->',
                f' norm {w}(read_signal fixed {r})=norm {w}(eval_expr fixed {stem}_cone_{r}).',
                f'Proof. intro HL. exact(eq_trans(port_{i}_lfp seed fixed HL)',
                f' (f_equal(norm {w})(eq_sym(bindings_substitute_sound {name} port_{i}_rhs fixed({name}_agree seed fixed HL))))). Qed.']
        v=row['valid_root'];iv=row['source_valid'];proc=ast['module']+'.'+row['process'];w=row['width'];r=row['root']
        expr=rtl.Parser(row['valid_expression']).complete()
        children=sorted({int(n.args[1].name)for n in rtl.walk(expr)if n.name=='EVar'and int(n.args[1].name)in byroot})
        name=stem+'_bindings';lines += [table(name,children),*agreement(name,children),
            f'Definition {stem}_expanded:Expr:={row["expanded"]}.',
            f'Lemma {stem}_expansion_checked:substitute(lookup_binding {name})root_{v}_expression={stem}_expanded.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {stem}_recipe:OriginRecipe:={row["recipe"]}.',
            f'Definition {stem}_capture:Expr:={row["capture"]}.',
            f'Lemma {stem}_payload_checked:RecipeMatches {w} {r} {stem}_capture root_{r}_expression {stem}_recipe.',
            f'Proof. unfold {stem}_recipe,{stem}_capture,root_{r}_expression. {row["payload_proof"]} Qed.',
            f'Lemma {stem}_checked:RecipeCovered {v} {iv} {stem}_expanded {stem}_recipe.',
            f'Proof. unfold {stem}_expanded,{stem}_recipe. {row["proof"]} Qed.',
            f'Theorem {stem}_actual_phase(Label:Type)seed ev pre(old incoming:option Label):',
            f' changed_signal ev<>{v}%nat ->changed_signal ev<>{iv}%nat ->',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' (norm 1(read_signal pre {v})<>0%Z ->exists label,old=Some label) ->',
            f' (norm 1(read_signal pre {iv})<>0%Z ->exists label,incoming=Some label) ->',
            f' norm 1(read_signal(PhaseSemantics {program} ev pre){v})<>0%Z ->',
            f' exists label,@projection_phase_origin Label {program} {proc} {stem}_recipe ev pre old incoming=Some label.',
            'Proof. intros HE HS HL Hold Hinput HV.',
            f' eapply(@actual_recipe_coverage Label {program} {v} {proc} root_{v}_expression {stem}_expanded',
            f' {stem}_recipe {iv} root_{v}_valid_certificate {stem}_checked ev pre old incoming);',
            ' [exact HE|exact Hold| | |exact HV].',
            f' - rewrite(sampled_root_preserved {program} ev pre {iv} root_{iv}_comb_frame HS). exact Hinput.',
            f' - pose proof(bindings_substitute_sound {name} root_{v}_expression(phase_driven_state {program} ev pre)',
            f'   ({name}_agree seed(phase_driven_state {program} ev pre)HL))as HX.',
            f'   rewrite {stem}_expansion_checked in HX. exact(f_equal(norm 1)(eq_sym HX)). Qed.']
        for suffix in['payload_checked','checked','actual_phase']:
            lines.append(f'Print Assumptions {stem}_{suffix}.');count+=1
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,audited_exports=count),combsource+'\n'+source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,old_pending_read=False,
            validity_completeness_proved=False,global_inv_proved=False,itree_refinement_proved=False)
        if isinstance(error,CoverageGap):
            (output/'plan.json').write_text(json.dumps(error.data,indent=2)+'\n')
            report['coverage_gap_count']=len(error.data['coverage_gaps'])
            report['unresolved_fields']=error.data['unresolved_fields']
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'RecipeCoverage.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedRecipeCoverage'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,native_started=True,scope='actual phase post-valid implies known metadata origin',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=data['ast_sha256'],covered_field_count=len(data['covered_fields']),old_inv_read=False,old_pending_read=False,
        validity_completeness_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRecipeCoverage.RecipeCoverage'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--analyze-only',action='store_true');a=p.parse_args()
    if a.analyze_only:
        ast,_,_=origin.raw_binding(a.ast,a.ast_module);data=discover(ast);a.output.mkdir(parents=True,exist_ok=False)
        (a.output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
        r=dict(analysis_completed=True,accepted=False,native_started=False,covered_field_count=len(data['covered_fields']),
            old_inv_read=False,old_pending_read=False,validity_completeness_proved=False,global_inv_proved=False,itree_refinement_proved=False)
        (a.output/'report.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
    else:
        r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
