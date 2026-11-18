"""Generate actual-LFP-to-phase metadata origin proofs from raw RTL only.

Only unique direct blocking scalar combinational writers are expanded. Every
expanded edge gets a new actual LFP certificate; a guessed connection is never
an invariant premise. Unsupported cones remain residuals, not empty tokens.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_projection_origins as direct
import cpu_comb_scalar_bindings as comb
from cpu_certificate_acceptance import run_stage

origin=direct.origins;rtl=direct.rtl


class Cones:
    def __init__(self,ast,budget=256):
        self.ast=ast;self.budget=budget;self.nodes={};self.failed={}

    def expand(self,e,stack=(),remaining=None):
        remaining=[self.budget]if remaining is None else remaining
        remaining[0]-=1
        if remaining[0]<0:raise ValueError('cone node budget exceeded; no partial expansion')
        if e.name=='EVar':
            width,root=int(e.args[0].name),int(e.args[1].name)
            writers=[p for p in self.ast['processes']if p['kind']!='Initial'and root in p['writers']]
            if not any(p['kind']=='Combinational'for p in writers):return e
            if root in stack:raise ValueError('combinational cycle')
            if len(writers)!=1:raise ValueError('non-unique combinational writer')
            proc=writers[0];body=proc['body']
            if body.name!='SAssign'or body.args[0].name!='false'or body.args[2].name!='LVar':
                raise ValueError('requires direct whole blocking assignment')
            if int(body.args[2].args[0].name)!=width:raise ValueError('read/write width mismatch')
            expanded=self.expand(body.args[1],stack+(root,),remaining)
            self.nodes[root]=dict(root=root,width=width,process=proc['name'],rhs=body.args[1],expanded=expanded)
            return rtl.Term('EExtend',(rtl.Term(str(width)),rtl.Term('false'),expanded))
        return rtl.Term(e.name,tuple(self.expand(a,stack,remaining)if a.name.startswith('E')else a for a in e.args))

    def bindings(self,e):
        return sorted({int(n.args[1].name)for n in rtl.walk(e)if n.name=='EVar'and int(n.args[1].name)in self.nodes
            and self.nodes[int(n.args[1].name)]['width']==int(n.args[0].name)})

    def closure(self,expressions):
        ordered=[];done=set()
        def visit(root):
            if root in done:return
            done.add(root)
            for child in self.bindings(self.nodes[root]['rhs']):visit(child)
            ordered.append(root)
        for expr in expressions:
            for root in self.bindings(expr):visit(root)
        return ordered


def find_captures(e,width,root,sources,cones):
    if direct.is_hold(e,width,root):return []
    try:
        expanded=cones.expand(e)
        reads={int(n.args[1].name)for n in rtl.walk(expanded)if n.name=='EVar'}
        if len(reads)==1:
            source=next(iter(reads))
            if source in sources and direct.word_only(expanded,source)and cones.bindings(e):
                return [dict(source=source,capture=rtl.render(e),expanded=rtl.render(expanded))]
    except ValueError as error:
        cones.failed.setdefault(rtl.render(e),str(error))
    if e.name=='ECond'and e.args[0].name==str(width):
        return find_captures(e.args[2],width,root,sources,cones)+find_captures(e.args[3],width,root,sources,cones)
    return []


def scalar_candidates(ast):
    found=origin.captures.analyze(ast)
    for root in found['analysis']['roots']:
        assignments=[n for p in ast['processes']for n in rtl.walk(p['body'])if n.name=='SAssign'and rtl.root_of(n.args[2])==root]
        width=int(assignments[0].args[2].args[0].name)
        if width>32:continue
        writers=[(p,plan)for p,plan in found['analysis']['plans']if root in p['writers']]
        if len(writers)!=1:continue
        proc,plan=writers[0]
        expr=origin.expressions.compile_expression(origin.pending.slices.slice_plan(plan,root),root,width,
            rtl.Term('EVar',(rtl.Term(str(width)),rtl.Term(str(root)))))
        if expr is not None:yield dict(root=root,width=width,process=proc['name'],expression=expr)


def discover(ast):
    sources=direct.instruction_sources(ast);cones=Cones(ast);rows=[];residuals=[]
    for scalar in scalar_candidates(ast):
        root=scalar['root'];width=scalar['width'];expr=scalar['expression']
        captures={r['capture']:r for r in find_captures(expr,width,root,sources,cones)}
        if len(captures)!=1:
            if captures:residuals.append(dict(root=root,reason='multiple connected capture functions',captures=list(captures.values())))
            continue
        row=next(iter(captures.values()));capture=rtl.Parser(row['capture']).complete()
        recipe,proof,unknown=direct.recipe(expr,width,root,capture)
        rows.append(dict(root=root,width=width,process=scalar['process'],expression=rtl.render(expr),
            recipe=recipe,proof=proof,unknown_paths=unknown,**row))
    order=cones.closure([rtl.Parser(row['capture']).complete()for row in rows])
    return dict(projections=rows,cone_order=order,
        cones=[dict(root=r,width=cones.nodes[r]['width'],process=cones.nodes[r]['process'],
            rhs=rtl.render(cones.nodes[r]['rhs']),expanded=rtl.render(cones.nodes[r]['expanded']),
            children=cones.bindings(cones.nodes[r]['rhs']))for r in order],
        residuals=residuals,unsupported_cones=cones.failed,old_inv_read=False,old_pending_read=False,
        upstream_identity_proved=False,validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if not data['projections']:raise ValueError('no supported connected capture; no empty fallback')
    _,analysis,comb_source=comb.proposal(profile,data['cone_order'])
    if analysis['residuals']:raise ValueError('actual combinational certificate residual')
    ports={r['output_root']:i for i,r in enumerate(analysis['ports'])}
    roots=sorted({r['root']for r in data['projections']})
    _,remaining,outputs,scalar_source,count=origin.expressions.proposal(profile,roots)
    if remaining:raise ValueError('actual scalar certificate residual')
    count+=len(analysis['ports']);program=profile['ast']['program'];byroot={r['root']:r for r in data['cones']}
    lines=['Require Import Lang.ExtendedSVProjectionConnection Lang.ExtendedSVProjectionOrigin',
        ' Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVProjectionConnection ExtendedSVProjectionOrigin ExtendedSVScalarHistory ExtendedSVWordInvariant.',
        f'Local Opaque {program}.']
    def table(name,children):
        return f'Definition {name}:list Binding:=['+';'.join(
            f'Build_Binding {byroot[r]["width"]} {r} cone_{r}_expanded'for r in children)+'].'
    def agreement(name,children):
        result=[f'Lemma {name}_agree seed fixed:CombLFP {program} seed fixed ->BindingsAgree fixed {name}.',
            f'Proof. intro HL. unfold {name},BindingsAgree.']
        for r in children:result += [f' constructor;[exact(cone_{r}_sound seed fixed HL)|].']
        return result+[' constructor. Qed.']
    for row in data['cones']:
        r=row['root'];w=row['width'];i=ports[r];children=row['children'];name=f'cone_{r}_bindings'
        lines += [table(name,children),*agreement(name,children),
            f'Definition cone_{r}_expanded:=substitute(lookup_binding {name})port_{i}_rhs.',
            f'Lemma cone_{r}_sound seed fixed:CombLFP {program} seed fixed ->',
            f' norm {w}(read_signal fixed {r})=norm {w}(eval_expr fixed cone_{r}_expanded).',
            f'Proof. intro HL. exact(eq_trans(port_{i}_lfp seed fixed HL)',
            f' (f_equal(norm {w})(eq_sym(bindings_substitute_sound {name} port_{i}_rhs fixed({name}_agree seed fixed HL))))). Qed.']
    for out in outputs:
        r=out['root'];w=out['width'];proc=ast['module']+'.'+out['process']
        lines += [f'Lemma root_{r}_connected_self:self_widthb {w} {r} root_{r}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition root_{r}_connected_certificate:ScalarCertificate {program} {r} {w} {proc} root_{r}_expression:=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{r}_comb_frame root_{r}_connected_self root_{r}_expression_phase.']
    def children_for(e):
        return sorted({int(n.args[1].name)for n in rtl.walk(e)if n.name=='EVar'and int(n.args[1].name)in byroot})
    for index,row in enumerate(data['projections']):
        stem=f'connected_{index}';r=row['root'];w=row['width'];src=row['source'];proc=ast['module']+'.'+row['process']
        children=children_for(rtl.Parser(row['capture']).complete());name=stem+'_bindings'
        lines += [table(name,children),*agreement(name,children),
            f'Definition {stem}_capture:Expr:={row["capture"]}.',
            f'Definition {stem}_expanded:=substitute(lookup_binding {name}){stem}_capture.',
            f'Definition {stem}_reference word:=norm {w}(capture_value {src} {stem}_expanded word).',
            f'Lemma {stem}_inputs:capture_inputs_onlyb {src} {stem}_expanded=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {stem}_at_lfp seed fixed word:CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {src})=norm 32 word ->',
            f' norm {w}(eval_expr fixed {stem}_capture)={stem}_reference word.',
            'Proof. intros HL HW.',
            f' pose proof(bindings_substitute_sound {name} {stem}_capture fixed({name}_agree seed fixed HL))as HC.',
            f' change(eval_expr fixed {stem}_expanded=eval_expr fixed {stem}_capture)in HC.',
            f' unfold {stem}_reference. rewrite <-HC.',
            f' rewrite(capture_value_sound {src} {stem}_expanded fixed word {stem}_inputs HW). reflexivity. Qed.',
            f'Definition {stem}_recipe:OriginRecipe:={row["recipe"]}.',
            f'Lemma {stem}_checked:RecipeMatches {w} {r} {stem}_capture root_{r}_expression {stem}_recipe.',
            f'Proof. unfold {stem}_recipe,{stem}_capture,root_{r}_expression. {row["proof"]} Qed.',
            f'Theorem {stem}_actual_phase(Label:Type)(word:Label->Z)seed ev pre old incoming label:',
            f' changed_signal ev<>{r}%nat ->CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' (forall l,old=Some l ->norm {w}(read_signal pre {r})={stem}_reference(word l)) ->',
            f' (forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {program} ev pre){src})=norm 32(word l)) ->',
            f' @projection_phase_origin Label {program} {proc} {stem}_recipe ev pre old incoming=Some label ->',
            f' norm {w}(read_signal(PhaseSemantics {program} ev pre){r})={stem}_reference(word label).',
            'Proof. intros HE HL Hold Hinput HT.',
            f' eapply(@connected_actual_phase Label(fun l=>{stem}_reference(word l)) {program} {r} {w} {proc}',
            f' root_{r}_expression {stem}_capture {stem}_recipe root_{r}_connected_certificate {stem}_checked',
            f' ev pre old incoming label);[exact HE|exact Hold| |exact HT].',
            f' intros l Hl. exact({stem}_at_lfp seed(phase_driven_state {program} ev pre)(word l) HL(Hinput l Hl)). Qed.']
        for suffix in['at_lfp','actual_phase']:
            lines.append(f'Print Assumptions {stem}_{suffix}.');count+=1
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,audited_exports=count),comb_source+'\n'+scalar_source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    data,source=render(ast_path,ast_module);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'ConnectedProjections.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedConnectedProjections'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='actual combinational LFP consumed by actual decoded-field capture phase',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=data['ast_sha256'],projection_count=len(data['projections']),cone_count=len(data['cones']),
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,upstream_identity_proved=False,
        validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedConnectedProjections.ConnectedProjections'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
