"""Derive scalar metadata origin histories from constructor RTL only.

Capture functions are maximal subexpressions depending on one instruction
word. Hold/reset/stall branches retain their actual guards; unsupported paths
are UNKNOWN, never empty/valid. No prior CPU INV or CPU proof is an input.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origins
from cpu_certificate_acceptance import run_stage

rtl=origins.pending.rtl


def instruction_sources(ast):
    roots=set(origins.pending.analyze(ast)['instruction_word_candidates']);edges=[]
    for proc in ast['processes']:
        for n in rtl.walk(proc['body']):
            if n.name!='SAssign'or n.args[2].name!='LVar'or n.args[2].args[0].name!='32':continue
            for leaf in origins.pending.data_leaves(n.args[1]):
                if leaf.name=='EVar'and leaf.args[0].name=='32':edges.append((int(leaf.args[1].name),rtl.root_of(n.args[2])))
    while True:
        more={a for a,b in edges if b in roots}-roots
        if not more:return roots
        roots.update(more)


def is_hold(e,width,root):
    return e.name=='EVar'and e.args[0].name==str(width)and e.args[1].name==str(root)


def word_only(e,source):
    leaves=[n for n in rtl.walk(e)if n.name=='EVar']
    return bool(leaves)and all(n.args[0].name=='32'and n.args[1].name==str(source)for n in leaves)


def capture_expressions(e,width,root,source):
    if is_hold(e,width,root):return set()
    if word_only(e,source):return {rtl.render(e)}
    if e.name=='ECond'and e.args[0].name==str(width):
        return capture_expressions(e.args[2],width,root,source)|capture_expressions(e.args[3],width,root,source)
    return set()


def recipe(e,width,root,capture,path=()):
    if is_hold(e,width,root):return 'Hold','apply MatchesHold.',[]
    if e==capture:return 'Capture','apply MatchesCapture.',[]
    if e.name=='ECond'and e.args[0].name==str(width):
        yes,py,uy=recipe(e.args[2],width,root,capture,path+(True,))
        no,pn,un=recipe(e.args[3],width,root,capture,path+(False,))
        return f'(Select {rtl.render(e.args[1])} {yes} {no})','apply MatchesSelect.\n'+py+'\n'+pn,uy+un
    return 'Unknown','apply MatchesUnknown.',[dict(path=list(path),expression=rtl.render(e),
        reason='reset/constant or unsupported non-instruction source; no tag, not a vacancy')]


def discover(ast):
    sources=instruction_sources(ast);found=origins.captures.analyze(ast);rows=[];residuals=[]
    for root in found['analysis']['roots']:
        assignments=[n for p in ast['processes']for n in rtl.walk(p['body'])if n.name=='SAssign'and rtl.root_of(n.args[2])==root]
        width=int(assignments[0].args[2].args[0].name)
        if width>32:continue
        writers=[(p,plan)for p,plan in found['analysis']['plans']if root in p['writers']]
        if len(writers)!=1:continue
        proc,plan=writers[0]
        expr=origins.expressions.compile_expression(origins.pending.slices.slice_plan(plan,root),root,width,
            rtl.Term('EVar',(rtl.Term(str(width)),rtl.Term(str(root)))))
        if expr is None:continue
        for source in sorted(sources&set(origins.pending.roots(expr))):
            functions=capture_expressions(expr,width,root,source)
            if len(functions)>1:
                residuals.append(dict(root=root,source=source,reason='multiple capture functions require another relation',functions=sorted(functions)));continue
            if not functions:continue
            capture=rtl.Parser(next(iter(functions))).complete();tree,proof,unknown=recipe(expr,width,root,capture)
            rows.append(dict(root=root,width=width,source=source,process=proc['name'],
                expression=rtl.render(expr),capture=rtl.render(capture),recipe=tree,proof=proof,unknown_paths=unknown))
    return dict(instruction_sources=sorted(sources),projections=rows,residuals=residuals,
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        projection_reference='actual instruction-only capture expression, not ISA identity or an old invariant',
        upstream_identity_proved=False,validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False,
        complete_R_generated=False)


def discover_control_transforms(ast):
    """Scalar reference functions, not guessed instruction-word identities."""
    import cpu_control_capture_frontier as controls
    frontier=controls.discover(ast)
    fields={r['root']:r for r in frontier['capture_fields']}
    rows=[];residuals=[];seen=set()
    for item in frontier['transformed_captures']:
        root=item['root'];width=item['width'];capture=rtl.Parser(item['expression']).complete()
        reads={int(n.args[1].name) for n in rtl.walk(capture) if n.name=='EVar'}
        if len(reads)!=1 or not word_only(capture,next(iter(reads))):
            residuals.append(dict(root=root,reason='requires one 32-bit source'));continue
        source=next(iter(reads));key=(root,item['expression'])
        if key in seen:continue
        seen.add(key)
        expr=rtl.Parser(fields[root]['expression']).complete()
        tree,proof,unknown=recipe(expr,width,root,capture)
        rows.append(dict(root=root,width=width,source=source,process=item['process'],
            expression=rtl.render(expr),capture=rtl.render(capture),recipe=tree,proof=proof,unknown_paths=unknown))
    return dict(projections=rows,residuals=residuals,old_inv_read=False,old_pending_read=False,
        old_cpu_proofs_used=False,projection_reference='raw single-source transform; source is NOT assumed to be an instruction',
        upstream_identity_proved=False,validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def discover_narrow_fields(ast):
    """Five-bit field provenance; not an architectural destination binding."""
    found=origins.captures.analyze(ast);rows=[];residuals=[]
    def captures(e,root,source):
        if is_hold(e,5,root):return set()
        leaves=[n for n in rtl.walk(e)if n.name=='EVar']
        if leaves and all(n.args[0].name=='5'and n.args[1].name==str(source)for n in leaves):return {rtl.render(e)}
        if e.name=='ECond'and e.args[0].name=='5':return captures(e.args[2],root,source)|captures(e.args[3],root,source)
        return set()
    for root in found['analysis']['roots']:
        assignments=[n for p in ast['processes']for n in rtl.walk(p['body'])if n.name=='SAssign'and rtl.root_of(n.args[2])==root]
        if not assignments or assignments[0].args[2].args[0].name!='5':continue
        writers=[(p,plan)for p,plan in found['analysis']['plans']if root in p['writers']]
        if len(writers)!=1:continue
        proc,plan=writers[0]
        expr=origins.expressions.compile_expression(origins.pending.slices.slice_plan(plan,root),root,5,
            rtl.Term('EVar',(rtl.Term('5'),rtl.Term(str(root)))))
        if expr is None:continue
        sources={int(n.args[1].name)for n in rtl.walk(expr)if n.name=='EVar'and n.args[0].name=='5'}-{root}
        for source in sorted(sources):
            functions=captures(expr,root,source)
            if len(functions)!=1:
                residuals.append(dict(root=root,source=source,reason='requires one field capture function',functions=sorted(functions)));continue
            capture=rtl.Parser(next(iter(functions))).complete();tree,proof,unknown=recipe(expr,5,root,capture)
            rows.append(dict(root=root,width=5,source_width=5,source=source,process=proc['name'],
                expression=rtl.render(expr),capture=rtl.render(capture),recipe=tree,proof=proof,unknown_paths=unknown))
    return dict(projections=rows,residuals=residuals,old_inv_read=False,
        projection_reference='actual five-bit capture; ISA instruction ownership NOT inferred')


def render(ast_path,ast_module,selected_roots=None,source_mode='instruction'):
    ast,profile,paths=origins.raw_binding(ast_path,ast_module)
    discovery={'instruction':discover,'control_transform':discover_control_transforms,'narrow_field':discover_narrow_fields}
    if source_mode not in discovery:raise ValueError('unknown source mode')
    data=discovery[source_mode](ast)
    if selected_roots is not None:
        selected=set(selected_roots)
        data['projections']=[row for row in data['projections'] if row['root'] in selected]
        if {row['root'] for row in data['projections']} != selected:
            raise ValueError('requested roots lack inferred instruction origins')
        data['selected_roots']=sorted(selected)
    roots=sorted({row['root']for row in data['projections']})
    if not roots:raise ValueError('no metadata projection supported; no empty pending fallback')
    _,residuals,outputs,prefix,count=origins.expressions.proposal(profile,roots)
    if residuals:raise ValueError('scalar projection residual: '+json.dumps(residuals))
    program=profile['ast']['program'];lines=[
        'Require Import Lang.ExtendedSVProjectionOrigin Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant Lang.ExtendedSVFieldOrigin.',
        'Import ExtendedSVProjectionOrigin ExtendedSVScalarHistory ExtendedSVWordInvariant ExtendedSVFieldOrigin.',
        f'Local Opaque {program}.']
    for out in outputs:
        root=out['root'];w=out['width'];proc=ast['module']+'.'+out['process']
        lines += [f'Lemma root_{root}_projection_self : self_widthb {w} {root} root_{root}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition root_{root}_projection_certificate : ScalarCertificate {program} {root} {w} {proc} root_{root}_expression :=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{root}_comb_frame root_{root}_projection_self root_{root}_expression_phase.']
    for index,row in enumerate(data['projections']):
        stem=f'projection_{index}';root=row['root'];w=row['width'];source=row['source'];proc=ast['module']+'.'+row['process']
        sw=row.get('source_width',32)
        lines += [f'Definition {stem}_capture : Expr := {row["capture"]}.',
            f'Definition {stem}_recipe : OriginRecipe := {row["recipe"]}.',
            f'Definition {stem}_reference word := norm {w}(capture_value {source} {stem}_capture word).',
            f'Lemma {stem}_inputs : field_inputs_onlyb {sw} {source} {stem}_capture=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {stem}_checked : RecipeMatches {w} {root} {stem}_capture root_{root}_expression {stem}_recipe.',
            f'Proof. unfold root_{root}_expression,{stem}_recipe,{stem}_capture. {row["proof"]} Qed.',
            f'Definition {stem}_origin (Label:Type) ev pre (old incoming:option Label) :=',
            f' @projection_phase_origin Label {program} {proc} {stem}_recipe ev pre old incoming.',
            f'Theorem {stem}_actual_phase (Label:Type)(word:Label->Z) ev pre old incoming label :',
            f' changed_signal ev<>{root}%nat ->',
            f' (forall l,old=Some l ->norm {w}(read_signal pre {root})={stem}_reference(word l)) ->',
            f' (forall l,incoming=Some l ->norm {sw}(read_signal(phase_driven_state {program} ev pre){source})=norm {sw}(word l)) ->',
            f' {stem}_origin Label ev pre old incoming=Some label ->',
            f' norm {w}(read_signal(PhaseSemantics {program} ev pre){root})={stem}_reference(word label).',
            f'Proof. intro HE. exact(@actual_field_projection_phase Label word {sw} {program} {root} {w} {proc} root_{root}_expression',
            f' {source} {stem}_capture {stem}_recipe root_{root}_projection_certificate {stem}_checked',
            f' ev pre old incoming label HE {stem}_inputs). Qed.']
        for suffix in ['checked','actual_phase']:
            lines.append(f'Print Assumptions {stem}_{suffix}.');count+=1
    pairs=synchronized_pairs(data['projections'])
    for i,j in pairs:
        a,b=data['projections'][i],data['projections'][j]
        ra,rb=a['root'],b['root'];wa,wb=a['width'],b['width'];src=a['source']
        sw=a.get('source_width',32)
        name=f'synchronized_{i}_{j}'
        lines += [f'Theorem {name}_tags (Label:Type) ev pre (old incoming:option Label):',
            f' projection_{i}_origin Label ev pre old incoming=projection_{j}_origin Label ev pre old incoming.',
            'Proof. reflexivity. Qed.',
            f'Theorem {name}_values (Label:Type)(word:Label->Z) ev pre old incoming label:',
            f' changed_signal ev<>{ra}%nat ->changed_signal ev<>{rb}%nat ->',
            f' (forall l,old=Some l ->norm {wa}(read_signal pre {ra})=projection_{i}_reference(word l)) ->',
            f' (forall l,old=Some l ->norm {wb}(read_signal pre {rb})=projection_{j}_reference(word l)) ->',
            f' (forall l,incoming=Some l ->norm {sw}(read_signal(phase_driven_state {program} ev pre){src})=norm {sw}(word l)) ->',
            f' projection_{i}_origin Label ev pre old incoming=Some label ->',
            f' norm {wa}(read_signal(PhaseSemantics {program} ev pre){ra})=projection_{i}_reference(word label) /\\',
            f' norm {wb}(read_signal(PhaseSemantics {program} ev pre){rb})=projection_{j}_reference(word label).',
            'Proof. intros HA HB HOa HOb HI HT;split.',
            f' - exact(projection_{i}_actual_phase Label word ev pre old incoming label HA HOa HI HT).',
            f' - apply(projection_{j}_actual_phase Label word ev pre old incoming label HB HOb HI).',
            f'   exact(eq_trans(eq_sym({name}_tags Label ev pre old incoming))HT). Qed.',
            f'Print Assumptions {name}_tags.',f'Print Assumptions {name}_values.']
        count+=2
    data['synchronized_pairs']=[dict(left=i,right=j,roots=[data['projections'][i]['root'],data['projections'][j]['root']]) for i,j in pairs]
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,audited_exports=count),prefix+'\n'+'\n'.join(lines)+'\n'


def synchronized_pairs(rows):
    """A spanning set, avoiding a quadratic bundle. Same source/phase/guards.
    Matching field names or widths is deliberately insufficient.
    """
    groups={};pairs=[]
    for i,row in enumerate(rows):
        key=(row['process'],row['source'],row.get('source_width',32),row['recipe'])
        if key in groups:
            j=groups[key]
            if rows[j]['root']!=row['root']:pairs.append((j,i))
        else:groups[key]=i
    return pairs


def check_synchronized(ast_path,ast_module,output):
    ast,_,_=origins.raw_binding(ast_path,ast_module)
    data=discover(ast);pairs=synchronized_pairs(data['projections'])
    roots=sorted({data['projections'][i]['root'] for pair in pairs for i in pair})
    if roots:return check(ast_path,ast_module,output,selected_roots=roots)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,status='no_synchronized_fields_discovered',old_inv_read=False,
        synchronized_pairs=[],upstream_identity_proved=False,global_inv_proved=False)
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def check_narrow(ast_path,ast_module,output):
    ast,_,_=origins.raw_binding(ast_path,ast_module)
    data=discover_narrow_fields(ast)
    if data['projections']:return check(ast_path,ast_module,output,source_mode='narrow_field')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,status='no_narrow_field_transfer',old_inv_read=False,
        complete_R_generated=False,projection_count=0,residuals=data['residuals'])
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def check(ast_path,ast_module,output,timeout=1200,selected_roots=None,source_mode='instruction'):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    data,source=render(ast_path,ast_module,selected_roots,source_mode);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'ProjectionOrigins.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedProjectionOrigins'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='scalar reference-function transport over actual raw phases',source_mode=source_mode,
        complete_R_generated=False,
        coqc_exit=c.returncode,coqc_timed_out=t,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=data['ast_sha256'],
        projection_count=len(data['projections']),distinct_roots=len({r['root']for r in data['projections']}),
        synchronized_pairs=data['synchronized_pairs'],
        upstream_identity_proved=False,validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedProjectionOrigins.ProjectionOrigins'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--source-mode',choices=['instruction','control_transform','narrow_field'],default='instruction')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output,source_mode=a.source_mode);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
