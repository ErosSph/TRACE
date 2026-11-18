"""Propagate inferred instruction metadata through actual NBA pipeline copies.

Seeds and edges are discovered from raw RTL, not old invariant definitions.
The theorem consumes a real source-field relation at the previous phase and
new checked combinational wiring. Validity, token age and commit remain open.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_connected_projections as connected
import cpu_scalar_expression_paths as paths
from cpu_certificate_acceptance import run_stage

origin=connected.origin;rtl=connected.rtl


def trace(ast,width,root):
    start=root;edges=[];seen=set()
    while True:
        if root in seen:return None
        seen.add(root)
        writers=[p for p in ast['processes']if p['kind']!='Initial'and root in p['writers']]
        if not any(p['kind']=='Combinational'for p in writers):
            return dict(input=start,source=root,width=width,edges=edges,
                source_sequential=any(p['kind']=='Sequential'for p in writers))
        if len(writers)!=1:return None
        proc=writers[0];st=proc['body']
        if st.name!='SAssign'or st.args[0].name!='false':return None
        rhs,lhs=st.args[1:]
        if lhs.name!='LVar'or rhs.name!='EVar'or lhs.args[0].name!=str(width)or rhs.args[0].name!=str(width):return None
        parent=int(rhs.args[1].name);edges.append(dict(root=root,parent=parent,width=width,process=proc['name']));root=parent


def discover(ast):
    direct=connected.direct.discover(ast);derived=connected.discover(ast)
    seeds={r['root']for data in(direct,derived)for r in data['projections']}
    candidates=[];residuals=[]
    for scalar in connected.scalar_candidates(ast):
        root=scalar['root'];width=scalar['width'];expression=scalar['expression'];captures={}
        # Reuse the actual expression-path visitor; no branch is assumed true.
        for choices,leaf in paths.leaf_paths(expression,width):
            if connected.direct.is_hold(leaf,width,root):continue
            if leaf.name=='EConst':continue
            if leaf.name!='EVar'or leaf.args[0].name!=str(width):
                captures[rtl.render(leaf)]=None;continue
            chain=trace(ast,width,int(leaf.args[1].name))
            captures[rtl.render(leaf)]=chain
        if len(captures)!=1:continue
        capture,chain=next(iter(captures.items()))
        if chain is None or not chain['source_sequential']or chain['source']==root:continue
        recipe,proof,unknown=connected.direct.recipe(expression,width,root,rtl.Parser(capture).complete())
        candidates.append(dict(root=root,width=width,process=scalar['process'],expression=rtl.render(expression),
            capture=capture,source=chain['source'],alias_chain=chain,recipe=recipe,proof=proof,unknown_paths=unknown))
    known=set(seeds);selected=[];remaining=candidates[:]
    while True:
        ready=[r for r in remaining if r['source']in known]
        if not ready:break
        selected+=ready;known.update(r['root']for r in ready);remaining=[r for r in remaining if r not in ready]
    return dict(seeds=sorted(seeds),direct_origins=direct['projections'],connected_origins=derived['projections'],copy_edges=selected,
        residuals=[dict(root=r['root'],source=r['source'],reason='source has no newly inferred instruction-field relation')for r in remaining],
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if not data['copy_edges']:raise ValueError('no supported metadata pipeline copy; no empty pending fallback')
    combroots=sorted({e['root']for row in data['copy_edges']for e in row['alias_chain']['edges']})
    if combroots:
        _,analysis,combsource=connected.comb.proposal(profile,combroots)
        if analysis['residuals']:raise ValueError('actual copy wiring residual')
        ports={r['output_root']:i for i,r in enumerate(analysis['ports'])};count=len(ports)
    else:combsource='';ports={};count=0
    roots=sorted({r for row in data['copy_edges']for r in(row['root'],row['source'])})
    _,residuals,outputs,source,audits=origin.expressions.proposal(profile,roots)
    if residuals:raise ValueError('actual scalar phase residual')
    count+=audits;program=profile['ast']['program'];lines=[
        'Require Import Lang.ExtendedSVProjectionConnection Lang.ExtendedSVProjectionOrigin',
        ' Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVProjectionConnection ExtendedSVProjectionOrigin ExtendedSVScalarHistory',
        ' ExtendedSVScalarExpression ExtendedSVWordInvariant.',f'Local Opaque {program}.']
    for row in outputs:
        r=row['root'];w=row['width'];proc=ast['module']+'.'+row['process']
        lines += [f'Lemma root_{r}_copy_self:self_widthb {w} {r} root_{r}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition root_{r}_copy_certificate:ScalarCertificate {program} {r} {w} {proc} root_{r}_expression:=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{r}_comb_frame root_{r}_copy_self root_{r}_expression_phase.']
    for index,row in enumerate(data['copy_edges']):
        stem=f'copy_{index}';r=row['root'];src=row['source'];w=row['width'];proc=ast['module']+'.'+row['process']
        lines += [f'Definition {stem}_capture:Expr:={row["capture"]}.',
            f'Definition {stem}_recipe:OriginRecipe:={row["recipe"]}.',
            f'Lemma {stem}_checked:RecipeMatches {w} {r} {stem}_capture root_{r}_expression {stem}_recipe.',
            f'Proof. unfold {stem}_capture,{stem}_recipe,root_{r}_expression. {row["proof"]} Qed.',
            f'Lemma {stem}_lfp seed fixed:CombLFP {program} seed fixed ->',
            f' norm {w}(eval_expr fixed {stem}_capture)=norm {w}(read_signal fixed {src}).',
            f'Proof. intro HL. unfold {stem}_capture. cbn[eval_expr]. rewrite norm_idempotent.']
        term='eq_refl'
        for edge in reversed(row['alias_chain']['edges']):
            step=f'(eq_trans(port_{ports[edge["root"]]}_lfp seed fixed HL)(norm_idempotent {w}(read_signal fixed {edge["parent"]})))'
            term=f'(eq_trans {step} {term})'
        lines += [f' exact {term}. Qed.',
            f'Theorem {stem}_actual_phase(Label:Type)(reference:Label->Z)seed ev pre old incoming label:',
            f' changed_signal ev<>{r}%nat ->changed_signal ev<>{src}%nat ->',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' (forall l,old=Some l ->norm {w}(read_signal pre {r})=reference l) ->',
            f' (forall l,incoming=Some l ->norm {w}(read_signal pre {src})=reference l) ->',
            f' @projection_phase_origin Label {program} {proc} {stem}_recipe ev pre old incoming=Some label ->',
            f' norm {w}(read_signal(PhaseSemantics {program} ev pre){r})=reference label.',
            'Proof. intros HE HS HL Hold Hinput HT.',
            f' eapply(@connected_actual_phase Label reference {program} {r} {w} {proc} root_{r}_expression',
            f' {stem}_capture {stem}_recipe root_{r}_copy_certificate {stem}_checked ev pre old incoming label);',
            ' [exact HE|exact Hold| |exact HT].',
            f' intros l Hi. rewrite({stem}_lfp seed(phase_driven_state {program} ev pre)HL).',
            f' rewrite(sampled_root_preserved {program} ev pre {src} root_{src}_comb_frame HS). exact(Hinput l Hi). Qed.']
        for suffix in['lfp','actual_phase']:
            lines.append(f'Print Assumptions {stem}_{suffix}.');count+=1
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,audited_exports=count),combsource+'\n'+source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    data,source=render(ast_path,ast_module);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'MetadataCopies.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedMetadataCopies'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='raw-RTL metadata pipeline copies using previous-phase source relations',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=data['ast_sha256'],copy_edge_count=len(data['copy_edges']),old_inv_read=False,old_pending_read=False,
        validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedMetadataCopies.MetadataCopies'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
