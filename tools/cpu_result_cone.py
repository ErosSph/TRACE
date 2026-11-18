"""Proof-producing combinational dependency slicing at result capture inputs.

Sequential and unsupported boundaries stay explicit. No control branch is pruned.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_result_companions as companions
import cpu_nba_observation_connection as nba_observation
from cpu_certificate_acceptance import run_stage
rtl=companions.rtl

def cone(raw,width,root):
    nodes={};boundaries={};active=set()
    def visit(w,x):
        key=(w,x)
        if key in nodes or key in boundaries:return
        if key in active:raise ValueError('combinational dependency cycle')
        writers=[p for p in raw['processes']if x in p['writers']]
        if len(writers)!=1 or writers[0]['kind']!='Combinational':
            # An actually unwritten boundary is different from an ambiguous
            # writer. Keep the latter unsupported; do not merge the two to
            # make CDFG boundary comparison pass.
            reason=('external_or_unresolved' if not writers else
                    'sequential' if len(writers)==1 and writers[0]['kind']=='Sequential' else 'external_or_ambiguous')
            boundaries[key]=dict(width=w,root=x,reason=reason);return
        p=writers[0];plan=companions.data.cases.case_plan(p)
        st=companions.data.cases.unwrap(p['body'])
        if plan is not None:ww,xx,e=plan;kind='case'
        elif st.name=='SAssign'and st.args[0].name=='false'and st.args[2].name=='LVar':
            ww,xx=[int(a.name)for a in st.args[2].args];e=st.args[1];kind='assignment'
        else:
            try:
                _,_,ww,_,e=companions.data.wires.selectors.proposal(p,x)
                xx=x;kind='blocking_slice'
            except ValueError as error:
                try:
                    _,e=nba_observation.proposal(p,x,w)
                    ww,xx,kind=w,x,'nba_slice'
                except ValueError as nba_error:
                    boundaries[key]=dict(width=w,root=x,reason='unsupported_process',
                        detail=str(error)+'; NBA: '+str(nba_error));return
        if (ww,xx)!=key:raise ValueError('dependency width or destination mismatch')
        active.add(key)
        deps=sorted({tuple(int(a.name)for a in n.args)for n in rtl.walk(e)if n.name=='EVar'})
        for dep in deps:visit(*dep)
        active.remove(key)
        nodes[key]=dict(width=w,root=x,kind=kind,process=p['name'],expression=rtl.render(e),dependencies=deps)
    visit(width,root)
    return dict(nodes=list(nodes.values()),boundaries=list(boundaries.values()),root=root,width=width)

def render(ast,module,raw,profile,plan):
    assigns={n['root']for n in plan['nodes']if n['kind']=='assignment'}
    _,wires,source=companions.companion.pc.fetch.rom.comb.proposal(profile,assigns)
    if wires['residuals']:raise ValueError('unproved cone assignments')
    ports={r['output_root']:i for i,r in enumerate(wires['ports'])}
    source='Module ConeAssignments.\n'+source+'\nEnd ConeAssignments.\n'
    for n in plan['nodes']:
        if n['kind']=='case':
            text,_=companions.data.cases.render(ast,module,n['process'],structural=True)
            source+=f'Module ConeCase{n["root"]}.\n{text}\nEnd ConeCase{n["root"]}.\n'
        elif n['kind']=='blocking_slice':
            text,_,_=companions.data.wires.selectors.render(ast,module,n['process'],n['root'])
            source+=f'Module ConeSlice{n["root"]}.\n{text}\nEnd ConeSlice{n["root"]}.\n'
        elif n['kind']=='nba_slice':
            text,_,_=nba_observation.render(ast,module,n['process'],n['root'],n['width'])
            source+=f'Module ConeNBA{n["root"]}.\n{text}\nEnd ConeNBA{n["root"]}.\n'
    p=profile['ast']['program']
    source+='''From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVProjectionConnection.
Import ListNotations ExtendedSV ExtendedSVProjectionConnection.
'''
    source+=f'Require Import {module}.\nLocal Opaque {p}.\n'
    available=set()
    for n in plan['nodes']:
        w,x=n['width'],n['root']
        deps=[(a,b)for a,b in n['dependencies']if(a,b)in available]
        entries=[f'{{|binding_width:={a};binding_root:={b};binding_expr:=cone_{b}|}}'for a,b in deps]
        if n['kind']=='case':original,theorem=f'ConeCase{x}.case_expression',f'ConeCase{x}.case_actual_lfp'
        elif n['kind']=='blocking_slice':original,theorem=f'ConeSlice{x}.selector_expression',f'ConeSlice{x}.selector_actual_lfp'
        elif n['kind']=='nba_slice':original,theorem=f'ConeNBA{x}.output_expression',f'ConeNBA{x}.actual_lfp'
        else:original,theorem=f'ConeAssignments.port_{ports[x]}_rhs',f'ConeAssignments.port_{ports[x]}_lfp'
        source+=f'''Definition bindings_{x}:list Binding:=[{';'.join(entries)}].
Definition cone_{x}:Expr:=substitute(lookup_binding bindings_{x}){original}.
Theorem cone_{x}_actual seed fixed:CombLFP {p} seed fixed ->
 norm {w}(read_signal fixed {x})=norm {w}(eval_expr fixed cone_{x}).
Proof. intro HL;rewrite({theorem} seed fixed HL).
 unfold cone_{x};symmetry;apply f_equal;apply bindings_substitute_sound.
 unfold bindings_{x}.
'''
        for a,b in deps:source+=f'constructor;[exact(cone_{b}_actual seed fixed HL)|].\n'
        source+='constructor. Qed.\n';available.add((w,x))
    source+='Goal True. idtac "RESULT_CONE_AUDIT". exact I. Qed.\n'
    source+=''.join(f'Print Assumptions cone_{n["root"]}_actual.\n'for n in plan['nodes'])
    return source

def check(ast,module,history,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    raw,profile,_=companions.companion.pc.fetch.origin.raw_binding(ast,module)
    _,v=companions.companion.pc.provenance.hb.boot.chain.render(ast,module)
    chain=companions.companion.pc.provenance.hb.coverage.capture.discover(raw,{r['rd']for r in v['rows']})['chain']
    paths=companions.data.discover(raw,companions.selected.discover(raw,v['rows']))
    rows=companions.discover(raw,chain,paths)
    roots={(r['width'],r['route']['terminal'])for r in rows if r['route']and r['route']['kind']=='computed'}
    if len(roots)!=1:raise ValueError('expected one computed result entry; multiple cones require separate outputs')
    plan=cone(raw,*next(iter(roots)))
    if not plan['nodes'] or plan['nodes'][-1]['root']!=plan['root']:
        raise ValueError('result entry has no supported combinational proof')
    loads=json.loads((Path(history)/'plan.json').read_text())['paths'];profile['coq_load_paths']=loads
    capture_report=companions.check(ast,module,history,out/'captures')
    if not capture_report['accepted']:
        report=dict(accepted=False,capture_provider=capture_report,complete_R_generated=False)
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    source=render(ast,module,raw,profile,plan)
    p=profile['ast']['program'];am=p.rsplit('.',1)[0];root=plan['root'];sample=f'(phase_driven_state {p} ev pre)'
    linked=[r for r in rows if r['route']and r['route']['terminal']==root]
    source+='''Require GeneratedResultCompanions.ResultCompanions.
Require Import Lang.ExtendedSVCompanionField Lang.ExtendedSVProjectionOrigin.
Import ExtendedSVCompanionField ExtendedSVProjectionOrigin.
Module RC:=GeneratedResultCompanions.ResultCompanions.
'''
    for r in linked:
        x=r['root'];w=r['width'];i=r['stage']
        source+=f'''Theorem capture_{x}_from_cone {{Label:Type}} (value:Label->option Z) seed ev pre old incoming:
 CombLFP {p} seed {sample} ->changed_signal ev<>{x}%nat ->
 FieldRelated value {w} {x} pre old ->ExpressionRelated value {w} cone_{root} {sample} incoming ->
 FieldRelated value {w} {x}(PhaseSemantics {p} ev pre)
 (projection_phase_origin {p} {am}.{r['process']} RC.C.projection_{i}_recipe ev pre old incoming).
Proof. intros HL HE HO HI;apply(RC.result_{x}_connected value seed ev pre old incoming HL HE HO).
 intros label HT;rewrite(cone_{root}_actual seed _ HL);exact(HI label HT). Qed.
'''
    source+='Goal True. idtac "RESULT_CONE_CAPTURE_AUDIT". exact I. Qed.\n'
    source+=''.join(f'Print Assumptions capture_{r["root"]}_from_cone.\n'for r in linked)
    file=out/'ResultCone.v';file.write_text(source)
    (out/'plan.json').write_text(json.dumps(dict(**plan,ast_sha256=raw['source_sha256']),indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in loads:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedResultCone','-R',str((out/'captures').resolve()),'GeneratedResultCompanions']
    start=time.monotonic()
    c,t=run_stage([str(companions.companion.pc.fetch.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),complete_R_generated=False,isa_value_correctness_proved=False,old_inv_read=False)
    if c.returncode==0 and time.monotonic()-start<1200:
        tail=c.stdout.split('RESULT_CONE_AUDIT')[-1]
        closed=tail.count('Closed under the global context')==len(plan['nodes'])+len(linked)and'Axioms:'not in tail
        k,t=run_stage([str(companions.companion.pc.fetch.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedResultCone.ResultCone'],out/'coqchk.log',1200-(time.monotonic()-start))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    report.update(seconds=time.monotonic()-start,nodes=len(plan['nodes']),boundaries=len(plan['boundaries']),capture_provider=capture_report,linked_capture_roots=[r['root']for r in linked])
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.history,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
