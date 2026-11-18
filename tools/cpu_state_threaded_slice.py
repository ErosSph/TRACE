"""Checked dependency-closed blocking slices, including temporary writes.
The proposal computes a finite write/read closure. Coq checks the slice against
the original process and connects its sequential execution to the actual LFP.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_blocking_selector as scalar
from cpu_certificate_acceptance import run_stage
rtl=scalar.rtl


def discover(ast):
    import cpu_operand_route_proofs as routes
    import cpu_control_capture_frontier as controls
    analysis,_=routes.analyze(ast);procs={p['name']:p for p in ast['processes']}
    found=[];residuals=[];requested=set()
    for row in analysis['residuals']:
        proc=procs[row['process']]
        if proc['kind']!='Combinational':continue
        for root in row['roots']:
            requested.add((proc['name'],root))
    for row in controls.discover(ast)['residuals']:
        root=row.get('producer')
        if root is None:continue
        writers=[p for p in ast['processes'] if root in p['writers'] and p['kind']!='Initial']
        if len(writers)==1 and writers[0]['kind']=='Combinational':
            requested.add((writers[0]['name'],root))
    for name,root in sorted(requested):
        try:
            plan,_=closure(procs[name],root)
            if len(plan['targets'])>1:found.append(dict(process=name,**plan))
        except ValueError as e:residuals.append(dict(root=root,reason=str(e)))
    return dict(candidates=found,residuals=residuals,old_inv_read=False,complete_R_generated=False)


def slice_statement(st,targets):
    T=rtl.Term
    if not any(n.name=='SAssign' and rtl.root_of(n.args[2]) in targets for n in rtl.walk(st)):
        return T('SSkip')
    n,a=st.name,st.args
    if n=='SAssign':return st
    if n=='SSeq':return T(n,(T('list',tuple(slice_statement(x,targets) for x in a[0].args)),))
    if n=='SIf':return T(n,(a[0],slice_statement(a[1],targets),slice_statement(a[2],targets)))
    if n=='SCase':return T(n,(a[0],T('list',tuple(T('pair',(x.args[0],slice_statement(x.args[1],targets))) for x in a[1].args))))
    raise ValueError('unsupported statement; no partial slice')


def closure(proc,root):
    if proc['kind']!='Combinational':raise ValueError('requires combinational process')
    assignments=[n for n in rtl.walk(proc['body']) if n.name=='SAssign']
    widths={int(n.args[2].args[0].name) for n in assignments if n.args[2].name=='LVar' and rtl.root_of(n.args[2])==root}
    if len(widths)!=1:raise ValueError('one whole scalar width required')
    writes={rtl.root_of(n.args[2]) for n in assignments};targets={root}
    while True:
        body=slice_statement(proc['body'],targets)
        reads={int(n.args[1].name) for n in rtl.walk(body) if n.name=='EVar'}
        added=(reads&writes)-targets
        if not added:break
        targets|=added
    return dict(root=root,width=next(iter(widths)),targets=sorted(targets),
        roots=sorted(targets|reads),external_inputs=sorted(reads-writes)),body


def render(ast_path,ast_module,process,root):
    ast,profile,paths=scalar.origin.raw_binding(ast_path,ast_module)
    proc=next(p for p in ast['processes'] if p['name']==process)
    plan,body=closure(proc,root);p=profile['ast']['program'];pn=ast['module']+'.'+process
    index=[x for x in ast['processes'] if x['kind']=='Combinational'].index(proc)
    nums=lambda xs:'['+';'.join(str(x)+'%nat' for x in xs)+']'
    targets=nums(plan['targets']);roots=nums(plan['roots']);w=plan['width']
    source=f'''From Coq Require Import List ZArith.
Require Import Lang.ExtendedSV Lang.ExtendedSVOutputSlice Lang.ExtendedSVBlocking
 Lang.ExtendedSVStateSliceBinding {ast_module}.
Import ListNotations ExtendedSV ExtendedSVOutputSlice ExtendedSVBlocking ExtendedSVStateSliceBinding.
Definition retained_body:Stmt:={rtl.render(body)}.
Definition retained_proc:=sliced_process {p} {targets} {pn}.
Lemma retained_body_checked:process_body retained_proc=retained_body.
Proof. vm_compute. reflexivity. Qed.
Lemma slice_safe:output_slice_safeb(statement_fuel {p}) {targets} {roots}(process_body {pn})=true.
Proof. vm_compute. reflexivity. Qed.
Lemma original_blocking:blocking_onlyb(process_body {pn})=true.
Proof. vm_compute. reflexivity. Qed.
Lemma slice_blocking:blocking_onlyb(process_body retained_proc)=true.
Proof. rewrite retained_body_checked. vm_compute. reflexivity. Qed.
Definition local_value s:=norm {w}(read_signal(run_process {p} s retained_proc){root}).
Lemma local_projection s:norm {w}(read_signal(run_process {p} s {pn}){root})=local_value s.
Proof.
 assert(HR:In {root}%nat {roots})by(simpl;tauto).
 exact(f_equal(norm {w})(actual_output_slice_process {p} {targets} {roots} {pn} s
 slice_safe original_blocking slice_blocking {root}%nat HR)). Qed.
Definition combs:=filter is_comb(processes {p}).
Lemma registered:nth_error combs {index}=Some {pn}.
Proof. vm_compute. reflexivity. Qed.
Lemma bound:bindingb combs {index} {root} {roots}=true.
Proof. vm_compute. reflexivity. Qed.
Theorem actual_lfp_projection seed fixed:CombLFP {p} seed fixed ->
 norm {w}(read_signal fixed {root})=local_value fixed.
Proof. intro HL.
 assert(HR:In {root}%nat {roots})by(simpl;tauto).
 exact(f_equal(norm {w})(actual_slice_at_lfp {p} combs {index} {pn} {targets} {roots}
 {root}%nat seed fixed eq_refl registered slice_safe original_blocking slice_blocking HR bound HL)). Qed.
Print Assumptions actual_lfp_projection.
'''
    plan.update(process=process,ast_sha256=ast['source_sha256'],original_order_preserved=True,
        old_inv_read=False,complete_R_generated=False,token_history_proved=False)
    return plan,source,paths


def check(ast_path,ast_module,process,root,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be within 20 minutes')
    plan,source,paths=render(ast_path,ast_module,process,root)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'StateSlice.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedStateSlice']
    report=dict(accepted=False,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        retained_targets=plan['targets'],complete_R_generated=False,token_history_proved=False,old_inv_read=False)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(scalar.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report.update(coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0 and time.monotonic()<deadline:
        report['assumptions_closed']=c.stdout.count('Closed under the global context')==1 and 'Axioms:' not in c.stdout
        k,t=run_stage([str(scalar.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedStateSlice.StateSlice'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and report['assumptions_closed'])
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','process','output']:p.add_argument('--'+n,required=True)
    p.add_argument('--root',type=int,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.process,a.root,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted'] else 1)
