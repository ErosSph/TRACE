"""Connect narrow-field histories to actual next-phase write address aliases."""
import argparse,json,time,hashlib
from pathlib import Path
import cpu_zero_instruction_rf as rf
import cpu_pending_projection_origins as projections
from cpu_certificate_acceptance import run_stage

def discover(ast):
    rows=projections.discover_narrow_fields(ast)['projections']
    byroot={r['root']:r for r in rows if sum(x['root']==r['root']for x in rows)==1}
    banks=rf.banks.analyze(ast);matches=[];residuals=[]
    for bank in banks['banks']:
        addresses=set()
        def visit(plan):
            if plan.name=='BPWord':
                addresses.update(int(n.args[1].name)for n in rf.rtl.walk(plan.args[0])if n.name=='EVar'and n.args[0].name=='5')
            elif plan.name=='BPSeq':
                for x in plan.args[0].args:visit(x)
            elif plan.name=='BPIf':visit(plan.args[1]);visit(plan.args[2])
        for _,_,plan in bank['plans']:visit(plan)
        if not addresses:residuals.append(dict(bank=bank['root'],reason='no dynamic five-bit write address'))
        for address in sorted(addresses):
            root=address;path=[];seen=set()
            while root not in seen and root not in byroot:
                seen.add(root)
                writers=[p for p in ast['processes']if root in p['writers']]
                if len(writers)!=1 or writers[0]['kind']!='Combinational':break
                body=writers[0]['body']
                if body.name!='SAssign' or body.args[0].name!='false':break
                rhs,lhs=body.args[1:]
                if rhs.name!='EVar'or rhs.args[0].name!='5'or lhs.name!='LVar'or lhs.args[0].name!='5':break
                path.append(root);root=int(rhs.args[1].name)
            if root in byroot and path:
                matches.append(dict(bank=bank['root'],address=address,leaf=root,path=path))
            else:residuals.append(dict(bank=bank['root'],address=address,frontier=root,path=path,
                reason='no proved narrow-field endpoint through direct aliases'))
    return matches,residuals

def render(ast_path,ast_module):
    ast,profile,paths=rf.origin.raw_binding(ast_path,ast_module);matches,residuals=discover(ast)
    if not matches:return None,dict(matches=[],residuals=residuals,paths=paths)
    data,prefix=projections.render(ast_path,ast_module,selected_roots={m['leaf']for m in matches},source_mode='narrow_field')
    _,bindings,wires=rf.comb.proposal(profile,{r for m in matches for r in m['path']})
    if bindings['residuals']:raise ValueError('actual alias certificates unavailable')
    indices={p['output_root']:i for i,p in enumerate(bindings['ports'])};p=profile['ast']['program'];lines=[]
    for k,m in enumerate(matches):
        i=next(i for i,r in enumerate(data['projections'])if r['root']==m['leaf']);r=data['projections'][i]
        leaf,source=m['leaf'],r['source'];proc=ast['module']+'.'+r['process']
        sample=f'(phase_driven_state {p} next_ev (PhaseSemantics {p} ev pre))'
        lines += [f'Theorem history_to_write_address_{k} (Label:Type)(value:Label->Z) ev next_ev pre old incoming label seed:',
            f' changed_signal ev<>{leaf}%nat ->changed_signal next_ev<>{leaf}%nat ->',
            f' (forall l,old=Some l ->norm 5(read_signal pre {leaf})=projection_{i}_reference(value l)) ->',
            f' (forall l,incoming=Some l ->norm 5(read_signal(phase_driven_state {p} ev pre){source})=norm 5(value l)) ->',
            f' projection_{i}_origin Label ev pre old incoming=Some label ->',
            f' CombLFP {p} seed {sample} ->',
            f' norm 5(read_signal {sample} {m["address"]})=projection_{i}_reference(value label).',
            'Proof. intros HE HN HO HI HT HL.']
        for root in m['path']:
            j=indices[root]
            lines += [f' rewrite(port_{j}_lfp seed _ HL);unfold port_{j}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
        lines += [f' rewrite(sampled_root_preserved {p} next_ev (PhaseSemantics {p} ev pre) {leaf}',
            f' (history_comb_frame _ _ _ _ _ root_{leaf}_projection_certificate) HN).',
            f' exact(projection_{i}_actual_phase Label value ev pre old incoming label HE HO HI HT). Qed.',
            f'Goal True. idtac "WRITE_ADDRESS_AUDIT_{k}". exact I. Qed.',
            f'Print Assumptions history_to_write_address_{k}.']
    return prefix+f'\nLocal Transparent {p}.\n'+wires+f'\nLocal Opaque {p}.\n'+'\n'.join(lines)+'\n',dict(matches=matches,residuals=residuals,paths=paths)

def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    source,data=render(ast_path,ast_module)
    report=dict(accepted=False,complete_R_generated=False,isa_destination_proved=False,
        incoming_identity_proved=False,old_inv_read=False,matches=data['matches'],residuals=data['residuals'])
    if source is None:report['status']='no_write_address_history_match'
    else:
        file=output/'WriteAddressHistory.v';file.write_text(source)
        flags=list(rf.rtl.framework.FLAGS)
        for row in data['paths']:flags+=['-R',row['directory'],row['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedWriteAddress']
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(rf.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
        if c.returncode==0 and time.monotonic()<deadline:
            import re
            marks=list(re.finditer(r'^WRITE_ADDRESS_AUDIT_\d+\s*$',c.stdout,re.M))
            chunks=[c.stdout[m.end():marks[i+1].start()if i+1<len(marks)else len(c.stdout)]for i,m in enumerate(marks)]
            closed=len(chunks)==len(data['matches'])and all(s.count('Closed under the global context')==1 and'Axioms:'not in s for s in chunks)
            k,t=run_stage([str(rf.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedWriteAddress.WriteAddressHistory'],output/'coqchk.log',deadline-time.monotonic())
            report.update(export_assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for n in ['ast','ast-module','output']:p.add_argument('--'+n,required=True)
    a=p.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.output),indent=2))
