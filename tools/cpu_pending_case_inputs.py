"""Infer and prove default-case instruction-copy domains from raw RTL.

Known selector values are conditional proof domains, not assumed reachable
facts. No CPU names, old INV, or old CPU theorem interface is consulted.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_instruction_word_aliases as aliases
import cpu_pending_tracker as tracker
import cpu_comb_scalar_bindings as comb
from cpu_certificate_acceptance import run_stage


def default(arms):
    result=origin.pending.rtl.Term('SSkip')
    for key,body in (a.args for a in arms.args):
        if key.name=='None':result=body
    return result


def specialize(st,selector,value):
    T=origin.pending.rtl.Term;n=st.name;a=st.args
    if n=='SCase'and a[0]==selector:
        keys=[key.args[0]for key,_ in (arm.args for arm in a[1].args)if key.name=='Some']
        if all(k.name=='EConst'and tracker.norm(int(k.args[0].name),int(k.args[1].name))!=value for k in keys):
            return T('SCase',(selector,T('list',(T('pair',(T('None'),default(a[1]))),)))),'apply specialize_default. vm_compute. reflexivity.'
    if n=='SSeq':
        pairs=[specialize(child,selector,value)for child in a[0].args]
        changed=any(new!=old for old,(new,_)in zip(a[0].args,pairs))
        if changed:
            steps=['apply specialize_seq.']
            for _,proof in pairs:steps+=['constructor.','{ '+proof+' }']
            steps+=['constructor.']
            return T('SSeq',(T('list',tuple(new for new,_ in pairs)),)),'\n'.join(steps)
    if n=='SIf':
        y,py=specialize(a[1],selector,value);no,pn=specialize(a[2],selector,value)
        if(y,no)!=(a[1],a[2]):return T('SIf',(a[0],y,no)),'apply specialize_if.\n{ '+py+' }\n{ '+pn+' }'
    return st,'apply specialize_same.'


def discover(ast):
    data=origin.pending.analyze(ast);slots={s['carrier']for s in data['slots']}
    frontier={int(n.args[1].name)for s in data['slots']
        for n in origin.pending.data_leaves(origin.pending.rtl.Parser(s['capture']['next_expression']).complete())
        if n.name=='EVar'}-slots
    rows=[]
    for source in sorted(frontier):
        chain=aliases.trace(ast,source);terminal=chain['terminal']
        writers=[p for p in ast['processes']if terminal in p['writers']]
        if len(writers)!=1 or writers[0]['kind']!='Combinational':continue
        proc=writers[0]
        for node in origin.pending.rtl.walk(proc['body']):
            if node.name!='SCase':continue
            selector,arms=node.args
            if selector.name!='ESel'or selector.args[1].name!='EVar'or selector.args[1].args[0].name!='32':continue
            width=int(selector.args[0].name);input_root=int(selector.args[1].args[1].name)
            if not 1<=width<=4 or input_root in proc['writers']:continue
            if selector.args[2].name!='EConst'or selector.args[2].args[1].name!='0':continue
            chosen=default(arms)
            copies=[n for n in origin.pending.rtl.walk(chosen)if n.name=='SAssign'and n.args[0].name=='false'
                and n.args[2].name=='LVar'and n.args[2].args[0].name=='32'and origin.pending.rtl.root_of(n.args[2])==terminal
                and n.args[1]==origin.pending.rtl.Term('EVar',(origin.pending.rtl.Term('32'),origin.pending.rtl.Term(str(input_root))))]
            if not copies:continue
            keys=[key.args[0]for key,_ in (a.args for a in arms.args)if key.name=='Some']
            if any(k.name!='EConst'for k in keys):continue
            values={tracker.norm(int(k.args[0].name),int(k.args[1].name))for k in keys}
            for value in range(1<<width):
                if value in values:continue
                specialized,proof=specialize(proc['body'],selector,value)
                if specialized==proc['body']:continue
                rows.append(dict(source=source,terminal=terminal,input_root=input_root,process=proc['name'],
                    selector=origin.pending.rtl.render(selector),value=value,selector_width=width,
                    specialized=origin.pending.rtl.render(specialized),proof=proof,
                    alias_chain=chain,domain_reachability_proved=False))
    if len(rows)>32:raise ValueError('case-domain budget exceeded; no truncation')
    return rows


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);rows=discover(ast)
    if not rows:raise ValueError('no supported default-copy input case')
    program=profile['ast']['program'];r=origin.pending.rtl.render
    alias_roots=sorted({e['root']for row in rows for e in row['alias_chain']['edges']})
    if alias_roots:
        _,ca,prefix=comb.proposal(profile,alias_roots)
        if ca['residuals']:raise ValueError('actual alias residual: '+json.dumps(ca['residuals']))
        ports={p['output_root']:i for i,p in enumerate(ca['ports'])}
        audit_count=len(ca['ports'])
    else:
        prefix=f'Require Import Lang.ExtendedSV {ast_module}.\nImport ExtendedSV.\nDefinition actual_combs := filter is_comb(processes {program}).\n'
        ports={};audit_count=0
    combs=[p for p in ast['processes']if p['kind']=='Combinational']
    lines=['From Coq Require Import List ZArith Bool Lia.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVBlocking Lang.ExtendedSVRootProjection',
        ' Lang.ExtendedSVCombCut Lang.ExtendedSVConstantRoot',
        ' Lang.ExtendedSVExprAgreement Lang.ExtendedSVAssignment Lang.ExtendedSVWordInvariant',
        ' Lang.ExtendedSVCaseSpecialization Lang.ExtendedSVInstructionOrigin '+ast_module+'.',
        'Import ListNotations ExtendedSV ExtendedSVBlocking ExtendedSVRootProjection',
        ' ExtendedSVCombCut ExtendedSVConstantRoot',
        ' ExtendedSVExprAgreement ExtendedSVAssignment ExtendedSVWordInvariant ExtendedSVCaseSpecialization ExtendedSVInstructionOrigin.',
        'Local Opaque read_signal write_signal norm.']
    for i,row in enumerate(rows):
        name='case_'+str(i);proc=ast['module']+'.'+row['process'];src=row['input_root'];out=row['terminal'];value=row['value']
        lines += [f'Definition {name}_selector : Expr := {row["selector"]}.',
            f'Definition {name}_specialized : Stmt := {row["specialized"]}.',
            f'Lemma {name}_checked : Specializes {name}_selector {value}%Z',
            f' (process_body {proc}) {name}_specialized.',
            f'Proof. unfold {name}_selector,{name}_specialized,{proc};cbn[process_body].',row['proof'],'Qed.',
            f'Lemma {name}_source_frame : ~In {src}%nat(stmt_writers(process_body {proc})).',
            'Proof. vm_compute. intuition discriminate. Qed.',
            f'Lemma {name}_unwritten : SelectorUnwritten {name}_selector(process_body {proc}).',
            f'Proof. intros width root HI. cbn[{name}_selector expr_inputs]in HI.',
            f' destruct HI as[HE|[]];inversion HE;subst. exact {name}_source_frame. Qed.',
            f'Lemma {name}_blocking : blocking_onlyb(process_body {proc})=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem {name}_actual_process_copy s : eval_expr s {name}_selector={value}%Z ->',
            f' norm 32(read_signal(run_process {program} s {proc}) {out})=',
            f' norm 32(read_signal s {src}).',
            f'Proof. intro HD. rewrite(blocking_run_process {program} {proc} s {name}_blocking).',
            f' rewrite(specializes_exec {name}_selector {value}%Z (statement_fuel {program})',
            f' (process_body {proc}) {name}_specialized',
            f' {{|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}} {name}_checked {name}_unwritten HD).',
            f' change(norm 32(read_signal(blocking_state(exec_stmt {ast["statement_fuel"]} {name}_specialized',
            f' {{|blocking_state:=s;pending_nba:=[];emitted_updates:=[]|}})) {out})=norm 32(read_signal s {src})).',
            f' cbn[{name}_specialized exec_stmt select_case_stmt fold_left blocking_state pending_nba',
            ' eval_expr apply_update resolve_update resolve_lvalue update_signal update_offset update_width update_value].',
            ' unfold apply_update; cbn[update_signal update_offset update_width update_value].',
            ' repeat first[rewrite read_signal_write_same|rewrite read_signal_write_other by discriminate',
            ' |rewrite norm_full_low_write|rewrite norm_idempotent]. reflexivity. Qed.',
            f'Print Assumptions {name}_actual_process_copy.']
        index=next(j for j,p in enumerate(combs)if p['name']==row['process'])
        lines += [f'Definition {name}_prefix := firstn {index}%nat actual_combs.',
            f'Definition {name}_suffix := skipn {index+1}%nat actual_combs.',
            f'Lemma {name}_registered : nth_error actual_combs {index}%nat=Some {proc}.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_output_frame : roots_unwrittenb {out}%nat(skipn {index+1}%nat actual_combs)=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_input_frame : roots_unwrittenb {src}%nat(firstn {index}%nat actual_combs) ||',
            f' roots_unwrittenb {src}%nat({proc}::skipn {index+1}%nat actual_combs)=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_selector_source : Forall(fun input=>snd input={src}%nat)(expr_inputs {name}_selector).',
            'Proof. repeat constructor. Qed.',
            f'Lemma {name}_selector_word : Forall(fun input=>input=(32%nat,{src}%nat))(expr_inputs {name}_selector).',
            'Proof. repeat constructor. Qed.',
            f'Local Opaque {program}.',
            f'Theorem {name}_actual_lfp_copy seed fixed : CombLFP {program} seed fixed ->',
            f' eval_expr fixed {name}_selector={value}%Z ->',
            f' norm 32(read_signal fixed {out})=norm 32(read_signal fixed {src}).',
            f'Proof. refine(indexed_conditional_copy_at_lfp {program} actual_combs {index}%nat {proc}',
            f' {out} {src} {name}_selector {value}%Z seed fixed _ _ _ _ _ _).',
            ' - unfold actual_combs. exact eq_refl.',
            f' - exact {name}_registered.',
            f' - exact {name}_output_frame.',
            f' - exact {name}_input_frame.',
            f' - exact {name}_selector_source.',
            f' - exact {name}_actual_process_copy. Qed.',
            f'Print Assumptions {name}_actual_lfp_copy.',
            f'Theorem {name}_frontier_word seed fixed : CombLFP {program} seed fixed ->',
            f' eval_expr fixed {name}_selector={value}%Z ->',
            f' norm 32(read_signal fixed {row["source"]})=norm 32(read_signal fixed {src}).',
            'Proof. intros HL HD.']
        term=f'({name}_actual_lfp_copy seed fixed HL HD)'
        for edge in reversed(row['alias_chain']['edges']):
            j=ports[edge['root']]
            term=f'(eq_trans (eq_trans (port_{j}_lfp seed fixed HL) (norm_idempotent 32 (read_signal fixed {edge["parent"]}%nat))) {term})'
        lines += [f' exact {term}. Qed.',f'Print Assumptions {name}_frontier_word.',
            f'Theorem {name}_frontier_origin (Label:Type)(word:Label->Z) seed fixed labels (label:Label) :',
            f' CombLFP {program} seed fixed ->OriginsAgree word fixed labels ->labels {src}=Some label ->',
            f' eval_expr(write_signal [] {src}(word label)){name}_selector={value}%Z ->',
            f' norm 32(read_signal fixed {row["source"]})=norm 32(word label).',
            'Proof. intros HL HA HT HD.',
            f' assert(HW:norm 32(read_signal fixed {src})=norm 32(word label))by(exact(HA {src} label HT)).',
            f' rewrite({name}_frontier_word seed fixed HL',
            f' (selector_domain_from_word {name}_selector {src}(word label)fixed {value}%Z {name}_selector_word HW HD)). exact HW. Qed.',
            f'Print Assumptions {name}_frontier_origin.']
        lines += [f'Local Transparent {program}.']
        audit_count+=4
    source=prefix+'\n'+'\n'.join(lines)+'\n'
    return dict(ast_sha256=ast['source_sha256'],raw_program=program,candidates=rows,
        coq_load_paths=paths,old_inv_read=False,audited_exports=audit_count,
        source_sha256=hashlib.sha256(source.encode()).hexdigest()),source


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'CaseInputs.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(origin.pending.rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedCaseInputs']
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='conditional default-copy actual process and LFP frontier-origin proof',coqc_exit=c.returncode,
        coqc_timed_out=t,old_inv_read=False,domain_reachability_proved=False,itree_refinement_proved=False)
    report.update(source_sha256=data['source_sha256'],ast_sha256=data['ast_sha256'])
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and 'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaseInputs.CaseInputs'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();result=check(a.ast,a.ast_module,a.output);print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
