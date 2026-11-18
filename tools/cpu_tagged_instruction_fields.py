"""Checked six-bit bank-tag/register-field adapters; never truncate the tag.

A plain RV32 index is emitted only when the real combinational tag chain is
proved zero. Nonzero, sequential or computed tag sources are residuals.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_auto_adapter as adapter
import cpu_comb_scalar_bindings as comb
import cpu_instruction_fields as fields
import cpu_instruction_word_aliases as words
import cpu_rf_read_ports as ports
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def tagged_leaf(e):
    if e.name!='EConcat' or e.args[0].name!='6':return None
    tag,low=e.args[1:]
    if tag.name not in {'EVar','EConst'} or tag.args[0].name!='1':return None
    field=fields.match_field(low,5)
    if not field or field['shape']!='native' or field['field'] not in {'Rd','Rs1','Rs2'}:return None
    return dict(field=field['field'],source=field['source'],tag=tag)


def trace_zero(ast,tag,budget=256):
    result=[];seen=set()
    if tag.name=='EConst':
        if int(tag.args[1].name)%2:raise ValueError('nonzero constant bank tag')
        return result
    current=int(tag.args[1].name)
    for _ in range(budget):
        if current in seen:raise ValueError('bank tag alias cycle')
        seen.add(current)
        writers=[p for p in ast['processes'] if current in p['writers']]
        if len(writers)!=1 or writers[0]['kind']!='Combinational':
            raise ValueError('bank tag needs a unique combinational source')
        try:assignments=ports.flatten_blocking(writers[0]['body'])
        except ValueError:
            assignments=[n for n in adapter.walk(writers[0]['body']) if n.name=='SAssign' and adapter.root_of(n.args[2])==current]
            if not assignments or not all(n.args[0].name=='false' and n.args[2].name=='LVar' and
                n.args[2].args[0].name=='1' and n.args[1].name=='EConst' and
                n.args[1].args[0].name=='1' and int(n.args[1].args[1].name)%2==0 for n in assignments):
                raise ValueError('branching bank tag has no constant-zero projection template') from None
            rhs=assignments[-1].args[1]
            result.append(dict(root=current,parent=None,mode='sliced_constant',
                process=writers[0]['name'],constant=adapter.render(rhs)))
            return result
        st=[s for s in assignments if int(s.args[2].args[1].name)==current][-1]
        rhs=st.args[1]
        if st.args[2].args[0].name!='1' or rhs.name not in {'EVar','EConst'} or rhs.args[0].name!='1':
            raise ValueError('bank tag source is not a one-bit copy/constant')
        if rhs.name=='EConst':
            if int(rhs.args[1].name)%2:raise ValueError('nonzero constant bank tag')
            result.append(dict(root=current,parent=None));return result
        parent=int(rhs.args[1].name)
        result.append(dict(root=current,parent=parent));current=parent
    raise ValueError('bank tag depth budget exhausted')


def output_slice(statement,root,fuel=512):
    T=adapter.Term
    if fuel==0 or not any(n.name=='SAssign' and adapter.root_of(n.args[2])==root for n in adapter.walk(statement)):
        return T('SSkip')
    n,a=statement.name,statement.args
    if n in {'SSkip','SAssign'}:return statement
    if n=='SSeq':return T(n,(T('list',tuple(output_slice(s,root,fuel-1) for s in a[0].args)),))
    if n=='SIf':return T(n,(a[0],output_slice(a[1],root,fuel-1),output_slice(a[2],root,fuel-1)))
    if n=='SCase':return T(n,(a[0],T('list',tuple(T('pair',(arm.args[0],output_slice(arm.args[1],root,fuel-1))) for arm in a[1].args))))
    raise ValueError('unknown blocking statement')


def proposal(profile, opaque_program_connection=False):
    ast=adapter.load_ast(adapter.ROOT/profile['ast']['file'])
    outputs=[];residuals=[];deferred=[]
    for proc in ast['processes']:
        if proc['kind']!='Combinational':continue
        try:assignments=ports.flatten_blocking(proc['body'])
        except ValueError:
            for st in adapter.walk(proc['body']):
                if st.name=='SAssign' and st.args[2].name=='LVar' and tagged_leaf(st.args[1]):
                    deferred.append(dict(root=int(st.args[2].args[1].name),process=proc['name'],
                        reason='statement-level choice needs path-sensitive tagged contract'))
            continue
        for st in assignments:
            if st.name!='SAssign' or st.args[0].name!='false' or st.args[2].name!='LVar' or st.args[2].args[0].name!='6':continue
            match=tagged_leaf(st.args[1])
            if match:
                root=int(st.args[2].args[1].name)
                try:
                    zero=trace_zero(ast,match['tag']);origin=words.trace(ast,match['source'])
                    outputs.append(dict(root=root,zero=zero,origin=origin,**match))
                except ValueError as exc:residuals.append(dict(root=root,reason=str(exc)))
    constants={n['root']:n for o in outputs for n in o['zero'] if n.get('mode')=='sliced_constant'}
    roots=sorted({o['root'] for o in outputs}|
        {n['root'] for o in outputs for n in o['zero'] if n['root'] not in constants}|
        {n['root'] for o in outputs for n in o['origin']['edges']})
    if not roots:return ast,residuals,outputs,'',0,deferred
    _,analysis,source=comb.proposal(profile,roots);residuals+=analysis['residuals']
    source=re.sub(r'RF_PORT_ASSUMPTIONS_(\d+)',lambda m:'AUTO_ADAPTER_ASSUMPTIONS_'+m.group(1),source)
    count=source.count('Print Assumptions ')
    port_for={o['output_root']:i for i,o in enumerate(analysis['ports'])}
    if not set(roots)<=set(port_for):return ast,residuals,outputs,source,count,deferred
    lines=['Require Import Ex.External.CPUInstructionFields Ex.External.CPUInstructionTaggedFields Ex.External.CPUInstructionFieldAlias',
        ' Lang.ExtendedSVWordInvariant Lang.ExtendedSVConstantOutputBinding Lang.ExtendedSVOutputSlice',
        ' Lang.ExtendedSVBlocking Lang.ExtendedSVConstantRoot Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut',
        ' Lang.ExtendedSVSlicedProcessBinding Lang.ExtendedSVIndexedConstantBinding.',
        'Import CPUInstructionFields CPUInstructionTaggedFields CPUInstructionFieldAlias ExtendedSVWordInvariant',
        ' ExtendedSVConstantOutputBinding ExtendedSVOutputSlice ExtendedSVBlocking ExtendedSVConstantRoot ExtendedSVCombConnection ExtendedSVCombCut',
        ' ExtendedSVSlicedProcessBinding ExtendedSVIndexedConstantBinding.']
    program=profile['ast']['program'];audits=[]
    zero_nodes={node['root']:node['parent'] for o in outputs for node in o['zero']};done=set()
    def emit_zero(root):
        nonlocal lines
        if root in done:return
        parent=zero_nodes[root]
        if parent is not None:emit_zero(parent)
        index=port_for.get(root)
        if root in constants:
            node=constants[root];proc=next(p for p in ast['processes'] if p['name']==node['process'])
            combinations=[p for p in ast['processes'] if p['kind']=='Combinational']
            position=combinations.index(proc);actual=ast['module']+'.'+node['process'];rhs=node['constant']
            sliced=adapter.render(output_slice(proc['body'],root))
            fuel=ast.get('statement_fuel')
            if fuel is None:
                # AST parser preserves the declared runtime statement budget.
                raise ValueError('tagged constant binding requires actual statement fuel')
            lines += [f'Definition root_{root}_slice : Stmt := {sliced}.',
                f'Definition root_{root}_scalar : Process := {{|process_kind:=Combinational;process_events:=[];',
                f' process_body:=SAssign false {rhs} (LVar 1 {root}%nat);process_source_line:=0|}}.',
                f'Lemma root_{root}_slice_checked : output_slice(statement_fuel {program})[{root}%nat]',
                f' (process_body {actual})=root_{root}_slice.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Lemma root_{root}_safe : output_slice_safeb(statement_fuel {program})[{root}%nat][{root}%nat]',
                f' (process_body {actual})=true.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Lemma root_{root}_blocking : blocking_onlyb(process_body {actual})=true.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Lemma root_{root}_slice_blocking : blocking_onlyb(process_body(sliced_process {program}[{root}%nat]{actual}))=true.',
                'Proof. vm_compute. reflexivity. Qed.',
                'Local Opaque eval_expr apply_update.',
                f'Lemma root_{root}_slice_exec es : exec_stmt {fuel}%nat root_{root}_slice es=',
                f' exec_stmt {fuel}%nat (process_body root_{root}_scalar) es.',
                'Proof. reflexivity. Qed.',
                f'Lemma root_{root}_single s : run_process {program} s(sliced_process {program}[{root}%nat]{actual})=',
                f' run_process {program} s root_{root}_scalar.',
                f'Proof. exact(sliced_process_run_equivalent {program} [{root}%nat] {actual}',
                f' root_{root}_scalar root_{root}_slice {fuel}%nat eq_refl root_{root}_slice_checked root_{root}_slice_exec s). Qed.',
                'Local Transparent eval_expr apply_update.',
                f'Lemma root_{root}_process_zero s : norm 1(read_signal(run_process {program} s {actual}){root}%nat)=0%Z.',
                f'Proof. exact(checked_sliced_constant {program} {actual} root_{root}_scalar 1%nat {root}%nat',
                f' {rhs} 0%Z root_{root}_safe root_{root}_blocking root_{root}_slice_blocking root_{root}_single',
                ' eq_refl ltac:(cbn;lia) (fun _=>eq_refl) s). Qed.',
                f'Lemma root_{root}_registered : nth_error actual_combs {position}%nat=Some {actual}.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Lemma root_{root}_suffix : roots_unwrittenb {root}%nat(skipn {position+1} actual_combs)=true.',
                'Proof. vm_compute. reflexivity. Qed.',
                *([f'Local Opaque {program}.'] if opaque_program_connection else []),
                f'Lemma root_{root}_tag_zero seed fixed : CombLFP {program} seed fixed ->norm 1(read_signal fixed {root}%nat)=0%Z.',
                f'Proof. exact(indexed_lfp_constant {program} actual_combs {position}%nat {actual}',
                f' {root}%nat (norm 1) 0%Z eq_refl root_{root}_registered root_{root}_suffix',
                f' root_{root}_process_zero seed fixed). Qed.',
                *([f'Local Transparent {program}.'] if opaque_program_connection else [])]
            audits.append(f'root_{root}_tag_zero');done.add(root);return
        lines += [f'Lemma root_{root}_tag_zero seed fixed : CombLFP {program} seed fixed ->',
            f' norm 1 (read_signal fixed {root}%nat)=0%Z.',
            'Proof. intro HL.']
        if parent is None:
            lines += [f' exact (port_{index}_lfp seed fixed HL). Qed.']
        else:
            lines += [f' exact (eq_trans (port_{index}_lfp seed fixed HL)',
                f'  (eq_trans (norm_idempotent 1 (read_signal fixed {parent}%nat))',
                f'   (root_{parent}_tag_zero seed fixed HL))). Qed.']
        audits.append(f'root_{root}_tag_zero');done.add(root)
    for root in zero_nodes:emit_zero(root)
    origin_done=set()
    for o in outputs:
        origin=o['origin'];source_root=o['source'];terminal=origin['terminal']
        if source_root not in origin_done:
            term='eq_refl'
            for edge in reversed(origin['edges']):
                i=port_for[edge['root']];parent=edge['parent']
                term=f'(eq_trans (port_{i}_lfp seed fixed HL) (eq_trans (norm_idempotent 32 (read_signal fixed {parent}%nat)) {term}))'
            lines += [f'Lemma source_{source_root}_origin seed fixed : CombLFP {program} seed fixed ->',
                f' norm 32(read_signal fixed {source_root}%nat)=norm 32(read_signal fixed {terminal}%nat).',
                f'Proof. intro HL. exact {term}. Qed.']
            audits.append(f'source_{source_root}_origin');origin_done.add(source_root)
        root,field,tag=o['root'],o['field'],adapter.render(o['tag']);i=port_for[root]
        tag_zero='eq_refl' if o['tag'].name=='EConst' else f'(root_{o["tag"].args[1].name}_tag_zero seed fixed HL)'
        lines += [f'Definition root_{root}_tag : Expr := {tag}.',
            f'Lemma root_{root}_full_layout s : norm 6(eval_expr s port_{i}_rhs)=',
            f' norm 6(Z.lor(Z.shiftl(eval_expr s root_{root}_tag)5)',
            f' (field_reference(read_signal s {source_root}%nat){field})).',
            f'Proof. exact (tagged_register_field_reference s {source_root}%nat {field} root_{root}_tag eq_refl). Qed.',
            f'Lemma root_{root}_plain_layout s : eval_expr s root_{root}_tag=0%Z ->',
            f' norm 6(eval_expr s port_{i}_rhs)=field_reference(read_signal s {source_root}%nat){field}.',
            f'Proof. exact (zero_tag_register_field_reference s {source_root}%nat {field} root_{root}_tag eq_refl). Qed.',
            f'Theorem root_{root}_actual_full seed fixed : CombLFP {program} seed fixed ->',
            f' norm 6(read_signal fixed {root}%nat)=norm 6(Z.lor(Z.shiftl(eval_expr fixed root_{root}_tag)5)',
            f' (field_reference(read_signal fixed {source_root}%nat){field})).',
            f'Proof. intro HL. exact(eq_trans(port_{i}_lfp seed fixed HL)(root_{root}_full_layout fixed)). Qed.',
            f'Theorem root_{root}_actual_plain seed fixed : CombLFP {program} seed fixed ->',
            f' norm 6(read_signal fixed {root}%nat)=field_reference(read_signal fixed {source_root}%nat){field}.',
            f'Proof. intro HL. exact(eq_trans(port_{i}_lfp seed fixed HL)(root_{root}_plain_layout fixed {tag_zero})). Qed.',
            f'Theorem root_{root}_actual_carrier seed fixed : CombLFP {program} seed fixed ->',
            f' norm 6(read_signal fixed {root}%nat)=field_reference(read_signal fixed {terminal}%nat){field}.',
            f'Proof. intro HL. exact(eq_trans(root_{root}_actual_plain seed fixed HL)',
            f' (field_reference_alias _ _ {field}(source_{source_root}_origin seed fixed HL))). Qed.']
        audits += [f'root_{root}_{suffix}' for suffix in ['full_layout','plain_layout','actual_full','actual_plain','actual_carrier']]
    for name in audits:
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',f'Print Assumptions {name}.'];count+=1
    return ast,residuals,outputs,source+'\n'.join(lines)+'\n',count,deferred


def emit_library(profile,destination,check=False):
    """Persist exact generated source, without claiming it has been checked."""
    _,residuals,outputs,source,count,deferred=proposal(profile)
    if residuals or not outputs:
        raise ValueError('unsupported or empty tagged instruction field selection')
    path=Path(destination)
    if check:
        if not path.is_file() or path.read_text()!=source:
            raise ValueError('persistent tagged instruction source differs from generation')
    elif path.exists():
        raise ValueError('destination exists; use --check-source')
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
    return dict(source=str(path),source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        fields=len(outputs),audited_exports=count,source_matches_generator=True,coq_checked=False,
        all_tagged_candidates_covered=not bool(deferred),deferred_candidates=deferred,
        current_isa_token_identity_proved=False,global_invariant_synthesized=False)


def check_profile(profile,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,residuals,outputs,source,count,deferred=proposal(profile)
    report=dict(accepted=False,status='unverified',ast_sha256=ast['source_sha256'],
        actual_program=profile['ast']['program'],outputs=[{**o,'tag':adapter.render(o['tag'])} for o in outputs],
        residuals=residuals,audited_exports=count,llm_calls=0,tag_truncated=False,
        deferred_candidates=deferred,all_tagged_candidates_covered=not bool(deferred),
        coverage_scope='unconditional straight-line tagged extraction; not arbitrary statement-level choices',
        current_isa_token_identity_proved=False,global_invariant_synthesized=False)
    if residuals:report['status']='unproved_tag_or_binding'
    elif not outputs and deferred:report.update(status='unproved_guarded_tagged_candidates',coq_checked=False)
    elif not outputs:report.update(accepted=True,status='not_applicable',coq_checked=False)
    else:
        file=output/'TaggedFields.v';file.write_text(source)
        report['source_sha256']=hashlib.sha256(source.encode()).hexdigest()
        flags=list(adapter.framework.FLAGS)
        for extra in profile.get('coq_load_paths',[]):flags+=['-R',extra['directory'],extra['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedTaggedFields']
        start=time.monotonic()
        c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-q','-time',*flags,str(file.resolve())],output/'coqc.log',timeout)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
        if c.returncode==0:
            report['assumptions_closed']=scalar.audit_output(c.stdout,count)
            start=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedTaggedFields.TaggedFields'],output/'coqchk.log',timeout)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
            report['accepted']=report['assumptions_closed'] and k.returncode==0
            report['coq_checked']=report['accepted']
            if report['accepted']:report['status']='checked_full_width_tagged_fields'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--profile',type=Path,required=True);p.add_argument('--output',type=Path)
    p.add_argument('--emit-source',type=Path);p.add_argument('--check-source',action='store_true')
    p.add_argument('--timeout',type=float,default=1200);a=p.parse_args()
    if not 0<a.timeout<=1200:p.error('timeout must be positive and at most1200 seconds')
    if bool(a.output)==bool(a.emit_source):p.error('choose exactly one of --output and --emit-source')
    if a.check_source and not a.emit_source:p.error('--check-source requires --emit-source')
    profile=json.loads(a.profile.read_text())
    if a.emit_source:
        print(json.dumps(emit_library(profile,a.emit_source,a.check_source),indent=2));return 0
    r=check_profile(profile,a.output,a.timeout)
    print(json.dumps(r,indent=2));return 0 if r['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
