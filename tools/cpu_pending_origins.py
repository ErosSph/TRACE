"""Generate actual-phase instruction-origin transport from raw RTL alone.

Admission labels are ghost data, not guessed hardware PCs. A missing label
means unknown and must never be filtered away as an empty physical slot.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_pending_from_rtl as pending
import cpu_scalar_expressions as expressions
import cpu_scalar_histories as histories
import cpu_scalar_captures as captures
from cpu_certificate_acceptance import run_stage

ROOT=pending.rtl.ROOT


def raw_binding(ast_path,ast_module):
    path=Path(ast_path).resolve()
    if not pending.rtl.SYMBOL.fullmatch(ast_module):raise ValueError('closed AST import required')
    ast=pending.rtl.load_ast(path)
    programs=re.findall(r'Definition\s+(\w+)\s*:\s*Program\s*:=',path.read_text())
    if len(programs)!=1:raise ValueError('unique raw Program required')
    profile={'ast':{'file':str(path),'module':ast_module,'program':ast['module']+'.'+programs[0]}}
    paths=[]
    if not path.is_relative_to(ROOT/'src'):
        paths=[dict(directory=str(path.parent),namespace=ast_module.rsplit('.',1)[0])]
    return ast,profile,paths


def render(ast_path,ast_module):
    ast,profile,paths=raw_binding(ast_path,ast_module)
    data=pending.analyze(ast);selected=[s['carrier']for s in data['slots']]
    if not selected:raise ValueError('no supported carrier; no empty-origin fallback')
    _,residuals,outputs,source,count=expressions.proposal(profile,selected)
    if residuals:raise ValueError('actual expression residual: '+json.dumps(residuals))
    for row in outputs:
        if row['width']!=32 or not histories.self_width_supported(row['expression'],row['root'],32):
            raise ValueError('full-word normalized self-feedback required')
    program=profile['ast']['program']
    lines=['Require Import Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant.',
        'Import ExtendedSVInstructionOrigin ExtendedSVScalarHistory ExtendedSVWordInvariant.',
        'Section GeneratedInstructionOrigins.',
        'Context {Label:Type}. Variable instruction_word:Label->Z.']
    audits=[]
    for row in outputs:
        r=row['root'];proc=ast['module']+'.'+row['process'];stem='root_'+str(r)
        lines += [f'Lemma {stem}_origin_self_width : self_widthb 32 {r} {stem}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {stem}_origin_certificate : ScalarCertificate {program} {r} 32 {proc} {stem}_expression :=',
            f' Build_ScalarCertificate _ _ _ _ _ {stem}_comb_frame {stem}_origin_self_width {stem}_expression_phase.',
            f'Definition {stem}_origin_step ev pre (old:option Label) (sampled:signal->option Label) :=',
            f' @phase_origin Label {program} {proc} {stem}_expression ev pre old sampled.',
            f'Theorem {stem}_actual_copy_route s source :',
            f' copy_source s {stem}_expression=Some source ->',
            f' norm 32(read_signal(run_process {program} s {proc}) {r})=',
            ' norm 32(read_signal s source).',
            f'Proof. intro H. rewrite ({stem}_expression_process s).',
            f' rewrite (copy_source_sound {stem}_expression s source H). apply norm_idempotent. Qed.',
            f'Theorem {stem}_actual_origin_phase ev pre old sampled label :',
            f' changed_signal ev<>{r}%nat ->',
            f' (forall l,old=Some l->norm 32(read_signal pre {r})=norm 32(instruction_word l)) ->',
            f' OriginsAgree instruction_word (phase_driven_state {program} ev pre) sampled ->',
            f' {stem}_origin_step ev pre old sampled=Some label ->',
            f' norm 32(read_signal(PhaseSemantics {program} ev pre) {r})=norm 32(instruction_word label).',
            f'Proof. exact (@actual_phase_origin Label instruction_word {program} {r} {proc}',
            f' {stem}_expression {stem}_origin_certificate ev pre old sampled label). Qed.']
        for suffix in ['actual_copy_route','actual_origin_phase']:
            audits += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
                f'Print Assumptions {stem}_{suffix}.']
            count+=1
    lines+=['End GeneratedInstructionOrigins.',*audits]
    source+='\n'+'\n'.join(lines)+'\n'
    return dict(ast_sha256=ast['source_sha256'],raw_program=program,carriers=selected,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),audited_exports=count,
        coq_load_paths=paths,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        origin_map_none_means_unknown=True,original_pc_pairing_guessed=False),source


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200s')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    data,source=render(ast_path,ast_module)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    path=output/'Origins.v';path.write_text(source)
    flags=list(pending.rtl.framework.FLAGS)
    for binding in data['coq_load_paths']:flags+=['-R',binding['directory'],binding['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedOrigins']
    report=dict(accepted=False,scope='raw-RTL instruction-origin copy and real phase transport only',
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        source_sha256=data['source_sha256'],ast_sha256=data['ast_sha256'],carriers=data['carriers'],
        llm_calls=0,queue_correspondence_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        closed=captures.audit_output(c.stdout,data['audited_exports']);report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedOrigins.Origins'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


def verify(ast_path,ast_module,folder):
    """Revalidate an existing LOCAL origin artifact, never promote it to INV."""
    folder=Path(folder);data,source=render(ast_path,ast_module)
    report=json.loads((folder/'report.json').read_text())
    object_path=folder/'Origins.vo'
    if not (report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
        and report.get('assumptions_closed')is True
        and report.get('old_inv_read')is False and report.get('old_cpu_proofs_used')is False
        and report.get('queue_correspondence_proved')is False
        and report.get('global_inv_proved')is False and report.get('itree_refinement_proved')is False
        and json.loads((folder/'plan.json').read_text())==data
        and (folder/'Origins.v').read_text()==source
        and report.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
        and report.get('object_sha256')==hashlib.sha256(object_path.read_bytes()).hexdigest()):
        raise ValueError('exact current raw-RTL local origin proof required; never accept a partial or promoted INV claim')
    return dict(accepted=True,scope='verified local instruction-origin phase proof only',
        source_sha256=report['source_sha256'],object_sha256=report['object_sha256'],
        global_inv_proved=False,itree_refinement_proved=False)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args();r=verify(a.ast,a.ast_module,a.output)if a.verify_only else check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
