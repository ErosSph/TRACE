"""Prove invalid captures have a zero ISA field, including nonzero NOPs."""
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_pending_capture_birth as birth
import cpu_capture_chain_coverage as coverage
import cpu_write_destination_history as history
from cpu_certificate_acceptance import run_stage
rtl=birth.rtl


def proof(word,valid,root,validroot,field='Rd'):
    literal=rtl.render
    # A known live slot imposes no restriction on its payload.
    if valid.name=='EConst' and valid.args[0].name=='1' and int(valid.args[1].name)%2==1:
        return 'intro H;vm_compute in H;discriminate.'
    if word.name=='EConst' and valid.name=='EConst' and valid.args[0].name=='1':
        value=int(word.args[1].name)%(1<<int(word.args[0].name))
        offset={'Rd':7,'Rs1':15,'Rs2':20}[field]
        if (value>>offset)&31:return None
        return 'intro H;vm_compute;reflexivity.'
    if birth.validity.is_var(word,32,root) and birth.validity.is_var(valid,1,validroot):
        return 'cbn[eval_expr];rewrite !norm_idempotent;exact HI.'
    if word.name==valid.name=='ECond' and word.args[0].name=='32' and valid.args[0].name=='1' and word.args[1]==valid.args[1]:
        yes=proof(word.args[2],valid.args[2],root,validroot,field)
        no=proof(word.args[3],valid.args[3],root,validroot,field)
        if yes is None or no is None:return None
        args=' '.join(literal(x)for x in [word.args[1],word.args[2],word.args[3],valid.args[2],valid.args[3]])
        return f'apply(choice_zero 32 (fun code=>field_reference code {field}) {args} s).\n{{ '+yes+' }\n{ '+no+' }'
    return None


def check(ast_path,ast_module,provider,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=birth.origin.raw_binding(ast_path,ast_module)
    targets,_=history.discover(ast)
    if len(targets)!=1:raise ValueError('unique destination chain required')
    expected,data=coverage.render(ast_path,ast_module,set(targets[0]['roots']))
    provider=Path(provider);rp=json.loads((provider/'report.json').read_text())
    if not(rp.get('accepted')is True and rp.get('coqc_exit')==rp.get('coqchk_exit')==0 and rp.get('export_assumptions_closed')is True
        and rp.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
        and(provider/'CoveredCapture.v').read_text()==expected and(provider/'CoveredCapture.vo').is_file()):raise ValueError('coverage provider mismatch')
    connection=coverage.capture.discover(ast,set(targets[0]['roots']))['connection']
    if connection is None:raise ValueError('original capture connection required')
    row=connection['capture'];root=row['carrier'];valid=row['valid_root'];p=profile['ast']['program'];proc=ast['module']+'.'+row['process']
    word=rtl.Parser(row['word_expression']).complete();bit=rtl.Parser(row['valid_expression']).complete()
    script=proof(word,bit,root,valid)
    report=dict(accepted=False,root=root,valid=valid,complete_R_generated=False,old_inv_read=False,
                full_pipeline_invalid_projection_proved=False,initialization_proved=False)
    if script is None:
        report['status']='unsupported_paired_expression'
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    lines=['From Coq Require Import List ZArith.',f'Require Import {ast_module}.',
        'Require Import GeneratedCoveredCapture.CoveredCapture Ex.External.CPUInstructionFields',
        ' Lang.ExtendedSV Lang.ExtendedSVInvalidProjection Lang.ExtendedSVWordInvariant',
        ' Lang.ExtendedSVScalarHistory Lang.ExtendedSVScalarExpression.',
        'Import ExtendedSV ExtendedSVScalarHistory ExtendedSVScalarExpression ExtendedSVInvalidProjection ExtendedSVWordInvariant CPUInstructionFields.',
        f'Local Opaque {p}.',
        f'Definition InvalidRd s:=Related 32 {root} {valid}(fun code=>field_reference code Rd)s.',
        f'Lemma capture_local s:InvalidRd s ->norm 1(eval_expr s B.root_{valid}_expression)=0%Z ->',
        f'field_reference(norm 32(eval_expr s B.root_{root}_expression))Rd=0%Z.',
        f'Proof. intro HI;unfold B.root_{root}_expression,B.root_{valid}_expression. '+script+' Qed.',
        f'Theorem capture_phase ev pre:changed_signal ev<>{root}%nat ->changed_signal ev<>{valid}%nat ->',
        f'InvalidRd pre ->InvalidRd(PhaseSemantics {p} ev pre).',
        f'Proof. exact(phase_preserves {p} 32 {root} {valid} {proc} B.root_{root}_expression B.root_{valid}_expression',
        f' (fun code=>field_reference code Rd) B.root_{root}_birth_certificate B.root_{valid}_birth_certificate capture_local ev pre). Qed.',
        'Theorem capture_history events:',f'Forall(fun ev=>changed_signal ev<>{root}%nat /\\changed_signal ev<>{valid}%nat)events ->',
        f'forall pre,InvalidRd pre ->InvalidRd(ExtendedSVScalarHistory.phase_run {p} events pre).',
        f'Proof. exact(history_preserves {p} 32 {root} {valid} {proc} B.root_{root}_expression B.root_{valid}_expression',
        f' (fun code=>field_reference code Rd) B.root_{root}_birth_certificate B.root_{valid}_birth_certificate capture_local events). Qed.',
        'Print Assumptions capture_local. Print Assumptions capture_phase. Print Assumptions capture_history.']
    exports=3
    if (word.name==bit.name=='ECond' and word.args[1]==bit.args[1]
        and word.args[3].name=='EConst' and birth.validity.is_const(bit.args[3],1,0)
        and proof(word.args[3],bit.args[3],root,valid) is not None):
        sample=f'(phase_driven_state {p} ev pre)';guard=rtl.render(word.args[1])
        lines += ['Theorem reset_branch_establishes ev pre:',
            f'changed_signal ev<>{root}%nat ->changed_signal ev<>{valid}%nat ->',
            f'process_matches_states pre {sample} {proc}=true ->',
            f'Z.eqb(eval_expr {sample} {guard})0=true ->InvalidRd(PhaseSemantics {p} ev pre).',
            'Proof. intros HE HV HT HG;unfold InvalidRd,Related.',
            f'rewrite(history_phase_projection _ _ _ _ _ B.root_{valid}_birth_certificate ev pre HV).',
            f'rewrite(history_phase_projection _ _ _ _ _ B.root_{root}_birth_certificate ev pre HE),HT.',
            f'unfold B.root_{root}_expression,B.root_{valid}_expression;',
            'cbn[eval_expr]in HG|-*;rewrite HG;intro H;vm_compute;reflexivity. Qed.',
            'Print Assumptions reset_branch_establishes.']
        exports+=1
    source='\n'.join(lines)+'\n';file=out/'InvalidCapture.v';file.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(provider.resolve()),'GeneratedCoveredCapture','-R',str(out.resolve()),'GeneratedInvalidCapture']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()<deadline:
        closed=c.stdout.count('Closed under the global context')==exports and'Axioms:'not in c.stdout
        k,t=run_stage([str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedInvalidCapture.InvalidCapture'],out/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
        report['conditional_reset_projection_proved']=exports==4 and closed and k.returncode==0
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','coverage-provider','output']:p.add_argument('--'+arg,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.coverage_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
