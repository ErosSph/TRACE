"""Prove pipeline tags belong to the actual capture log, not ISA order."""
import argparse,json,hashlib,time
from pathlib import Path
import cpu_captured_history_boot as hb
from cpu_certificate_acceptance import run_stage

def render(program,chain,module='Raw.AST'):
    n=len(chain['rows']);edges={e['target']:e['source'] for e in chain['edges']}
    if n==0:raise ValueError('empty field chain')
    clauses=['Recorded(history(fst packed))(current(fst packed))']+[
        f'Recorded(history(fst packed))(C.C.chain_tag{i}(snd packed))' for i in range(n)]
    lines=['From Coq Require Import List ZArith.',f'Require Import {module}.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVScalarHistory Lang.ExtendedSVCaptureBirth',
        ' Lang.ExtendedSVCaptureProvenance Lang.ExtendedSVRuntimeHistory',
        ' GeneratedCapturedHistoryBoot.CapturedHistoryBoot.',
        'Import ListNotations ExtendedSV ExtendedSVScalarHistory ExtendedSVCaptureBirth ExtendedSVCaptureProvenance.',
        'Module H:=GeneratedCapturedHistoryBoot.CapturedHistoryBoot. Module C:=H.C.',
        f'Local Opaque {program} PhaseSemantics.',
        'Definition RecordedFields(packed:C.Packed):Prop:='+' /\\ '.join(clauses)+'.',
        'Lemma recorded_step ev pre packed unused:RecordedFields packed ->RecordedFields(C.advance_capture_fields ev pre packed unused).',
        'Proof. destruct packed as[g tags];unfold RecordedFields;cbn[fst snd].',
        'intros [HG '+''.join(f'[H{i} 'for i in range(n-1))+f'H{n-1}'+']'*n+'.',
        'cbn[C.advance_capture_fields fst snd C.C.advance_tags '+ ' '.join(f'C.C.chain_tag{i}'for i in range(n))+'].',
        'split;[apply ghost_recorded;exact HG|].']
    for i in range(n):
        incoming=f'H{edges[i]}'if i in edges else 'HG'
        proof=f'eapply recorded_extend;[apply ghost_history_extends|];unfold C.C.projection_{i}_origin;apply projection_recorded;[exact H{i}|exact {incoming}]'
        lines += [proof+'.'if i==n-1 else 'split;['+proof+'|].']
    lines += ['Qed.',
        'Lemma empty_recorded:RecordedFields H.empty.',
        'Proof. unfold RecordedFields,H.empty;cbn;repeat split;intros token HT;discriminate. Qed.',
        'Theorem recorded_replay events:forall pre packed,RecordedFields packed ->RecordedFields(H.history events pre packed).',
        'Proof. induction events as[|ev rest IH];intros pre packed HR;[exact HR|].',
        'unfold H.history;cbn[ExtendedSVRuntimeHistory.replay];apply IH;apply recorded_step;exact HR. Qed.',
        'Theorem boot_recorded image events:RecordedFields(H.boot_history image events).',
        'Proof. apply recorded_replay;exact empty_recorded. Qed.',
        'Theorem boot_token_id_unique image events:',
        'Forall H.W.Environment events ->forall a b,',
        'In a(history(fst(H.boot_history image events))) ->',
        'In b(history(fst(H.boot_history image events))) ->token_id a=token_id b ->a=b.',
        'Proof. intro HE;destruct(H.boot_and_runtime_related image events HE)as[[[HI HC]HV]HW].',
        'apply token_id_identifies;exact(proj2(proj2(proj2 HI))). Qed.',
        'Print Assumptions recorded_step. Print Assumptions boot_recorded. Print Assumptions boot_token_id_unique.']
    return '\n'.join(lines)+'\n'

def check(ast,module,history_provider,output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False);hp=Path(history_provider)
    plan=json.loads((hp/'plan.json').read_text());report=json.loads((hp/'report.json').read_text())
    raw,profile,_=hb.boot.chain.origin.raw_binding(ast,module)
    paths=plan['paths'];ns={r['namespace']:Path(r['directory']) for r in paths}
    env=json.loads((ns['GeneratedSeedBoot']/'plan.json').read_text())['environment']
    _,data=hb.boot.chain.render(ast,module)
    expected=hb.render(profile['ast']['program'],module,data,env)
    if not(report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
        and report.get('assumptions_closed')is True and plan['ast_sha256']==raw['source_sha256']
        and (hp/'CapturedHistoryBoot.v').read_text()==expected
        and report['source_sha256']==hashlib.sha256(expected.encode()).hexdigest()):
        raise ValueError('history provider differs from raw reconstruction')
    for file,sha in env['input_hashes'].items():
        if hb.boot.digest(file)!=sha:raise ValueError('environment data changed')
    chain=hb.coverage.capture.discover(raw,{r['rd'] for r in data['rows']})['chain']
    source=render(profile['ast']['program'],chain,module);file=out/'CaptureProvenance.v';file.write_text(source)
    flags=list(hb.boot.chain.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedCaptureProvenance']
    start=time.monotonic();c,t=run_stage([str(hb.boot.chain.origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    result=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,complete_R_generated=False,
        isa_retirement_identity_proved=False,old_inv_read=False,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()-start<1200:
        closed=c.stdout.count('Closed under the global context')==3 and 'Axioms:'not in c.stdout
        k,t=run_stage([str(hb.boot.chain.origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaptureProvenance.CaptureProvenance'],out/'coqchk.log',1200-(time.monotonic()-start))
        result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    result['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history-provider','output']:parser.add_argument('--'+key,required=True)
    a=parser.parse_args();result=check(a.ast,a.ast_module,a.history_provider,a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
