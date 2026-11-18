"""Raw RTL -> actual capture labels and replay invariant, with no supplied labels.

Tokens describe observed valid captures, not yet ISA admissions. Optional PC
values are sampled candidates; ISA/environment correspondence stays open.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_validity as validity
import cpu_pending_recipe_coverage as requires
import cpu_pending_fetch_pairs as fetch
from cpu_certificate_acceptance import run_stage

origin=validity.origins;rtl=origin.pending.rtl


def birth_match(word,valid,root,validroot):
    if validity.is_const(valid,1,0):return 'apply BirthInvalid.'
    if validity.is_var(word,32,root):
        proof=requires.requires(valid,validroot)
        return None if proof is None else'apply BirthHold.\n'+proof
    if validity.is_var(word,32):return 'apply BirthFresh;intro H;discriminate.'
    if word.name==valid.name=='ECond'and word.args[0].name=='32'and valid.args[0].name=='1'and word.args[1]==valid.args[1]:
        yes=birth_match(word.args[2],valid.args[2],root,validroot);no=birth_match(word.args[3],valid.args[3],root,validroot)
        if yes is not None and no is not None:return 'apply BirthSelect.\n'+yes+'\n'+no
    return None


def discover(ast):
    data=validity.discover(ast);pcs=fetch.discover(ast);rows=[];residuals=list(data['residuals'])
    for row in data['pairs']:
        root=row['carrier'];v=row['valid_root']
        proof=birth_match(rtl.Parser(row['word_expression']).complete(),rtl.Parser(row['valid_expression']).complete(),root,v)
        if proof is None:
            residuals.append(dict(root=root,reason='no complete birth/hold/drop shape certificate'));continue
        pc=[p for p in pcs['pairs']if p['carrier']==root]
        initial_writers=[p['name']for p in ast['processes']if p['kind']=='Initial'and v in p['writers']]
        rows.append(dict(**row,birth_proof=proof,pc_candidates=pc,initial_validity_writers=initial_writers))
    return dict(captures=rows,residuals=residuals,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        external_origin_labels_required=False,capture_is_not_yet_isa_admission=True,
        original_runtime_initialization_proved=False,pc_correspondence_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module):
    ast,profile,loadpaths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if not data['captures']:raise ValueError('no supported word/valid capture; no fake admission or empty queue')
    roots=sorted({r for row in data['captures']for r in(row['carrier'],row['valid_root'])})
    _,remaining,outputs,source,count=origin.expressions.proposal(profile,roots)
    if remaining:raise ValueError('actual capture scalar residual')
    program=profile['ast']['program'];lines=[
        'Require Import Lang.ExtendedSVCaptureBirth Lang.ExtendedSVScalarHistory Lang.ExtendedSVRootProjection',
        ' Lang.ExtendedSVConstantRoot Lang.ExtendedSVRecipeCoverage Lang.ExtendedSVCoveredField.',
        'Import ExtendedSVCaptureBirth ExtendedSVScalarHistory ExtendedSVRootProjection ExtendedSVConstantRoot',
        ' ExtendedSVRecipeCoverage ExtendedSVCoveredField.']
    for out in outputs:
        r=out['root'];w=out['width'];proc=ast['module']+'.'+out['process']
        lines += [f'Lemma root_{r}_birth_self:self_widthb {w} {r} root_{r}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition root_{r}_birth_certificate:ScalarCertificate {program} {r} {w} {proc} root_{r}_expression:=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{r}_comb_frame root_{r}_birth_self root_{r}_expression_phase.']
    for index,row in enumerate(data['captures']):
        stem=f'capture_{index}';root=row['carrier'];v=row['valid_root'];proc=ast['module']+'.'+row['process']
        if not row['initial_validity_writers']:
            lines += [f'Lemma {stem}_initial_unwritten:roots_unwrittenb {v}(filter is_initial(processes {program}))=true.',
                'Proof. vm_compute. reflexivity. Qed.']
        lines += [f'Definition {stem}_pc(s:State)(source:signal):option Z:=']
        for pc in row['pc_candidates']:
            lines += [f' if Nat.eqb source {pc["word_input"]} then Some(norm 32(read_signal s {pc["address_root"]}))else']
        lines += [' None.',
            f'Lemma {stem}_checked:BirthMatches {root} {v} root_{root}_expression root_{v}_expression.',
            f'Proof. unfold root_{root}_expression,root_{v}_expression. {row["birth_proof"]} Qed.',
            f'Definition {stem}_step ev pre g:=ghost_step {program} {proc} {root}',
            f' root_{root}_expression root_{v}_expression {stem}_pc ev pre g.',
            f'Definition {stem}_run events pre g:=replay {program} {proc} {root}',
            f' root_{root}_expression root_{v}_expression {stem}_pc events pre g.',
            f'Theorem {stem}_phase ev pre g:changed_signal ev<>{root}%nat ->changed_signal ev<>{v}%nat ->',
            f' Invariant {root} {v} pre g ->Invariant {root} {v}(PhaseSemantics {program} ev pre)({stem}_step ev pre g).',
            f'Proof. exact(ghost_step_invariant {program} {root} {v} {proc} root_{root}_expression root_{v}_expression',
            f' root_{root}_birth_certificate root_{v}_birth_certificate {stem}_checked {stem}_pc ev pre g). Qed.',
            f'Theorem {stem}_replay events:Forall(fun ev=>changed_signal ev<>{root}%nat /\\changed_signal ev<>{v}%nat)events ->',
            f' forall pre g,Invariant {root} {v} pre g ->Invariant {root} {v}(fst({stem}_run events pre g))(snd({stem}_run events pre g)).',
            f'Proof. exact(replay_invariant {program} {root} {v} {proc} root_{root}_expression root_{v}_expression',
            f' root_{root}_birth_certificate root_{v}_birth_certificate {stem}_checked {stem}_pc events). Qed.',
            f'Theorem {stem}_erases events pre g:fst({stem}_run events pre g)=phase_run {program} events pre.',
            f'Proof. exact(replay_erases {program} {proc} {root} root_{root}_expression root_{v}_expression {stem}_pc events pre g). Qed.']
        audits=['checked','phase','replay','erases']
        if not row['initial_validity_writers']:
            lines += [f'Theorem {stem}_initialize seed:norm 1(read_signal seed {v})=0%Z ->',
                f' Invariant {root} {v}(initialize {program} seed)(Build_Ghost 0 None []).',
                'Proof. intro HV;apply empty_initial_invariant.',
                f' rewrite(initialize_unwritten_field {program} {v} {stem}_initial_unwritten seed). exact HV. Qed.',
                f'Corollary {stem}_zero_seed:Invariant {root} {v}(initialize {program} [])(Build_Ghost 0 None []).',
                f'Proof. apply {stem}_initialize;reflexivity. Qed.']
            audits+=['initialize','zero_seed']
        for suffix in audits:lines.append(f'Print Assumptions {stem}_{suffix}.');count+=1
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=loadpaths,audited_exports=count),source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,old_pending_read=False,
            global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'CaptureBirth.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedCaptureBirth'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual valid-capture labels and arbitrary finite phase replay invariant',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        ast_sha256=data['ast_sha256'],capture_count=len(data['captures']),old_inv_read=False,old_pending_read=False,
        external_origin_labels_required=False,capture_is_not_yet_isa_admission=True,
        original_runtime_initialization_proved=False,pc_correspondence_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaptureBirth.CaptureBirth'],
                output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
