"""Consume a new default-copy origin proof in a real carrier phase.

Both providers must be current generated raw-RTL artifacts, never a previous
CPU invariant. Upstream birth/age/validity and actual LFP reachability remain
explicit obligations rather than being declared true by this consumer.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_case_inputs as cases
import cpu_pending_origins as origins
from cpu_certificate_acceptance import run_stage


def verify_case_provider(cp,case_data,case_source):
    cp=Path(cp)
    report=json.loads((cp/'report.json').read_text())
    if not(report.get('accepted')is True and report.get('coqc_exit')==report.get('coqchk_exit')==0
        and report.get('assumptions_closed')is True and report.get('old_inv_read')is False
        and report.get('domain_reachability_proved')is False
        and report.get('global_inv_proved',False)is False
        and report.get('itree_refinement_proved')is False
        and (cp/'CaseInputs.v').read_text()==case_source
        and json.loads((cp/'plan.json').read_text())==case_data
        and report.get('source_sha256')==hashlib.sha256(case_source.encode()).hexdigest()
        and report.get('object_sha256')==hashlib.sha256((cp/'CaseInputs.vo').read_bytes()).hexdigest()):
        raise ValueError('exact checked generated case provider required')
    return report


def render(ast_path,ast_module,case_provider,phase_provider):
    cp=Path(case_provider);pp=Path(phase_provider)
    case_data,case_source=cases.render(ast_path,ast_module)
    pr=origins.verify(ast_path,ast_module,pp)
    report=verify_case_provider(cp,case_data,case_source)
    ast,profile,paths=origins.raw_binding(ast_path,ast_module);analysis=origins.pending.analyze(ast)
    connections=[]
    for index,row in enumerate(case_data['candidates']):
        for slot in analysis['slots']:
            expression=origins.pending.rtl.Parser(slot['capture']['next_expression']).complete()
            sources={int(n.args[1].name)for n in origins.pending.data_leaves(expression)if n.name=='EVar'and n.args[0].name=='32'}
            if row['source']in sources:connections.append(dict(index=index,case=row,slot=slot))
    if not connections:raise ValueError('no actual case-to-carrier connection')
    program=profile['ast']['program'];count=0
    lines=['From Coq Require Import ZArith List Bool.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVOriginFrame',
        ' Lang.ExtendedSVScalarExpression GeneratedCaseInputs.CaseInputs GeneratedOrigins.Origins.',
        f'Require Import {ast_module}.',
        'Import ListNotations ExtendedSV ExtendedSVInstructionOrigin ExtendedSVOriginFrame ExtendedSVScalarExpression.',
        'Module C := GeneratedCaseInputs.CaseInputs.',
        'Module P := GeneratedOrigins.Origins.',
        f'Local Opaque {program}.']
    for i,item in enumerate(connections):
        r=item['case'];root=item['slot']['carrier'];src=r['source'];up=r['input_root'];n='connection_'+str(i);case='C.case_'+str(item['index'])
        lines += [f'Definition {n}_input_origin (Label:Type)(word:Label->Z)(incoming:option Label) :=',
            f' match incoming with None=>None|Some label=>if Z.eqb',
            f' (eval_expr(write_signal [] {up}(word label)){case}_selector){r["value"]}%Z then Some label else None end.',
            f'Lemma {n}_input_known (Label:Type)(word:Label->Z) seed fixed incoming :',
            f' CombLFP {program} seed fixed ->KnownAt word fixed {up} incoming ->',
            f' KnownAt word fixed {src}({n}_input_origin Label word incoming).',
            'Proof. intros HL HK label HT.',
            f' unfold {n}_input_origin in HT. destruct incoming as[l|];[|discriminate].',
            f' destruct(Z.eqb(eval_expr(write_signal [] {up}(word l)){case}_selector){r["value"]}%Z)eqn:HD;[|discriminate].',
            ' inversion HT;subst l. apply Z.eqb_eq in HD.',
            f' pose proof(HK label eq_refl)as HW.',
            f' rewrite({case}_frontier_word seed fixed HL',
            f' (ExtendedSVCaseSpecialization.ExtendedSVCaseSpecialization.selector_domain_from_word',
            f' {case}_selector {up}(word label)fixed {r["value"]}%Z {case}_selector_word HW HD)). exact HW. Qed.',
            f'Definition {n}_sampled (Label:Type)(word:Label->Z)(old incoming:option Label) :=',
            f' origin_pair {root} {src} old({n}_input_origin Label word incoming).',
            f'Definition {n}_actual_phase (Label:Type)(word:Label->Z) ev pre old incoming :=',
            f' @P.root_{root}_origin_step Label ev pre old({n}_sampled Label word old incoming).',
            f'Theorem {n}_actual_phase_known (Label:Type)(word:Label->Z) seed ev pre old incoming :',
            f' changed_signal ev<>{root}%nat ->KnownAt word pre {root} old ->',
            f' CombLFP {program} seed(phase_driven_state {program} ev pre) ->',
            f' KnownAt word(phase_driven_state {program} ev pre){up} incoming ->',
            f' KnownAt word(PhaseSemantics {program} ev pre){root}',
            f' ({n}_actual_phase Label word ev pre old incoming).',
            'Proof. intros HE Hold HL Hinput label HT.',
            f' eapply(@P.root_{root}_actual_origin_phase Label word ev pre old',
            f' ({n}_sampled Label word old incoming)label);[exact HE|exact Hold| |exact HT].',
            f' unfold {n}_sampled. apply origin_pair_known.',
            f' - intros l Hl. rewrite(sampled_root_preserved {program} ev pre {root} P.root_{root}_comb_frame HE). exact(Hold l Hl).',
            f' - exact({n}_input_known Label word seed(phase_driven_state {program} ev pre)incoming HL Hinput). Qed.',
            f'Print Assumptions {n}_input_known.',f'Print Assumptions {n}_actual_phase_known.']
        count+=2
    source='\n'.join(lines)+'\n'
    return dict(ast_sha256=ast['source_sha256'],coq_load_paths=paths,connections=connections,
        phase_provider=pr,case_object_sha256=report['object_sha256'],audited_exports=count,
        old_inv_read=False,source_sha256=hashlib.sha256(source.encode()).hexdigest()),source


def check(ast_path,ast_module,case_provider,phase_provider,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    data,source=render(ast_path,ast_module,case_provider,phase_provider)
    output=Path(output);output.mkdir(parents=True,exist_ok=False);path=output/'Consumer.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(origins.pending.rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(Path(case_provider).resolve()),'GeneratedCaseInputs','-R',str(Path(phase_provider).resolve()),'GeneratedOrigins',
        '-R',str(output.resolve()),'GeneratedCaseConsumer']
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='actual phase consuming new input-origin rule only',coqc_exit=c.returncode,
        coqc_timed_out=t,old_inv_read=False,source_sha256=data['source_sha256'],
        upstream_birth_proved=False,validity_coverage_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and 'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
                '-norec','GeneratedCaseInputs.CaseInputs','-norec','GeneratedOrigins.Origins',
                '-norec','GeneratedCaseConsumer.Consumer'],output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--case-provider',type=Path,required=True)
    p.add_argument('--phase-provider',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.case_provider,a.phase_provider,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
