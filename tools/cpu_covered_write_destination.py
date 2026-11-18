"""Use endogenous valid-token coverage to prove actual guarded write addresses.

The witness is obtained from the actual field history, not supplied by the
caller. ISA retirement order, value correctness and reset remain obligations.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_write_destination_history as history
import cpu_capture_chain_coverage as coverage
import cpu_single_bank_branch as single
from cpu_certificate_acceptance import run_stage


def render(ast,profile,target,covered,branch,ports,validity=None,boot_connected=False):
    rows=covered['coverage']['covered_fields'];valid=next(r['valid_root']for r in rows if r['root']==target['endpoint'])
    chain=history.chain.discover(ast,set(target['roots']))
    n=next(i for i,r in enumerate(chain['rows'])if r['root']==target['endpoint'])
    root=target['endpoint'];src=target['head']['source'];p=profile['ast']['program'];br=branch['bank']
    idx=branch['index_root'];sample=f'(phase_driven_state {p} ev pre)'
    value=f'(norm 32(eval_expr {sample} {branch["data"]}))'
    guards=[f'Z.eqb(eval_expr {sample} {g})0={str(not t).lower()}'for g,t in branch['guards']]
    lines=['From Coq Require Import List ZArith Lia.',f'Require Import {profile["ast"]["module"]}.',
        'Require Import GeneratedCoveredCapture.CoveredCapture GeneratedISADestinations.ISADestinations',
        ' GeneratedBank.AutoBank Lang.ExtendedSV Lang.ExtendedSVScalarExpression',
        ' Lang.ExtendedSVScalarHistory Lang.ExtendedSVRootProjection Lang.ExtendedSVRegisterBank',
        ' Ex.External.CPUInstructionFields Lang.ExtendedSVWordInvariant Lang.ExtendedSVCaptureBirth.',
        'Import ListNotations ExtendedSV ExtendedSVScalarExpression ExtendedSVScalarHistory',
        ' ExtendedSVRootProjection ExtendedSVRegisterBank CPUInstructionFields ExtendedSVWordInvariant.',
        'Import ExtendedSVCaptureBirth.',
        single.render(ast,branch),
        'Lemma captured_head_rd code:norm 5(C.chain_head_value code)=field_reference code Rd.',
        'Proof.',f'change(norm 5(norm 5(eval_expr(write_signal [] {src} code)(field_expr {src} Rd)))=field_reference code Rd).',
        f'exact(eq_trans(norm_idempotent 5(eval_expr(write_signal [] {src} code)(field_expr {src} Rd)))',
        f' (eq_trans(native_field_reference(write_signal [] {src} code){src} Rd)',
        f' (f_equal(fun v=>field_reference v Rd)(read_signal_write_same [] {src} code)))). Qed.']
    if ports:lines+=['Require Import GeneratedScalarComb.ScalarCombBindings.']
    lines += [f'Lemma sampled_endpoint seed ev pre:changed_signal ev<>{root}%nat ->',
        f'CombLFP {p} seed {sample} ->norm 5(read_signal {sample}{idx})=norm 5(read_signal pre {root}).',
        'Proof. intros HE HL.']
    for alias in target['aliases']:
        i=ports[alias]
        lines += [f'rewrite(GeneratedScalarComb.ScalarCombBindings.port_{i}_lfp seed _ HL).',
                  f'unfold GeneratedScalarComb.ScalarCombBindings.port_{i}_rhs;cbn[eval_expr];rewrite norm_idempotent.']
    lines += [f'exact(f_equal (norm 5)(sampled_root_preserved {p} ev pre {root}%nat',
              f' (history_comb_frame _ _ _ _ _ C.root_{root}_projection_certificate) HE)). Qed.']
    proc=ast['module']+'.'+branch['process']
    assumptions=['CoveredCapturedFields pre packed ->',f'norm 1(read_signal pre {valid})<>0%Z ->',
        f'changed_signal ev<>{root}%nat ->',f'CombLFP {p} seed {sample} ->',
        f'process_matches_states pre {sample} {proc}=true ->',*[g+' ->'for g in guards]]
    conclusion=[f'exists token,C.chain_tag{n}(snd packed)=Some token /\\',
        'forall instruction address rest,',
        'Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction instruction ->',
        'destination_registers instruction=address::rest ->',
        f'bank_phase_operations {branch["total"]} pre {sample} bank_{br}_entries=[WriteLane address {value}].']
    names=' '.join(f'HG{i}'for i in range(len(guards)))
    lines += ['Theorem valid_actual_write_destination seed ev pre packed:',*assumptions,*conclusion,
        'Proof. intros HR HV HE HL HP '+names+'.',
        f'destruct(valid_field_{n}_has_value pre packed HR HV)as[token[HT HF]].',
        'exists token;split;[exact HT|]. intros instruction address rest HD HS.',
        f'apply(selected_bank_write pre {sample} address HP {names}).',
        'rewrite(sampled_endpoint seed ev pre HE HL),HF,captured_head_rd.',
        'exact(eq_sym(original_destination_address(token_word token)instruction address rest HD HS)). Qed.',
        'Theorem history_valid_actual_write_destination initial initial_tags events pre packed seed ev:',
        'CoveredExecution initial initial_tags events pre packed ->CoveredCapturedFields initial initial_tags ->',
        *assumptions[1:],*conclusion,
        'Proof. intros HX HI HV HE HL HP '+names+'.',
        'exact(valid_actual_write_destination seed ev pre packed',
        ' (covered_capture_history initial initial_tags events pre packed HX HI) HV HE HL HP '+names+'). Qed.',
        'Print Assumptions captured_head_rd. Print Assumptions sampled_endpoint.',
        'Print Assumptions valid_actual_write_destination. Print Assumptions history_valid_actual_write_destination.']
    if validity is not None:
        if not validity.get('entry'):raise ValueError('write validity entry must be proved, not supplied')
        end=validity['rows'][-1]
        if end['rd']!=root or end['valid']!=valid:raise ValueError('coverage and write validity endpoints differ')
        matches=[i for i,(guard,taken) in enumerate(branch['guards'])if guard==validity['write_guard'] and taken]
        if len(matches)!=1:raise ValueError('actual bank guard does not match checked write validity')
        roots=sorted({row[k]for row in validity['rows']for k in ['rd','write','valid']}|
                     {validity['entry']['capture']['carrier'],validity['entry']['capture']['valid_root']})
        boundary='HB'
        for _ in range(roots.index(root)):boundary=f'(proj2 {boundary})'
        if roots.index(root)!=len(roots)-1:boundary=f'(proj1 {boundary})'
        lines += ['Require Import GeneratedWriteValidity.WriteValidity.',
            'Module WV:=GeneratedWriteValidity.WriteValidity.',
            'Theorem actual_write_destination_from_relation seed ev pre packed:',
            'CoveredCapturedFields pre packed ->WV.WriteValidityInvariant pre ->WV.Boundary ev ->',
            *assumptions[3:],*conclusion,
            'Proof. intros HR HI HB HL HP '+names+'.',
            f'pose proof(WV.actual_write_branch_valid seed ev pre HB HL HI HG{matches[0]})as HV.',
            f'exact(valid_actual_write_destination seed ev pre packed HR HV {boundary} HL HP {names}). Qed.',
            'Print Assumptions actual_write_destination_from_relation.']
        if boot_connected:
            lines += ['Require Import GeneratedCapturedHistoryBoot.CapturedHistoryBoot',
                ' Lang.ExtendedSVEmptyPipeline Lang.ExtendedSVBootstrap Lang.ExtendedSVBoundedCatalogPhase.',
                'Module HB:=GeneratedCapturedHistoryBoot.CapturedHistoryBoot.',
                'Theorem actual_write_destination_from_boot image events ev:',
                f'let pre:=phase_run {p} events(HB.F.boot image) in',
                'let packed:=HB.boot_history image events in',
                'Forall HB.W.Environment events ->HB.W.Environment ev ->',
                *assumptions[4:],*conclusion,
                'Proof. intros pre packed HE HEv HP '+names+'.',
                'destruct(HB.boot_and_runtime_related image events HE)as[HR HI].',
                f'assert(HA:Forall(ExtendedSVBoundedCatalogPhase.CatalogEvent {p} Catalog.actual_catalog)events).',
                '{ eapply Forall_impl;[|exact HE];intros event H;exact(proj1 H). }',
                f'pose proof(ExtendedSVEmptyPipeline.catalog_shape_history {p} Catalog.actual_catalog Phase.actual_certificate events HA (HB.F.boot image)(proj1(HB.B.boot_runtime image)))as HS.',
                f'destruct(ExtendedSVBootstrap.catalog_phase_evidence {p} Catalog.actual_catalog Phase.actual_certificate ev pre (proj1 HEv) HS)as[HL _].',
                f'exact(actual_write_destination_from_relation _ ev pre packed HR HI (proj2(HB.W.environment_protects_fields ev HEv)) HL HP {names}). Qed.',
                'Print Assumptions actual_write_destination_from_boot.']
    elif boot_connected:
        raise ValueError('boot connection requires checked write validity')
    return '\n'.join(lines)+'\n'


def check(ast_path,ast_module,isa_provider,coverage_provider,output,validity_provider=None,history_boot_provider=None):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=history.chain.p.origins.raw_binding(ast_path,ast_module);profile['coq_load_paths']=paths
    targets,residuals=history.discover(ast)
    if len(targets)!=1:raise ValueError('one structurally selected Rd history required')
    target=targets[0];idx=target['aliases'][0]if target['aliases']else target['endpoint']
    branches=single.discover(ast,idx)
    if len(branches)!=1:raise ValueError('one complete single-write branch required')
    expected,data=coverage.render(ast_path,ast_module,set(target['roots']))
    provider=Path(coverage_provider);rp=json.loads((provider/'report.json').read_text())
    if not(rp.get('accepted')is True and rp.get('coqc_exit')==rp.get('coqchk_exit')==0
        and rp.get('export_assumptions_closed')is True
        and (provider/'CoveredCapture.v').read_text()==expected
        and rp.get('source_sha256')==hashlib.sha256(expected.encode()).hexdigest()
        and (provider/'CoveredCapture.vo').is_file()):raise ValueError('coverage provider differs from raw reconstruction')
    isa_provider=Path(isa_provider);ir=json.loads((isa_provider/'report.json').read_text())
    original=history.isa.render((history.isa.synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text())
    if not(ir.get('accepted')is True and ir.get('original_assumptions_only')is True
        and ir.get('coqc_exit')==ir.get('coqchk_exit')==0
        and (isa_provider/'ISADestinations.v').read_text()==original
        and (isa_provider/'ISADestinations.vo').is_file()):raise ValueError('ISA provider mismatch')
    report=dict(accepted=False,complete_R_generated=False,isa_retirement_identity_proved=False,
                initialization_proved=False,old_inv_read=False,targets=targets)
    validity=None
    if validity_provider is not None:
        import cpu_write_validity_chain
        validity_provider=Path(validity_provider)
        vs,validity=cpu_write_validity_chain.render(ast_path,ast_module)
        vr=json.loads((validity_provider/'report.json').read_text())
        if not(vr.get('accepted')is True and vr.get('entry_relation_proved')is True
            and vr.get('coqc_exit')==vr.get('coqchk_exit')==0 and vr.get('assumptions_closed')is True
            and vr.get('ast_sha256')==ast['source_sha256']
            and vr.get('source_sha256')==hashlib.sha256(vs.encode()).hexdigest()
            and (validity_provider/'WriteValidity.v').read_text()==vs
            and (validity_provider/'WriteValidity.vo').is_file()):
            raise ValueError('write validity provider differs from raw reconstruction')
    boot_paths=[]
    if history_boot_provider is not None:
        if validity is None:raise ValueError('boot connection requires checked write validity')
        import cpu_captured_history_boot as hb
        hp=Path(history_boot_provider);hr=json.loads((hp/'report.json').read_text());hd=json.loads((hp/'plan.json').read_text())
        boot_paths=hd['paths'];bn={b['namespace']:Path(b['directory']) for b in boot_paths}
        env=json.loads((bn['GeneratedSeedBoot']/'plan.json').read_text())['environment']
        hs=hb.render(profile['ast']['program'],ast_module,validity,env)
        if not(hr.get('accepted')is True and hr.get('coqc_exit')==hr.get('coqchk_exit')==0
            and hr.get('assumptions_closed')is True and hd['ast_sha256']==ast['source_sha256']
            and hd['program']==profile['ast']['program'] and (hp/'CapturedHistoryBoot.v').read_text()==hs
            and hr['source_sha256']==hashlib.sha256(hs.encode()).hexdigest()
            and bn['GeneratedCoveredCapture'].resolve()==provider.resolve()
            and bn['GeneratedWriteValidity'].resolve()==validity_provider.resolve()):
            raise ValueError('history bootstrap does not match actual checked relations')
        for file,sha in env['input_hashes'].items():
            if hb.boot.digest(file)!=sha:raise ValueError('original environment data changed')
    bank=history.index.ownership.bank.check_profile(profile,out/'bank');report['bank']=bank
    ports={}
    if target['aliases']:
        alias=history.chain.rf.comb.check_profile(profile,out/'aliases',target['aliases']);report['aliases']=alias
        if alias.get('accepted')is not True:raise ValueError('alias certificate failed')
        ports={r['output_root']:i for i,r in enumerate(alias['outputs'])}
    if bank.get('accepted')is not True:raise ValueError('bank certificate failed')
    source=render(ast,profile,target,data,branches[0],ports,validity,history_boot_provider is not None);file=out/'CoveredDestination.v';file.write_text(source)
    flags=list(history.index.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    for folder,ns in [(out,'GeneratedCoveredDestination'),(provider,'GeneratedCoveredCapture'),
        (isa_provider,'GeneratedISADestinations'),(out/'bank','GeneratedBank')]:
        flags+=['-R',str(folder.resolve()),ns]
    if ports:flags+=['-R',str((out/'aliases').resolve()),'GeneratedScalarComb']
    if validity_provider is not None:flags+=['-R',str(validity_provider.resolve()),'GeneratedWriteValidity']
    for b in boot_paths:
        if b['namespace'] not in ['GeneratedRuntimeInput','GeneratedCoveredCapture','GeneratedWriteValidity']:
            flags+=['-R',b['directory'],b['namespace']]
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(history.index.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()<deadline:
        closed=c.stdout.count('Closed under the global context')==(7 if history_boot_provider is not None else 6 if validity else 5) and 'Axioms:'not in c.stdout
        k,t=run_stage([str(history.index.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedCoveredDestination.CoveredDestination'],out/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,accepted=closed and k.returncode==0)
    report['separate_terminal_validity_assumption_removed']=validity is not None and report['accepted']
    report['history_and_validity_derived_from_boot']=history_boot_provider is not None and report['accepted']
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for arg in ['ast','ast-module','isa-provider','coverage-provider','output']:p.add_argument('--'+arg,required=True)
    p.add_argument('--validity-provider')
    p.add_argument('--history-boot-provider')
    a=p.parse_args();r=check(a.ast,a.ast_module,a.isa_provider,a.coverage_provider,a.output,a.validity_provider,a.history_boot_provider)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
