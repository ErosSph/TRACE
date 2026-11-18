"""Compile checked rule selection against an actual imported Program.

Default mode proves the accepted subset and a conditional ordered certificate.
--prove-ordered also requires the complete real ordered check to succeed. A
multi-round design is never silently replaced by a fuel-1 variant.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import time
import cpu_auto_adapter as adapter
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage, SYMBOL


def proposal(profile, prove_ordered=False):
    if type(prove_ordered) is not bool:
        raise ValueError('prove_ordered must be boolean')
    p=profile['ast']['program']
    extra=profile['ast'].get('program_imports',[])
    if not isinstance(extra,list):raise ValueError('program_imports must be a list of symbols')
    imports=[profile['ast']['module'],*extra]
    if not all(isinstance(s,str)and SYMBOL.fullmatch(s)for s in [p,*imports]):
        raise ValueError('program and imports must be Coq symbols, not source text')
    ast=adapter.load_ast(adapter.ROOT/profile['ast']['file'])
    lines=['From Coq Require Import List Bool PeanoNat.',
      'Require Import Lang.ExtendedSV Lang.ExtendedSVCombIdempotence',
      ' Lang.ExtendedSVCombRuleRegistry Ex.External.CPUCombRuleCatalog',
      ' '+' '.join(imports)+'.',
      'Import ListNotations ExtendedSV ExtendedSVCombIdempotence ExtendedSVCombRuleRegistry CPUCombRuleCatalog.',
      f'Definition actual_order := filter is_comb(processes {p}).',
      'Definition checked_order := certified_order producer_rules actual_order.',
      'Definition unresolved_order := residual_order producer_rules actual_order.',
      f'Lemma actual_fuel_check : Nat.ltb 0(statement_fuel {p})=true.',
      'Proof. vm_compute. reflexivity. Qed.',
      f'Lemma actual_fuel_positive : (0<statement_fuel {p})%nat.',
      f'Proof. exact(proj1(Nat.ltb_lt 0(statement_fuel {p}))actual_fuel_check). Qed.']
    for marker,expression in [('TOTAL','length actual_order'),('ACCEPTED','length checked_order'),
                              ('RESIDUAL','length unresolved_order'),('LFP_FUEL',f'lfp_fuel {p}')]:
        lines += [f'Goal True. let n := eval vm_compute in ({expression}) in idtac "REGISTRY_{marker}" n. exact I. Qed.']
    lines += ['Local Opaque actual_order certified_order residual_order.',
      f'Theorem all_checked_producers : Forall(ProducerIdempotent {p})checked_order.',
      f'Proof. exact(certified_order_sound producer_rules {p} actual_order actual_fuel_positive). Qed.',
      'Theorem original_ordered_when_checked : ordered_check producer_rules transport_rules actual_order=true ->',
      f' OrderedProducerCertificate {p} actual_order.',
      f'Proof. exact(ordered_check_sound producer_rules transport_rules {p} actual_order actual_fuel_positive). Qed.']
    audits=['all_checked_producers','original_ordered_when_checked']
    if prove_ordered:
        lines += ['Lemma actual_order_check : ordered_check producer_rules transport_rules actual_order=true.',
                  'Proof. vm_compute. reflexivity. Qed.',
                  f'Theorem original_ordered_certificate : OrderedProducerCertificate {p} actual_order.',
                  'Proof. exact(original_ordered_when_checked actual_order_check). Qed.']
        audits.append('original_ordered_certificate')
    for i,name in enumerate(audits):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.',
                  f'Print Assumptions {name}.']
    return ast,'\n'.join(lines)+'\n',len(audits)


def counts(log):
    result={}
    for name in ('TOTAL','ACCEPTED','RESIDUAL','LFP_FUEL'):
        found=re.findall(r'^REGISTRY_'+name+r'\s+(\d+)\s*$',log,re.M)
        if len(found)!=1:
            raise ValueError('missing or ambiguous actual Coq count '+name)
        result[name.lower()]=int(found[0])
    if result['accepted']+result['residual']!=result['total']:
        raise ValueError('partition does not cover the complete actual order')
    return result


def check_profile(profile, output, timeout=1200, prove_ordered=False):
    output=Path(output)
    if output.exists():raise ValueError('output must be fresh')
    output.mkdir(parents=True)
    ast,text,count=proposal(profile,prove_ordered)
    source=output/'Registry.v';source.write_text(text)
    flags=list(adapter.framework.FLAGS)
    for entry in profile.get('coq_load_paths',[]):flags+=['-R',entry['directory'],entry['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedCombRegistry']
    report=dict(accepted=False,source_sha256=hashlib.sha256(text.encode()).hexdigest(),
      ast_sha256=ast['source_sha256'],actual_program=profile['ast']['program'],
      requested_full_ordered_certificate=prove_ordered,full_ordered_certificate_proved=False,
      global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0,audited_exports=count)
    start=time.monotonic()
    c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(source.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        report['counts']=counts(c.stdout)
        report['assumptions_closed']=scalar.audit_output(c.stdout,count)
        start=time.monotonic()
        k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                      'GeneratedCombRegistry.Registry'],output/'coqchk.log',timeout)
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-start)
        report['accepted']=report['assumptions_closed']and k.returncode==0
        report['full_ordered_certificate_proved']=report['accepted']and prove_ordered
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def emit_library(profile, path, prove_ordered=False):
    """Persist the exact candidate, without asserting that it is checked."""
    path=Path(path)
    if not path.is_absolute():path=adapter.ROOT/path
    try:path.resolve().relative_to(adapter.ROOT/'src/Ex/Generated')
    except ValueError:raise ValueError('library must stay under src/Ex/Generated')
    if path.suffix!='.v':raise ValueError('library must be a .v')
    _,text,_=proposal(profile,prove_ordered)
    if path.exists()and path.read_text()!=text:
        raise ValueError('refuse to overwrite a different generated library')
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    return path


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--prove-ordered',action='store_true')
    parser.add_argument('--emit-library',type=Path)
    args=parser.parse_args()
    profile=json.loads(args.profile.read_text())
    if args.emit_library:emit_library(profile,args.emit_library,args.prove_ordered)
    result=check_profile(profile,args.output,prove_ordered=args.prove_ordered)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
