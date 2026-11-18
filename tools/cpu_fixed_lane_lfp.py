"""Connect discovered decoded-enable processes to the ORIGINAL CPU fixed point."""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_fixed_lane_enable as local
from cpu_certificate_acceptance import run_stage

def render(ast,profile,rows):
    p=profile['ast']['program'];combs=[x for x in ast['processes']if x['kind']=='Combinational']
    lines=[f'Require Import {profile["ast"]["module"]}.',
      'From Coq Require Import List ZArith Lia.',
      'Require Import GeneratedFixedLaneEnable.FixedLaneEnable Lang.ExtendedSV',
      ' Lang.ExtendedSVSliceCombConnection Lang.ExtendedSVCombConnection Lang.ExtendedSVCombCut',
      ' Lang.ExtendedSVConstantRoot Lang.ExtendedSVBitSlice.',
      'Import ListNotations ExtendedSV ExtendedSVSliceCombConnection ExtendedSVCombConnection',
      ' ExtendedSVCombCut ExtendedSVConstantRoot ExtendedSVBitSlice.',
      f'Definition combs:=filter is_comb(processes {p}).']
    audits=[]
    for n,r in enumerate(rows):
        addr=local.rtl.Parser(r['address']).complete()
        if addr.name!='EVar':raise ValueError('input stability rule requires full scalar address')
        w,ar=[int(x.name)for x in addr.args];idx=next(i for i,x in enumerate(combs)if x['name']==r['process'])
        proc=ast['module']+'.'+r['process'];root=r['root'];lane=r['lane']
        prefix=f'(firstn {idx} combs)';suffix=f'(skipn {idx+1} combs)'
        lines += [f'Lemma registered_{n}:nth_error combs {idx}=Some {proc}.',
          'Proof. vm_compute;reflexivity. Qed.',
          f'Lemma output_frame_{n}:forallb(slice_frameb {root}%nat {lane}%Z 1%Z){suffix}=true.',
          'Proof. vm_compute;reflexivity. Qed.',
          f'Lemma address_frame_{n}:roots_unwrittenb {ar}%nat({proc}::{suffix})=true.',
          'Proof. vm_compute;reflexivity. Qed.',
          f'Theorem lane_{n}_actual_lfp seed fixed:CombLFP {p} seed fixed ->',
          f' read_slice(read_signal fixed {root}){lane} 1<>0%Z ->',
          f' norm {w}(read_signal fixed {ar})=norm {w} {lane}.',
          'Proof. intros HL Hbit.',
          f' pose proof(split_at combs {idx} {proc} registered_{n})as Horder.',
          f' pose proof(actual_lfp_slice_output {p} {prefix} {proc} {suffix} {root}%nat {lane}%Z 1%Z',
          f' seed fixed Horder fuel_positive ltac:(clear;lia) ltac:(clear;lia) output_frame_{n} HL)as HO.',
          ' unfold slice_view in HO;rewrite HO in Hbit.',
          f' pose proof(lane_{n}_local_selection (fold_left(run_process {p}){prefix} fixed) Hbit)as HA.',
          f' change(norm {w}(read_signal(fold_left(run_process {p}){prefix} fixed){ar})=norm {w} {lane})in HA.',
          f' rewrite(actual_lfp_pivot_input {p} {prefix} {proc} {suffix} {ar}%nat seed fixed',
          f' Horder address_frame_{n} HL)in HA;exact HA. Qed.']
        audits.append(f'Print Assumptions lane_{n}_actual_lfp.')
    return '\n'.join(lines+audits)+'\n'

def check(ast_path,ast_module,provider,output):
    ast,profile,paths=local.ownership.origin.raw_binding(ast_path,ast_module)
    plan=local.discover(ast);rows=plan['rows'];out=Path(output);out.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,rows=len(rows),old_inv_read=False,isa_destination_proved=False,
        full_lfp_bit_connection_proved=False,complete_R_generated=False)
    if not rows:
        report['status']='no_applicable_fixed_lane_decoder'
        (out/'report.json').write_text(json.dumps(report,indent=2));return report
    provider=Path(provider);pr=json.loads((provider/'report.json').read_text())
    expected=local.render(ast_module,profile['ast']['program'],ast['module'],rows)
    if not(pr.get('accepted')is True and pr.get('coqc_exit')==pr.get('coqchk_exit')==0
        and pr.get('assumptions_closed')is True
        and pr['source_sha256']==hashlib.sha256(expected.encode()).hexdigest()
        and (provider/'FixedLaneEnable.v').read_text()==expected):
        raise ValueError('unchanged checked local decoder provider required')
    source=render(ast,profile,rows);file=out/'FixedLaneLFP.v';file.write_text(source)
    flags=list(local.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(provider.resolve()),'GeneratedFixedLaneEnable','-R',str(out.resolve()),'GeneratedFixedLaneLFP']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(local.rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==len(rows)and'Axioms:'not in c.stdout
        k,t=run_stage([str(local.rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedFixedLaneLFP.FixedLaneLFP'],out/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,assumptions_closed=closed,
            accepted=k.returncode==0 and closed,full_lfp_bit_connection_proved=k.returncode==0 and closed)
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','provider','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.provider,a.output);print(json.dumps(r,indent=2))
    raise SystemExit(0 if r['accepted']else 1)
