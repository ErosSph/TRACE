"""Join full tagged RF addresses to generated actual capture histories.
Never truncate a bank tag or use an old CPU joint invariant.
"""
import argparse,json,time
from pathlib import Path
import cpu_capture_address_connection as c
import cpu_operand_tagged_origins as tagged
from cpu_certificate_acceptance import run_stage
o=c.origin


def select(rows,captures):
    joins=[];missing=[]
    for row in rows:
        matches=[(i,b)for i,b in enumerate(captures)if b['carrier']==row['word_root']]
        if row['field']not in('Rs1','Rs2')or len(matches)!=1:missing.append(row);continue
        i,b=matches[0];joins.append((row,i,b))
    return joins,missing


def check(ast_path,ast_module,output,address_provider=None,birth_provider=None):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,p,paths=o.raw_binding(ast_path,ast_module)
    ar,asource,_,_=tagged.render(ast_path,ast_module)
    birth_plan=c.births.discover(ast)
    joins,missing=select(ar['origins'],birth_plan['captures'])
    report=dict(accepted=False,connections=len(joins),unresolved_roots=ar['unresolved_roots'],
        unmatched=missing,old_inv_read=False,complete_R_generated=False,isa_admission_proved=False,
        operand_freshness_proved=False,tag_truncated=False)
    def save():
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    if not asource or not joins:
        report['status']='no_supported_tagged_capture_join';return save()
    _,bsource=c.births.render(ast_path,ast_module)
    address_folder=Path(address_provider)if address_provider else output/'addresses'
    birth_folder=Path(birth_provider)if birth_provider else output/'births'
    if address_provider is None:
        report['address_provider']=tagged.check(ast_path,ast_module,address_folder)
        if not report['address_provider']['accepted']:return save()
    c.verify(address_folder,'TaggedAddresses.v',asource)
    if birth_provider is None:
        report['birth_provider']=c.births.check(ast_path,ast_module,birth_folder)
        if not report['birth_provider']['accepted']:return save()
    c.verify(birth_folder,'CaptureBirth.v',bsource)
    program=p['ast']['program']
    lines=[f'Require Import {ast_module}.',
        'From Coq Require Import List ZArith.',
        'Require Import GeneratedTaggedAddresses.TaggedAddresses GeneratedCaptureBirth.CaptureBirth',
        ' Ex.External.CPUISADecodeInputs Ex.External.CV32E40PReq41Instruction Ex.External.CPUIndexedSource',
        ' Lang.ExtendedSV Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCoveredField.',
        'Import ListNotations ExtendedSV ExtendedSVCaptureBirth CPUISADecodeInputs CV32E40PReq41Instruction.',
        'Module A:=GeneratedTaggedAddresses.TaggedAddresses. Module B:=GeneratedCaptureBirth.CaptureBirth.']
    for row,i,b in joins:
        root=row['root'];src=b['carrier'];v=b['valid_root'];f=row['field']
        extra=''if f=='Rs1'else'first ';shape='address::rest'if f=='Rs1'else'first::address::rest'
        rule='actual_first_address'if f=='Rs1'else'actual_second_address'
        run=f'(B.capture_{i}_run events pre g)'
        lines += [f'Theorem address_{root}_captured events pre g seed:',
            f'Forall(fun ev=>changed_signal ev<>{src}%nat /\\changed_signal ev<>{v}%nat)events ->',
            f'Invariant {src} {v} pre g ->CombLFP {program} seed(fst {run}) ->',
            f'norm 1(read_signal(fst {run}){v})<>0%Z ->',
            f'exists label,current(snd {run})=Some label /\\forall instruction {extra}address rest,',
            'Decode.decode Decode.RV32I(token_word label)=Decode.IInstruction instruction ->',
            f'source_registers instruction={shape} ->norm 6(read_signal(fst {run}){root})=address.',
            f'Proof. intros HE HI HL HV;pose proof(B.capture_{i}_replay events HE pre g HI)as[HR _].',
            'destruct(ExtendedSVCoveredField.related_valid_value _ _ _ _ _ _ HR HV)as[label[HT HW]].',
            f'exists label;split;[exact HT|];intros instruction {extra}address rest HD HS.',
            f'eapply {rule};[|exact HD|exact HS].',
            f'exact(A.address_{root}_tagged_origin seed(fst {run})(token_word label)HL HW). Qed.',
            f'Print Assumptions address_{root}_captured.']
        pos=0 if f=='Rs1'else 1
        lines += [f'Theorem address_{root}_captured_indexed events pre g seed:',
            f'Forall(fun ev=>changed_signal ev<>{src}%nat /\\changed_signal ev<>{v}%nat)events ->',
            f'Invariant {src} {v} pre g ->CombLFP {program} seed(fst {run}) ->',
            f'norm 1(read_signal(fst {run}){v})<>0%Z ->',
            f'exists label,current(snd {run})=Some label /\\forall instruction,',
            'Decode.decode Decode.RV32I(token_word label)=Decode.IInstruction instruction ->',
            f'IndexedSourceAddress 6 {root} (fst {run}) instruction {pos}%nat.',
            f'Proof. intros HE HI HL HV;destruct(address_{root}_captured events pre g seed HE HI HL HV)as[label[HT HA]].',
            'exists label;split;[exact HT|];intros instruction HD;unfold IndexedSourceAddress.',
            'destruct(source_registers instruction)as[|first rest]eqn:HS;[exact I|].']
        if pos:
            lines += ['destruct rest as[|address rest];[exact I|].',
                'exact(HA instruction first address rest HD HS). Qed.']
        else:
            lines += ['exact(HA instruction first rest HD HS). Qed.']
        lines += [f'Print Assumptions address_{root}_captured_indexed.']
    source='\n'.join(lines)+'\n';file=output/'TaggedCapture.v';file.write_text(source)
    flags=list(o.pending.rtl.framework.FLAGS)
    for path in paths:flags+=['-R',path['directory'],path['namespace']]
    # Parent first; nested providers retain their own logical namespaces.
    flags+=['-R',str(output.resolve()),'GeneratedTaggedCapture',
        '-R',str(address_folder.resolve()),'GeneratedTaggedAddresses',
        '-R',str(birth_folder.resolve()),'GeneratedCaptureBirth']
    start=time.monotonic();deadline=start+1200
    result,t=run_stage([str(o.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=result.returncode,coqc_timed_out=t)
    if result.returncode==0:
        closed=result.stdout.count('Closed under the global context')==2*len(joins)and'Axioms:'not in result.stdout
        k,t=run_stage([str(o.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedTaggedCapture.TaggedCapture'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
    report['seconds']=time.monotonic()-start
    return save()


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    for name in ['address-provider','birth-provider']:p.add_argument('--'+name)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output,a.address_provider,a.birth_provider)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
