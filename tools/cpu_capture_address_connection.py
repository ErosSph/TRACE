"""Join fresh raw address cones to endogenous capture histories.
No caller-provided token word equality is accepted by the generated theorem.
The capture invariant is a checked local history, not a CPU ISA invariant.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_operand_address_origins as addresses
import cpu_pending_capture_birth as births
import cpu_instruction_fields as fields
from cpu_certificate_acceptance import run_stage


def strip(e):
    T=origin.pending.rtl.Term
    args=tuple(strip(x)for x in e.args)
    e=T(e.name,args)
    if e.name=='EExtend'and args[1].name=='false'and args[2].args and args[0]==args[2].args[0]:
        return args[2]
    return e


def verify(folder,file,source):
    folder=Path(folder);r=json.loads((folder/'report.json').read_text())
    if not(r.get('accepted')is True and r.get('coqc_exit')==r.get('coqchk_exit')==0
        and r.get('assumptions_closed')is True and (folder/file).read_text()==source
        and r.get('source_sha256')==hashlib.sha256(source.encode()).hexdigest()
        and(folder/file).with_suffix('.vo').exists()):raise ValueError('checked raw provider mismatch')


def select_connections(rows,captures):
    joins=[];residuals=[]
    for row in rows:
        field=fields.match_field(strip(origin.pending.rtl.Parser(row['expanded']).complete()),row['width'])
        candidates=[(i,b)for i,b in enumerate(captures)if b['carrier']==row['source']]
        if not field or field['field']not in('Rs1','Rs2')or len(candidates)!=1:
            residuals.append(dict(row,reason='requires unique capture carrier and canonical source field'));continue
        i,b=candidates[0];joins.append((row,field,i,b))
    return joins,residuals


def automatic(ast_path,ast_module,output,address_provider=None):
    """Build both providers from raw AST; do not consult an old CPU INV."""
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=origin.raw_binding(ast_path,ast_module)
    rows,unresolved,_,_=addresses.discover(ast)
    birth_plan=births.discover(ast)
    joins,unmatched=select_connections(rows,birth_plan['captures'])
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        isa_admission_proved=False,ast_sha256=ast['source_sha256'],
        candidate_connections=len(joins),residuals=unresolved+unmatched,
        capture_residuals=birth_plan['residuals'],native_started=False)
    if not joins:
        report['status']='no_supported_capture_address_join'
    else:
        report['native_started']=True
        address_folder=Path(address_provider)if address_provider else output/'addresses'
        if address_provider:
            _,source,_,_=addresses.render(ast_path,ast_module)
            verify(address_folder,'AddressOrigins.v',source)
            ar=json.loads((address_folder/'report.json').read_text())
        else:
            ar=addresses.check(ast_path,ast_module,address_folder)
        report['address_provider']=ar
        if ar.get('accepted'):
            br=births.check(ast_path,ast_module,output/'births')
            report['birth_provider']=br
            if br.get('accepted'):
                result=run(ast_path,ast_module,address_folder,output/'births',output/'connection')
                report['connection']=result
                report['accepted']=result['accepted']
        report['status']='checked_local_connections'if report['accepted']else'provider_or_connection_failed'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


def run(ast_path,ast_module,address_provider,birth_provider,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ar,asource,paths,_=addresses.render(ast_path,ast_module)
    br,bsource=births.render(ast_path,ast_module)
    verify(address_provider,'AddressOrigins.v',asource);verify(birth_provider,'CaptureBirth.v',bsource)
    ast,p,_=origin.raw_binding(ast_path,ast_module);program=p['ast']['program']
    joins,residuals=select_connections(ar['origins'],br['captures'])
    lines=[f'Require Import {ast_module}.','From Coq Require Import ZArith List Lia.',
        'Require Import GeneratedAddressOrigins.AddressOrigins GeneratedCaptureBirth.CaptureBirth',
        ' Ex.External.CPUISADecodeInputs Ex.External.CPUInstructionFields Ex.External.CPUPhysicalRegisterFile Ex.External.CPUIndexedSource',
        ' Ex.External.CV32E40PReq41Instruction Lang.ExtendedSV Lang.ExtendedSVBitSlice',
        ' Lang.ExtendedSVWordInvariant Lang.ExtendedSVCaptureBirth Lang.ExtendedSVCoveredField.',
        'Import ListNotations ExtendedSV ExtendedSVBitSlice ExtendedSVWordInvariant CPUInstructionFields CPUPhysicalRegisterFile',
        ' ExtendedSVCaptureBirth CPUISADecodeInputs CV32E40PReq41Instruction.',
        'Module A:=GeneratedAddressOrigins.AddressOrigins. Module B:=GeneratedCaptureBirth.CaptureBirth.']
    for row,field,i,b in joins:
        r=row['root'];w=row['width'];src=row['source'];v=b['valid_root'];f=field['field'];off=15 if f=='Rs1' else 20
        extra=''if f=='Rs1'else'first ';shape='address::rest'if f=='Rs1'else'first::address::rest'
        rule='actual_first_address'if f=='Rs1'else'actual_second_address'
        run=f'(B.capture_{i}_run events pre g)'
        lines += [f'Lemma address_{r}_layout word:A.address_{r}_reference word=field_reference word {f}.',
            f'Proof. let expression:=eval vm_compute in A.address_{r}_expanded in',
            f'change(norm {w}(eval_expr(write_signal [] {src} word)expression)=field_reference word {f}).',
            'cbn[eval_expr];rewrite read_signal_write_same;repeat rewrite norm_idempotent.',
            f'change(read_slice(norm 32 word){off} 5=field_reference word {f}).',
            'rewrite read_slice_normalized_inside by lia;apply read_slice_reference;lia. Qed.',
            f'Theorem captured_address_{r} events pre g seed:',
            f'Forall(fun ev=>changed_signal ev<>{src}%nat /\\changed_signal ev<>{v}%nat)events ->',
            f'Invariant {src} {v} pre g ->',
            f'CombLFP {program} seed(fst {run}) ->',
            f'norm 1(read_signal(fst {run}){v})<>0%Z ->',
            f'exists label,current(snd {run})=Some label /\\',
            f'forall instruction {extra}address rest,',
            'Decode.decode Decode.RV32I(token_word label)=Decode.IInstruction instruction ->',
            f'source_registers instruction={shape} ->',
            f'norm {w}(read_signal(fst {run}){r})=address.',
            f'Proof. intros HE HI HL HV;pose proof(B.capture_{i}_replay events HE pre g HI)as H.',
            'destruct H as[H _];destruct(ExtendedSVCoveredField.related_valid_value _ _ _ _ _ _ H HV)as[label[HT HW]].',
            f'exists label;split;[exact HT|];intros instruction {extra}address rest HD HS.',
            f'eapply {rule};[|exact HD|exact HS].',
            f'rewrite(A.address_{r}_instruction seed(fst {run})(token_word label)HL HW).',
            f'exact(address_{r}_layout(token_word label)). Qed.',
            f'Print Assumptions address_{r}_layout. Print Assumptions captured_address_{r}.']
        pos=0 if f=='Rs1'else 1
        lines += [f'Theorem captured_address_{r}_indexed events pre g seed:',
            f'Forall(fun ev=>changed_signal ev<>{src}%nat /\\changed_signal ev<>{v}%nat)events ->',
            f'Invariant {src} {v} pre g ->CombLFP {program} seed(fst {run}) ->',
            f'norm 1(read_signal(fst {run}){v})<>0%Z ->',
            f'exists label,current(snd {run})=Some label /\\forall instruction,',
            'Decode.decode Decode.RV32I(token_word label)=Decode.IInstruction instruction ->',
            f'IndexedSourceAddress {w} {r} (fst {run}) instruction {pos}%nat.',
            f'Proof. intros HE HI HL HV;destruct(captured_address_{r} events pre g seed HE HI HL HV)as[label[HT HA]].',
            'exists label;split;[exact HT|];intros instruction HD;unfold IndexedSourceAddress.',
            'destruct(source_registers instruction)as[|first rest]eqn:HS;[exact I|].']
        if pos:
            lines += ['destruct rest as[|address rest];[exact I|].',
                'exact(HA instruction first address rest HD HS). Qed.']
        else:
            lines += ['exact(HA instruction first rest HD HS). Qed.']
        lines += [f'Print Assumptions captured_address_{r}_indexed.']
    source='\n'.join(lines)+'\n';path=output/'CaptureAddresses.v';path.write_text(source)
    flags=list(origin.pending.rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(Path(address_provider).resolve()),'GeneratedAddressOrigins','-R',str(Path(birth_provider).resolve()),'GeneratedCaptureBirth','-R',str(output.resolve()),'GeneratedCaptureAddresses']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',deadline-time.monotonic())
    report=dict(accepted=False,coqc_exit=c.returncode,coqc_timed_out=t,connections=len(joins),residuals=residuals,
        old_inv_read=False,isa_admission_proved=False,complete_R_generated=False)
    if c.returncode==0 and joins:
        closed=c.stdout.count('Closed under the global context')==3*len(joins)and'Axioms:'not in c.stdout
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedCaptureAddresses.CaptureAddresses'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
        report.update(assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    for name in ['address-provider','birth-provider']:p.add_argument('--'+name)
    a=p.parse_args()
    if bool(a.address_provider)!=bool(a.birth_provider):p.error('supply both providers or neither')
    r=(run(a.ast,a.ast_module,a.address_provider,a.birth_provider,a.output)if a.address_provider
       else automatic(a.ast,a.ast_module,a.output))
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
