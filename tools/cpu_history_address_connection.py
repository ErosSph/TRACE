"""Raw actual RF cones -> sequential word history -> original ISA read address.

This rule needs no guessed valid bit or externally supplied token labels.
The observed history is not an ISA admission history or operand-value proof.
"""
import argparse,json,time
from pathlib import Path
import cpu_capture_address_connection as capture
from cpu_certificate_acceptance import run_stage
origin=capture.origin


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    address_plan,address_source,_,address_count=capture.addresses.render(ast_path,ast_module)
    rows=[];residuals=list(address_plan['residuals'])
    for row in address_plan['origins']:
        field=capture.fields.match_field(capture.strip(origin.pending.rtl.Parser(row['expanded']).complete()),row['width'])
        if field and field['field']in('Rs1','Rs2'):
            rows.append((row,field))
    if not address_source or not rows:
        return dict(connections=0,residuals=residuals,status='no_direct_word_address_cone'),None,paths,0
    roots=sorted({row['source']for row,_ in rows})
    _,unsupported,outputs,scalar_source,scalar_count=origin.expressions.proposal(profile,roots)
    if unsupported:
        return dict(connections=0,residuals=residuals+unsupported,status='source_history_unsupported'),None,paths,0
    program=profile['ast']['program'];out={r['root']:r for r in outputs}
    lines=['Require Import Lang.ExtendedSVScalarHistory Ex.External.CPUISADecodeInputs Ex.External.CPUInstructionFields Ex.External.CPUPhysicalRegisterFile Ex.External.CV32E40PReq41Instruction Ex.External.CPUIndexedSource.',
           'Import ExtendedSV ExtendedSVBitSlice ExtendedSVWordInvariant ExtendedSVScalarHistory CPUISADecodeInputs CPUInstructionFields CPUPhysicalRegisterFile.',
           'Module A:=Address. Module W:=Word.']
    count=address_count+scalar_count
    for root in roots:
        r=out[root]
        if r['width']!=32 or not origin.histories.self_width_supported(r['expression'],root,32):
            return dict(connections=0,residuals=residuals,status='non_word_self_feedback'),None,paths,0
        proc=ast['module']+'.'+r['process']
        lines += [f'Lemma word_{root}_self:self_widthb 32 {root} W.root_{root}_expression=true.',
            'Proof. vm_compute;reflexivity. Qed.',
            f'Definition word_{root}_certificate:ScalarCertificate {program} {root} 32 {proc} W.root_{root}_expression:=',
            f'Build_ScalarCertificate _ _ _ _ _ W.root_{root}_comb_frame word_{root}_self W.root_{root}_expression_phase.',
            f'Definition word_{root}_history events pre:=local_run 32 {root} W.root_{root}_expression',
            f'(observed_frames {program} {proc} {root} events pre)(norm 32(read_signal pre {root})).',
            f'Lemma word_{root}_history_actual events pre:Forall(fun ev=>changed_signal ev<>{root}%nat)events ->',
            f'norm 32(read_signal(phase_run {program} events pre){root})=word_{root}_history events pre.',
            f'Proof. exact(history_from_initial {program} {root} 32 {proc} W.root_{root}_expression word_{root}_certificate events pre). Qed.',
            f'Print Assumptions word_{root}_history_actual.']
        count+=1
    for row,f in rows:
        r=row['root'];src=row['source'];field=f['field'];off=15 if field=='Rs1'else 20
        extra=''if field=='Rs1'else'first ';shape='address::rest'if field=='Rs1'else'first::address::rest'
        rule='normalized_first_address'if field=='Rs1'else'normalized_second_address'
        lines += [f'Lemma address_{r}_layout word:A.address_{r}_reference word=field_reference word {field}.',
            f'Proof. let expression:=eval vm_compute in A.address_{r}_expanded in',
            f'change(norm 5(eval_expr(write_signal [] {src} word)expression)=field_reference word {field}).',
            'cbn[eval_expr];rewrite read_signal_write_same;repeat rewrite norm_idempotent.',
            f'change(read_slice(norm 32 word){off} 5=field_reference word {field}).',
            'rewrite read_slice_normalized_inside by lia;apply read_slice_reference;lia. Qed.',
            f'Theorem history_address_{r} events pre seed instruction {extra}address rest:',
            f'Forall(fun ev=>changed_signal ev<>{src}%nat)events ->',
            f'CombLFP {program} seed(phase_run {program} events pre) ->',
            f'Decode.decode Decode.RV32I(word_{src}_history events pre)=Decode.IInstruction instruction ->',
            f'CV32E40PReq41Instruction.source_registers instruction={shape} ->',
            f'norm 5(read_signal(phase_run {program} events pre){r})=address.',
            'Proof. intros HE HL HD HS.',
            f'apply (CPUISANormalizedInputs.{rule} (read_signal(phase_run {program} events pre){src})',
            f'(word_{src}_history events pre) instruction _ {extra}address rest).',
            f'- rewrite(A.address_{r}_instruction seed(phase_run {program} events pre)',
            f' (read_signal(phase_run {program} events pre){src})HL eq_refl). apply address_{r}_layout.',
            f'- rewrite(word_{src}_history_actual events pre HE). apply eq_sym.',
            f'  rewrite <- (word_{src}_history_actual events pre HE);apply norm_idempotent.',
            '- exact HD. - exact HS. Qed.',
            f'Print Assumptions address_{r}_layout. Print Assumptions history_address_{r}.']
        count+=2
        pos=0 if field=='Rs1' else 1
        lines += [f'Theorem history_address_{r}_indexed events pre seed instruction:',
            f'Forall(fun ev=>changed_signal ev<>{src}%nat)events ->',
            f'CombLFP {program} seed(phase_run {program} events pre) ->',
            f'Decode.decode Decode.RV32I(word_{src}_history events pre)=Decode.IInstruction instruction ->',
            f'IndexedSourceAddress 5 {r} (phase_run {program} events pre) instruction {pos}%nat.',
            'Proof. intros HE HL HD;unfold IndexedSourceAddress.',
            'destruct(CV32E40PReq41Instruction.source_registers instruction)as[|first rest]eqn:HS;[exact I|].']
        if pos:
            lines += ['destruct rest as[|address rest];[exact I|].',
                f'exact(history_address_{r} events pre seed instruction first address rest HE HL HD HS). Qed.']
        else:
            lines += [f'exact(history_address_{r} events pre seed instruction first rest HE HL HD HS). Qed.']
        lines += [f'Print Assumptions history_address_{r}_indexed.']
        count+=1
    source=f'From Coq Require Import List ZArith Lia.\nRequire Import {ast_module} Ex.External.CPUISANormalizedInputs Lang.ExtendedSV Lang.ExtendedSVBitSlice Lang.ExtendedSVWordInvariant.\nImport ListNotations.\nModule Address.\n'+address_source+'\nEnd Address.\nModule Word.\n'+scalar_source+'\nEnd Word.\n'+'\n'.join(lines)+'\n'
    return dict(connections=len(rows),residuals=residuals,status='generated',roots=roots),source,paths,count


def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report,source,paths,count=render(ast_path,ast_module)
    report.update(accepted=False,old_inv_read=False,complete_R_generated=False,
        isa_admission_proved=False,operand_freshness_proved=False)
    if source:
        path=output/'HistoryAddresses.v';path.write_text(source)
        flags=list(origin.pending.rtl.framework.FLAGS)
        for p in paths:flags+=['-R',p['directory'],p['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedHistoryAddresses']
        start=time.monotonic();deadline=start+1200
        c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',1200)
        report.update(coqc_exit=c.returncode,coqc_timed_out=t)
        if c.returncode==0:
            closed=c.stdout.count('Closed under the global context')==count and 'Axioms:'not in c.stdout
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedHistoryAddresses.HistoryAddresses'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
            report.update(assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
