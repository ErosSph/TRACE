"""Connect original ISA ADD decoding to boot-derived stored RTL controls."""
import argparse,json,hashlib,time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage


def verified(folder,file):
    folder=Path(folder);r=json.loads((folder/'report.json').read_text())
    if not(r.get('accepted') is True and r.get('coqc_exit')==r.get('coqchk_exit')==0 and r.get('assumptions_closed')is True
      and hashlib.sha256((folder/(file+'.v')).read_bytes()).hexdigest()==r['source_sha256'] and (folder/(file+'.vo')).is_file()):
        raise ValueError('unchanged checked provider required')
    return r


def check(ast,module,history,controls,control_history,output):
    raw,profile,_=origin.raw_binding(ast,module)
    verified(controls,'ControlCones');verified(control_history,'ControlHistory')
    plan=json.loads((Path(controls)/'plan.json').read_text())
    if plan['ast_sha256']!=raw['source_sha256']:raise ValueError('different configured AST')
    rows=plan['rows'];p=profile['ast']['program']
    if len({r['word']for r in rows})!=1 or any(r['external']!=rows[0]['external']for r in rows) or len(rows[0]['external'])!=1:
        raise ValueError('single word and external reset input required')
    word,reset=rows[0]['word'],rows[0]['external'][0]
    source=f'''From Coq Require Import List ZArith.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarHistory
 Lang.ExtendedSVCaptureBirth Lang.ExtendedSVTwoInputExpression Ex.External.CPUInstructionFields
 Ex.External.CPUISAAddControlFields GeneratedControlCones.ControlCones GeneratedControlHistory.ControlHistory.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarHistory ExtendedSVCaptureBirth CPUInstructionFields CPUISAAddControlFields.
Module G:=GeneratedControlCones.ControlCones. Module H:=GeneratedControlHistory.ControlHistory.
Definition word_state code:=ExtendedSVTwoInputExpression.frame {word} code {reset} 1%Z.
Lemma state_word code:read_signal(word_state code){word}=code.
Proof. unfold word_state,ExtendedSVTwoInputExpression.frame.
 rewrite read_signal_write_other by discriminate;apply read_signal_write_same. Qed.
Lemma state_reset code:read_signal(word_state code){reset}=1%Z.
Proof. unfold word_state,ExtendedSVTwoInputExpression.frame;apply read_signal_write_same. Qed.
'''
    exports=[]
    for row in rows:
        x,w,src=row['root'],row['width'],row['capture']
        source+=f'''Lemma decoder_{x}_add code rd rs1 rs2:
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->G.decoder_{x} code 1%Z=0%Z.
Proof. intro HD;destruct(original_decode_add_fields code rd rs1 rs2 HD)as[HO[H3 H7]].
'''
        for field,hyp in [('Opcode','HO'),('Funct3','H3'),('Funct7','H7')]:
            fw,offset,value={'Opcode':(7,0,51),'Funct3':(3,12,0),'Funct7':(7,25,0)}[field]
            source+=f'''pose proof(native_field_reference(word_state code){word} {field})as F{field}.
unfold field_expr in F{field};cbn[field_width field_offset eval_expr]in F{field}.
rewrite state_word in F{field};repeat rewrite norm_idempotent in F{field};rewrite {hyp} in F{field}.
change(norm {fw}(Z.shiftr(norm 32 code)(norm 5 {offset}%Z))={value}%Z)in F{field}.
'''
        source+=f'''unfold G.decoder_{x};let e:=eval cbv in G.cone_{src} in
 change(norm {w}(eval_expr(word_state code)e)=0%Z).
cbn[eval_expr];rewrite ?state_word,?state_reset;repeat rewrite norm_idempotent.
rewrite FOpcode,?FFunct3,?FFunct7;reflexivity. Qed.
'''
        exports.append(f'decoder_{x}_add')
    source+=f'''Theorem actual_stored_add_controls image events token rd rs1 rs2:
 let pre:=phase_run {p} events(H.H.F.boot image)in
 Forall H.H.W.Environment events ->H.C.C.chain_tag0(snd(H.H.boot_history image events))=Some token ->
 Decode.decode Decode.RV32I(token_word token)=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
'''+ ' /\\\n'.join(f'norm {r["width"]}(read_signal pre {r["root"]})=0%Z'for r in rows)+'.\nProof. intros pre HE HT HD.\n'
    # Build the exact right-associated conjunction pattern, retaining row order.
    pattern='V'+str(len(rows)-1)
    for i in reversed(range(len(rows)-1)):pattern=f'[V{i} {pattern}]'
    source+=f'destruct(H.stored_controls image events token HE HT)as{pattern}.\n'
    for i,row in enumerate(rows):
        if i<len(rows)-1:source+='split.\n{ '
        source+=f'exact(eq_trans V{i}(decoder_{row["root"]}_add _ rd rs1 rs2 HD)).'
        source+=' }\n'if i<len(rows)-1 else'\n'
    source+='Qed.\nGoal True. idtac "ADD_CONTROL_ISA_AUDIT". exact I. Qed.\n'
    exports.append('actual_stored_add_controls')
    source+=''.join(f'Print Assumptions {e}.\n'for e in exports)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);file=out/'AddControl.v';file.write_text(source)
    paths=json.loads((Path(history)/'plan.json').read_text())['paths'];flags=list(origin.pending.rtl.framework.FLAGS)
    for path in paths:flags+=['-R',path['directory'],path['namespace']]
    for folder,ns in [(controls,'GeneratedControlCones'),(control_history,'GeneratedControlHistory'),(out,'GeneratedAddControl')]:
        flags+=['-R',str(Path(folder).resolve()),ns]
    start=time.monotonic();cc,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),complete_R_generated=False,isa_add_result_proved=False)
    if cc.returncode==0 and time.monotonic()-start<1200:
        kk,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedAddControl.AddControl'],out/'coqchk.log',1200-(time.monotonic()-start))
        tail=cc.stdout.split('ADD_CONTROL_ISA_AUDIT')[-1]
        closed=tail.count('Closed under the global context')==len(exports) and 'Axioms:'not in tail
        report.update(coqchk_exit=kk.returncode,assumptions_closed=closed,accepted=closed and kk.returncode==0)
    report['seconds']=time.monotonic()-start;(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['ast','ast-module','history','controls','control-history','output']:p.add_argument('--'+key,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.history,a.controls,a.control_history,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
