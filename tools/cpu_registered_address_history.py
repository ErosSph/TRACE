"""Prove actual registered RF addresses against their last captured word.
No CPU INV, invented validity bit, or caller-provided label map is used.
"""
import argparse,json,time
from pathlib import Path
import cpu_capture_address_connection as c
from cpu_certificate_acceptance import run_stage
o=c.origin


def match(row):
    e=row['expression'];root=row['root']
    if row['width']!=5 or e.name!='ECond' or e.args[0].name!='5':return None
    _,guard,yes,no=e.args
    if not c.births.validity.is_var(no,5,root):return None
    field=c.fields.match_field(yes,5)
    if not field or field['field']not in('Rs1','Rs2'):return None
    return dict(root=root,process=row['process'],guard=o.pending.rtl.render(guard),**field)


def render(ast_path,ast_module):
    ast,p,paths=o.raw_binding(ast_path,ast_module)
    roots=sorted({int(n.args[1].name)for port in c.addresses.readers.analyze(ast)['ports']
        for n in o.pending.rtl.walk(port['rhs'])if n.name=='EVar'and n.args[0].name in('5','6')})
    seq=[r for r in roots if any(pr['kind']=='Sequential'and r in pr['writers']for pr in ast['processes'])]
    if not seq:return dict(connections=0,residuals=roots),None,paths,0
    _,res,outputs,prefix,count=o.expressions.proposal(p,seq)
    selected=[]
    for row in outputs:
        candidate=match(row)
        if candidate:selected.append(candidate)
        else:res.append(dict(root=row['root'],reason='requires capture-field/hold shape'))
    if not selected:return dict(connections=0,residuals=res),None,paths,0
    program=p['ast']['program']
    lines=['Require Import Ex.External.CPURegisteredFieldHistory Ex.External.CPUISADecodeInputs Ex.External.CPUInstructionFields Ex.External.CV32E40PReq41Instruction Ex.External.CPUIndexedSource.',
        'Require Import Lang.ExtendedSVScalarHistory Lang.ExtendedSVWordInvariant.',
        'Import CPUInstructionFields CPUISADecodeInputs ExtendedSVScalarHistory ExtendedSVWordInvariant.',
        'Local Transparent read_signal PhaseSemantics phase_driven_state norm.']
    for row in selected:
        r=row['root'];src=row['source'];f=row['field'];proc=ast['module']+'.'+row['process']
        rule='actual_first_address'if f=='Rs1'else'actual_second_address'
        extra=''if f=='Rs1'else'first ';shape='address::rest'if f=='Rs1'else'first::address::rest'
        lines += [f'Definition address_{r}_guard:Expr:={row["guard"]}.',
            f'Lemma address_{r}_self:self_widthb 5 {r} root_{r}_expression=true.',
            'Proof. vm_compute;reflexivity. Qed.',
            f'Definition address_{r}_certificate:ScalarCertificate {program} {r} 5 {proc} root_{r}_expression:=',
            f'Build_ScalarCertificate _ _ _ _ _ root_{r}_comb_frame address_{r}_self root_{r}_expression_phase.',
            f'Lemma address_{r}_shape s:norm 5(eval_expr s root_{r}_expression)=',
            f'if Z.eqb(eval_expr s address_{r}_guard)0 then norm 5(read_signal s {r})else field_reference(read_signal s {src}){f}.',
            f'Proof. unfold root_{r}_expression,address_{r}_guard;cbn[eval_expr].',
            'destruct(Z.eqb _ 0);repeat rewrite norm_idempotent;[reflexivity|].',
            f'exact(field_value s {src} {f}). Qed.',
            f'Definition address_{r}_word_history events pre:=CPURegisteredFieldHistory.history {program} {proc} address_{r}_guard {src} events pre None.',
            f'Theorem address_{r}_history_decoded events pre code instruction {extra}address rest:',
            f'Forall(fun ev=>changed_signal ev<>{r}%nat)events ->',
            f'address_{r}_word_history events pre=Some code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            f'CV32E40PReq41Instruction.source_registers instruction={shape} ->',
            f'norm 5(read_signal(phase_run {program} events pre){r})=address.',
            'Proof. intros HE HC HD HS.',
            f'eapply {rule};[|exact HD|exact HS].',
            f'exact(CPURegisteredFieldHistory.from_unknown {program} {r} {proc} root_{r}_expression address_{r}_guard {src} {f}',
            f' address_{r}_certificate address_{r}_shape events pre HE code HC). Qed.',
            f'Print Assumptions address_{r}_history_decoded.']
        count+=1
        pos=0 if f=='Rs1'else 1
        lines += [f'Theorem address_{r}_history_indexed events pre code instruction:',
            f'Forall(fun ev=>changed_signal ev<>{r}%nat)events ->',
            f'address_{r}_word_history events pre=Some code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            f'IndexedSourceAddress 5 {r} (phase_run {program} events pre) instruction {pos}%nat.',
            'Proof. intros HE HC HD;unfold IndexedSourceAddress.',
            'destruct(CV32E40PReq41Instruction.source_registers instruction)as[|first rest]eqn:HS;[exact I|].']
        if pos:
            lines += ['destruct rest as[|address rest];[exact I|].',
                f'exact(address_{r}_history_decoded events pre code instruction first address rest HE HC HD HS). Qed.']
        else:
            lines += [f'exact(address_{r}_history_decoded events pre code instruction first rest HE HC HD HS). Qed.']
        lines += [f'Print Assumptions address_{r}_history_indexed.']
        count+=1
    pairs=[]
    for first in selected:
        if first['field']!='Rs1':continue
        peers=[second for second in selected if second['field']=='Rs2'and
            all(first[k]==second[k]for k in('process','guard','source'))]
        if len(peers)!=1:continue
        a,b=first['root'],peers[0]['root'];pairs.append([a,b])
        lines += [f'Lemma addresses_{a}_{b}_same_word events pre:',
            f'address_{a}_word_history events pre=address_{b}_word_history events pre.',
            'Proof. reflexivity. Qed.',
            f'Theorem addresses_{a}_{b}_joint events pre code instruction rs1 rs2 rest:',
            f'Forall(fun ev=>changed_signal ev<>{a}%nat)events ->',
            f'Forall(fun ev=>changed_signal ev<>{b}%nat)events ->',
            f'address_{a}_word_history events pre=Some code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            'CV32E40PReq41Instruction.source_registers instruction=rs1::rs2::rest ->',
            f'norm 5(read_signal(phase_run {program} events pre){a})=rs1 /\\',
            f'norm 5(read_signal(phase_run {program} events pre){b})=rs2.',
            'Proof. intros HA HB HC HD HS;split.',
            f'- exact(address_{a}_history_decoded events pre code instruction rs1(rs2::rest)HA HC HD HS).',
            f'- exact(address_{b}_history_decoded events pre code instruction rs1 rs2 rest HB',
            f' (eq_trans(eq_sym(addresses_{a}_{b}_same_word events pre))HC)HD HS). Qed.',
            f'Print Assumptions addresses_{a}_{b}_same_word. Print Assumptions addresses_{a}_{b}_joint.']
        count+=2
    return dict(connections=len(selected),selected=selected,joint_pairs=pairs,residuals=res),prefix+'\n'+'\n'.join(lines)+'\n',paths,count


def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    r,source,paths,count=render(ast_path,ast_module)
    r.update(accepted=False,old_inv_read=False,complete_R_generated=False,isa_admission_proved=False,
             operand_freshness_proved=False,history_presence_proved=False)
    if source:
        file=output/'RegisteredAddresses.v';file.write_text(source)
        flags=list(o.pending.rtl.framework.FLAGS)
        for p in paths:flags+=['-R',p['directory'],p['namespace']]
        flags+=['-R',str(output.resolve()),'GeneratedRegisteredAddresses']
        start=time.monotonic();deadline=start+1200
        result,t=run_stage([str(o.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
        r.update(coqc_exit=result.returncode,coqc_timed_out=t)
        if result.returncode==0:
            closed=result.stdout.count('Closed under the global context')==count and'Axioms:'not in result.stdout
            k,t=run_stage([str(o.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedRegisteredAddresses.RegisteredAddresses'],output/'coqchk.log',max(.1,deadline-time.monotonic()))
            r.update(assumptions_closed=closed,coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=closed and k.returncode==0)
        r['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(r,indent=2)+'\n');return r


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
