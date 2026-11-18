"""Infer actual blocking stall/flush tails, without old CPU invariants.

A default-cleared flag is set from a selector only after a disabled gate has
cleared that selector. Prefix cases remain abstract, checked for non-writes.
The result is an actual-LFP control theorem, not a queue or ISA theorem.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage
rtl=origin.pending.rtl


def is_var(e,width):return e.name=='EVar'and e.args[0].name==str(width)
def is_const(e,width,value):return e.name=='EConst'and e.args==(rtl.Term(str(width)),rtl.Term(str(value)))
def scalar_set(st,width,root,value):
    return(st.name=='SAssign'and st.args[0].name=='false'and is_const(st.args[1],width,value)
        and st.args[2]==rtl.Term('LVar',(rtl.Term(str(width)),rtl.Term(str(root)))))


def discover(ast):
    rows=[];residuals=[]
    for index,p in enumerate(ast['processes']):
        if p['kind']!='Combinational':continue
        body=p['body'];depth=0
        while body.name=='SSeq'and len(body.args[0].args)==1:depth+=1;body=body.args[0].args[0]
        if body.name!='SSeq'or len(body.args[0].args)<3:continue
        statements=list(body.args[0].args);clear,flag=statements[-2:]
        if clear.name!='SIf'or flag.name!='SIf'or clear.args[2].name!='SSkip'or flag.args[2].name!='SSkip':continue
        g=clear.args[0];test=flag.args[0]
        if g.name!='EUnary'or g.args[:2]!=(rtl.Term('1'),rtl.Term('UNot'))or not is_var(g.args[2],1):continue
        if test.name!='EBinary'or test.args[1].name!='BNeq'or not is_var(test.args[3],int(test.args[2].args[0].name)):continue
        width=int(test.args[3].args[0].name)
        if not is_const(test.args[2],width,0):continue
        gate=int(g.args[2].args[1].name);selector=int(test.args[3].args[1].name)
        fs=flag.args[1]
        if fs.name!='SAssign'or fs.args[2].name!='LVar'or fs.args[2].args[0].name!='1':continue
        flag_root=int(fs.args[2].args[1].name)
        if not scalar_set(clear.args[1],width,selector,0)or not scalar_set(fs,1,flag_root,1):continue
        if len({gate,selector,flag_root})!=3:residuals.append('tail roots alias');continue
        prefix=statements[:-2];zeros=[i for i,s in enumerate(prefix)if scalar_set(s,1,flag_root,0)]
        if not zeros:residuals.append('flag has no explicit prefix zero');continue
        pivot=zeros[-1];after=prefix[pivot+1:]
        if any(flag_root in {rtl.root_of(n.args[2])for n in rtl.walk(s)if n.name=='SAssign'}for s in after):
            residuals.append('later prefix writes flag');continue
        if any(n.args[0].name!='false'for n in rtl.walk(p['body'])if n.name=='SAssign'):
            residuals.append('not blocking-only');continue
        rows.append(dict(process=p['name'],index=index,wrappers=depth,width=width,gate=gate,selector=selector,flag=flag_root,
            before=[rtl.render(s)for s in prefix[:pivot]],after=[rtl.render(s)for s in after],
            clear=rtl.render(clear),raise_flag=rtl.render(flag)))
    return dict(tails=rows,residuals=residuals,old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,
        queue_correspondence_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);data=discover(ast)
    if not data['tails']:raise ValueError('no supported complete stall/flush suffix; no assumed control law')
    p=profile['ast']['program'];lines=['From Coq Require Import List ZArith Bool.',
        'Require Import Lang.ExtendedSV Lang.ExtendedSVStallFlush Lang.ExtendedSVBlocking',
        f' Lang.ExtendedSVRootProjection Lang.ExtendedSVWordInvariant Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVCombCut {ast_module}.',
        'Import ListNotations ExtendedSV ExtendedSVStallFlush ExtendedSVBlocking ExtendedSVRootProjection',
        ' ExtendedSVAutoAdapterEffects ExtendedSVWordInvariant ExtendedSVCombCut.']
    for number,row in enumerate(data['tails']):
        prefix=f'ctrl_{number}';proc=ast['module']+'.'+row['process'];g=row['gate'];s=row['selector'];f=row['flag'];w=row['width']
        def effects(sts):return '['+';'.join(rtl.render(rtl.effect_of(rtl.Parser(st).complete()))for st in sts)+']'
        lines += [f'Definition {prefix}_before:list EffectPlan:={effects(row["before"])}.',
            f'Definition {prefix}_after:list EffectPlan:={effects(row["after"])}.',
            f'Definition {prefix}_after_stmt:Stmt:=SSeq['+';'.join(row['after'])+'].',
            f'Definition {prefix}_prefix_code:={prefix}_before++[FAssign false(EConst 1 0)(LVar 1 {f})]++{prefix}_after.',
            f'Definition {prefix}_prefix:=FSeq {prefix}_prefix_code.',
            f'Definition {prefix}_after_effect:=FSeq {prefix}_after.']
        tail='['+rtl.render(rtl.effect_of(rtl.Parser(row['clear']).complete()))+';'+rtl.render(rtl.effect_of(rtl.Parser(row['raise_flag']).complete()))+']'
        effect=f'FSeq({prefix}_prefix_code++{tail})'
        for _ in range(row['wrappers']):effect='FSeq['+effect+']'
        lines += [f'Definition {prefix}_effect:EffectPlan:={effect}.',
            f'Lemma {prefix}_compiled:compile_effect(statement_fuel {p})(process_body {proc})=Some {prefix}_effect.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {prefix}_blocking:blocking_onlyb(process_body {proc})=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {prefix}_after_compiled:compile_effect(statement_fuel {p}){prefix}_after_stmt=Some {prefix}_after_effect.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {prefix}_after_no_flag:existsb(Nat.eqb {f})(stmt_writers {prefix}_after_stmt)=false.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {prefix}_registered:nth_error(processes {p}){row["index"]}=Some {proc}.',
            'Proof. vm_compute. reflexivity. Qed.']
        for r in[g,f]:
            lines += [f'Lemma {prefix}_suffix_{r}:avoids_root {r}(filter is_comb(skipn(S {row["index"]})(processes {p})))=true.',
                'Proof. vm_compute. reflexivity. Qed.']
        lines += [f'Local Opaque {p} {prefix}_before {prefix}_after.',
            f'Lemma {prefix}_after_frame es:read_signal(blocking_state(eval_effect {prefix}_after_effect es)){f}=',
            f' read_signal(blocking_state es){f}.',
            f'Proof. exact(checked_effect_frame(statement_fuel {p}){prefix}_after_stmt {prefix}_after_effect {f}',
            f' {prefix}_after_compiled {prefix}_after_no_flag es). Qed.',
            f'Lemma {prefix}_prefix_split es:eval_effect {prefix}_prefix es=',
            f' eval_effect {prefix}_after_effect(eval_effect(FAssign false(EConst 1 0)(LVar 1 {f}))(eval_effect(FSeq {prefix}_before)es)).',
            f'Proof. exact(effect_seq_sandwich {prefix}_before {prefix}_after(FAssign false(EConst 1 0)(LVar 1 {f}))es). Qed.',
            f'Lemma {prefix}_prefix_zero es:norm 1(read_signal(blocking_state(eval_effect {prefix}_prefix es)){f})=0%Z.',
            f'Proof. rewrite {prefix}_prefix_split,{prefix}_after_frame.',
            f' change(norm 1(read_signal(scalar_write 1 {f} 0(blocking_state(eval_effect(FSeq {prefix}_before)es))){f})=0%Z).',
            ' rewrite scalar_write_same,norm_zero;reflexivity. Qed.',
            f'Lemma {prefix}_effect_split es:eval_effect {prefix}_effect es=',
            f' eval_effect(gate_tail {w} {g} {s} {f})(eval_effect {prefix}_prefix es).',
            f'Proof. exact(effect_seq_append {prefix}_prefix_code {tail} es). Qed.',
            f'Theorem {prefix}_process s:norm 1(read_signal(run_process {p} s {proc}){f})<>0%Z ->',
            f' norm 1(read_signal(run_process {p} s {proc}){g})<>0%Z.',
            f'Proof. rewrite(blocking_run_process {p} {proc} s {prefix}_blocking).',
            f' rewrite(compile_effect_sound _ _ _ _ {prefix}_compiled),{prefix}_effect_split,effect_tail_state.',
            f' apply(tail_flush_requires_enable {w} {g} {s} {f} _);',
            f' [intro H;discriminate|intro H;discriminate|intro H;discriminate|apply {prefix}_prefix_zero]. Qed.',
            f'Theorem {prefix}_actual_lfp seed fixed:CombLFP {p} seed fixed ->',
            f' norm 1(read_signal fixed {f})<>0%Z ->norm 1(read_signal fixed {g})<>0%Z.',
            f'Proof. exact(actual_lfp_relation {p} {row["index"]} {proc} {g} {f}',
            f' (fun a b=>norm 1 b<>0%Z ->norm 1 a<>0%Z){prefix}_registered eq_refl',
            f' {prefix}_suffix_{g} {prefix}_suffix_{f} {prefix}_process seed fixed). Qed.',
            f'Print Assumptions {prefix}_process.',f'Print Assumptions {prefix}_actual_lfp.',
            f'Local Transparent {p}.']
    return dict(**data,ast_sha256=ast['source_sha256'],coq_load_paths=paths,audited_exports=2*len(data['tails'])),'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module)
    except ValueError as error:
        result=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,global_inv_proved=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result
    path=output/'StallFlush.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedStallFlush'];start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    result=dict(accepted=False,native_started=True,scope='actual whole-controller and LFP flush-implies-enable; not queue preservation',
        coqc_exit=c.returncode,coqc_timed_out=t,source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=data['ast_sha256'],
        old_inv_read=False,old_pending_read=False,old_cpu_proofs_used=False,queue_correspondence_proved=False,
        global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        result['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedStallFlush.StallFlush'],output/'coqchk.log',deadline-time.monotonic())
            result.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    result['overall_seconds']=time.monotonic()-start
    if result['accepted']:result['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True);p.add_argument('--ast-module',required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
