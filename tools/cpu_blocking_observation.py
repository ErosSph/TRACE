"""Backward observation compiler for original whole blocking processes.

Each generated step is checked against EffectPlan semantics. No old INV input.
"""
import argparse, hashlib, json, time
from pathlib import Path
import cpu_pending_origins as origin
from cpu_certificate_acceptance import run_stage
rtl=origin.pending.rtl

def inputs(e):
    return {(int(t.args[0].name),int(t.args[1].name)) for t in rtl.walk(e) if t.name=='EVar'}

class Compiler:
    def __init__(self,width):self.width=width;self.lines=[];self.serial=0;self.expression_aliases={}
    def emit(self,plan,post,before,proof,deps):
        i=self.serial;self.serial+=1
        self.expression_aliases[f'expr_{i}']=self.expression_aliases.get(before,before)
        self.lines += [f'Definition plan_{i}:EffectPlan:={plan}.',
          f'Definition expr_{i}:Expr:={before}.',
          f'Lemma obs_{i}:Observes plan_{i} {self.width} {post} expr_{i}.',
          f'Proof. {proof} Qed.']
        return f'plan_{i}',f'expr_{i}',f'obs_{i}',deps
    def compile(self,st,post,deps):
        n,a=st.name,st.args
        if n=='SSkip':return self.emit('FEmpty',post,post,'apply empty.',deps)
        if n=='SAssign':
            if a[0].name!='false':raise ValueError('non-blocking assignment is unsupported')
            root=rtl.root_of(a[2]);rhs=rtl.render(a[1])
            if a[2].name!='LVar':
                if any(x==root for w,x in deps):
                    # Exact reusable clear-low-bit certificate; no RTL rewrite.
                    if (rtl.render(a[2])==f'(LSel 1 (LVar 32 {root}) (EConst 5 0))'
                        and rhs=='(EConst 1 0)'
                        and all(w==32 for w,x in deps if x==root)):
                        plan=f'(FAssign false {rhs} {rtl.render(a[2])})'
                        return self.emit(plan,post,
                            f'(substitute(assign_substitution 32 {root} (cleared {root})){post})',
                            'apply clear_low_observation. vm_compute;reflexivity.',deps)
                    raise ValueError('observed partial write requires a substitution certificate')
                plan=f'(FAssign false {rhs} {rtl.render(a[2])})'
                return self.emit(plan,post,post,
                    'apply assignment_unread_lvalue_checked. vm_compute;reflexivity.',deps)
            aw=int(a[2].args[0].name)
            matches={(w,x)for w,x in deps if x==root}
            if any(w!=aw for w,x in matches):raise ValueError('read width differs from written width')
            plan=f'(FAssign false {rhs} (LVar {aw} {root}))'
            # Kernel checks the concrete dependency side condition, not Python.
            tactic='vm_compute;reflexivity.'
            if not matches:return self.emit(plan,post,post,'apply assignment_unread_checked. '+tactic,deps)
            return self.emit(plan,post,f'(substitute(assign_substitution {aw} {root} {rhs}){post})',
                'apply assignment_checked. '+tactic,(deps-matches)|inputs(a[1]))
        if n=='SSeq':
            tail=self.emit('(FSeq [])',post,post,'apply seq_nil.',deps)
            for child in reversed(a[0].args):
                head=self.compile(child,tail[1],tail[3])
                # The tail plan is a named FSeq; retain its list explicitly.
                children=getattr(self,'seq_children',{}).get(tail[0],[])
                plan='(FSeq ['+';'.join([head[0]]+children)+'])'
                combined=self.emit(plan,post,head[1],
                    f'eapply seq_cons;[exact {tail[2]}|exact {head[2]}].',head[3])
                if not hasattr(self,'seq_children'):self.seq_children={}
                self.seq_children[combined[0]]=[head[0]]+children
                tail=combined
            return tail
        if n=='SIf':
            yes=self.compile(a[1],post,deps);no=self.compile(a[2],post,deps)
            guard=rtl.render(a[0])
            if self.expression_aliases[yes[1]]==self.expression_aliases[no[1]]:
                return self.emit(f'(FIf {guard} {yes[0]} {no[0]})',post,yes[1],
                    f'apply branch_same;[exact {yes[2]}|exact {no[2]}].',yes[3]|no[3])
            return self.emit(f'(FIf {guard} {yes[0]} {no[0]})',post,
              f'(ECond {self.width} {guard} {yes[1]} {no[1]})',
              f'apply branch;[exact {yes[2]}|exact {no[2]}].',yes[3]|no[3]|inputs(a[0]))
        if n=='SCase':
            scr=rtl.render(a[0]);arms=list(a[1].args)
            if any(arm.args[0].name=='None' for arm in arms[:-1]):raise ValueError('non-final default needs explicit case normalization')
            tail=self.emit(f'(FCase {scr} [])',post,post,'apply case_nil.',deps);compiled=[]
            for arm in reversed(arms):
                key,body=arm.args;branch=self.compile(body,post,deps)
                if key.name=='None':
                    compiled=[f'(None,{branch[0]})']
                    tail=self.emit(f'(FCase {scr} ['+';'.join(compiled)+'])',post,branch[1],
                      f'apply case_default;exact {branch[2]}.',branch[3]);continue
                k=rtl.render(key.args[0]);compiled=[f'(Some {k},{branch[0]})']+compiled
                if self.expression_aliases[branch[1]]==self.expression_aliases[tail[1]]:
                    tail=self.emit(f'(FCase {scr} ['+';'.join(compiled)+'])',post,branch[1],
                        f'apply case_some_same;[exact {branch[2]}|exact {tail[2]}].',branch[3]|tail[3])
                    continue
                tail=self.emit(f'(FCase {scr} ['+';'.join(compiled)+'])',post,
                  f'(ECond {self.width} (EBinary 1 BEq {scr} {k}) {branch[1]} {tail[1]})',
                  f'apply case_some;[exact {branch[2]}|exact {tail[2]}].',
                  branch[3]|tail[3]|inputs(a[0])|inputs(key.args[0]))
            return tail
        raise ValueError('unsupported statement '+n)

def render(ast_path,module,process,root,width):
    ast,profile,paths=origin.raw_binding(ast_path,module)
    proc=next(p for p in ast['processes']if p['name']==process)
    c=Compiler(width);last=c.compile(proc['body'],f'(EVar {width} {root})',{(width,root)})
    program=profile['ast']['program'];pn=ast['module']+'.'+process
    lines=['From Coq Require Import List ZArith Bool.',
      f'Require Import Lang.ExtendedSV Lang.ExtendedSVAutoAdapterEffects Lang.ExtendedSVBlocking Lang.ExtendedSVSequentialSubstitution Lang.ExtendedSVProjectionConnection Lang.ExtendedSVExprAgreement Lang.ExtendedSVBlockingObservation Lang.ExtendedSVBlockingObservationPartial Lang.ExtendedSVBlockingObservationClearLowBit Lang.ExtendedSVBlockingObservationBranches {module}.',
      'Import ListNotations ExtendedSV ExtendedSVAutoAdapterEffects ExtendedSVBlocking ExtendedSVSequentialSubstitution ExtendedSVProjectionConnection ExtendedSVExprAgreement ExtendedSVBlockingObservation ExtendedSVBlockingObservationPartial ExtendedSVBlockingObservationClearLowBit ExtendedSVBlockingObservationBranches.']+c.lines+[
      f'Lemma original_blocking:blocking_onlyb(process_body {pn})=true. Proof. vm_compute;reflexivity. Qed.',
      f'Lemma compiled:compile_effect(statement_fuel {program})(process_body {pn})=Some {last[0]}. Proof. vm_compute;reflexivity. Qed.',
      f'Theorem actual_observation s:norm {width}(read_signal(run_process {program} s {pn}){root})=norm {width}(eval_expr s {last[1]}).',
      f'Proof. exact(actual_output {program} {pn} {last[0]} {width} {root} {last[1]} original_blocking compiled {last[2]} s). Qed.',
      'Goal True. idtac "BLOCKING_OBSERVATION_AUDIT". exact I. Qed.',
      'Print Assumptions actual_observation.']
    return '\n'.join(lines)+'\n',paths,dict(process=process,root=root,width=width,
      ast_sha256=ast['source_sha256'],dependencies=sorted(last[3]),rules=c.serial)

def check(ast_path,module,process,root,width,output):
    source,paths,report=render(ast_path,module,process,root,width)
    out=Path(output);out.mkdir(parents=True,exist_ok=False);path=out/'Observation.v';path.write_text(source)
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedBlockingObservation']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],out/'coqc.log',deadline-time.monotonic())
    report.update(accepted=False,complete_R_generated=False,old_inv_read=False,
      source_sha256=hashlib.sha256(source.encode()).hexdigest(),coqc_exit=c.returncode,coqc_timed_out=t)
    if c.returncode==0:
        audit=c.stdout.split('BLOCKING_OBSERVATION_AUDIT')[-1]
        k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedBlockingObservation.Observation'],out/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
          accepted=k.returncode==0 and audit.count('Closed under the global context')==1 and 'Axioms:'not in audit)
    report['seconds']=time.monotonic()-start
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for x in ['ast','ast-module','process','output']:p.add_argument('--'+x,required=True)
    p.add_argument('--root',type=int,required=True);p.add_argument('--width',type=int,required=True)
    a=p.parse_args();print(json.dumps(check(a.ast,a.ast_module,a.process,a.root,a.width,a.output),indent=2))
