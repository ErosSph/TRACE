"""Propose checked dependency slices for state-threaded multi-output processes.

Backward root closure is untrusted. Coq checks actual registration, safe erasure,
normalized input dependence and catalog soundness. No CPU-name dispatch or LLM.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_known_producers as known
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def roots_read(expr):
    return {int(n.args[1].name) for n in adapter.walk(expr) if n.name=='EVar'}


def writers(st):
    return {adapter.root_of(n.args[2]) for n in adapter.walk(st) if n.name=='SAssign'}


def retained_reads(st,targets):
    if not writers(st)&targets:return set()
    n,a=st.name,st.args
    if n=='SAssign':return roots_read(a[1])
    if n=='SSeq':return set().union(*(retained_reads(s,targets) for s in a[0].args))
    if n=='SIf':return roots_read(a[0])|retained_reads(a[1],targets)|retained_reads(a[2],targets)
    if n=='SCase':
        result=roots_read(a[0])
        for arm in a[1].args:
            key,body=arm.args
            if key.name=='Some':result|=roots_read(key.args[0])
            result|=retained_reads(body,targets)
        return result
    if n=='SSkip':return set()
    raise ValueError('unsupported original statement '+n)


def backward_closure(body,root):
    written=writers(body);targets={root};trace=[]
    for _ in range(len(written)+1):
        reads=retained_reads(body,targets);trace.append(sorted(targets))
        expanded=targets|(reads&written)
        if expanded==targets:
            return dict(kept=sorted(targets),observed=sorted(targets|reads),closure_trace=trace)
        targets=expanded
    raise ValueError('finite root closure failed to terminate')


def analyze(ast):
    selected=[];unsupported=[]
    for index,proc in enumerate(ast['processes']):
        if proc['kind']!='Combinational' or len(proc['writers'])<2 or not set(proc['readers'])&set(proc['writers']):continue
        assignments=[n for n in adapter.walk(proc['body']) if n.name=='SAssign']
        if any(n.args[0].name!='false' or n.args[2].name!='LVar' for n in assignments):
            unsupported.append(dict(index=index,process=proc['name'],reason='requires pure blocking whole-scalar assignments'));continue
        widths={}
        for node in assignments:
            w,r=(int(x.name) for x in node.args[2].args);widths.setdefault(r,set()).add(w)
        rows=[]
        for root,ws in sorted(widths.items()):
            if len(ws)!=1:
                unsupported.append(dict(index=index,process=proc['name'],root=root,reason='inconsistent target widths'));continue
            row=backward_closure(proc['body'],root);row.update(root=root,width=next(iter(ws)));rows.append(row)
        selected.append(dict(index=index,process=proc['name'],rows=rows))
    return selected,unsupported


def render_proposal(row):
    ns=lambda xs:'['+';'.join(str(n)+'%nat' for n in xs)+']'
    return ('{|kept_roots:='+ns(row['kept'])+';observed_roots:='+ns(row['observed'])+
        f';wanted_outputs:=[({row["width"]}%nat,{row["root"]}%nat)]|}}')


def proposal(profile):
    known.completion_source(profile)  # Validate Coq symbols/imports.
    b=profile['ast'];p=b['program'];ast=adapter.load_ast(adapter.ROOT/b['file'])
    selected,unsupported=analyze(ast);imports=[b['module'],*b.get('program_imports',[])]
    lines=['From Coq Require Import List Bool PeanoNat.',
      'Require Import Lang.ExtendedSV Lang.ExtendedSVDependencyPropagation',
      ' Lang.ExtendedSVOutputDependencySlice '+' '.join(imports)+'.',
      'Import ListNotations ExtendedSV ExtendedSVDependencyPropagation ExtendedSVOutputDependencySlice.']
    entries=[]
    for entry in selected:
        actual=ast['module']+'.'+entry['process'];index=entry['index']
        lines += [f'Lemma actual_registration_{index} : nth_error(processes {p}){index}%nat=Some {actual}.',
            'Proof. reflexivity. Qed.']
        proposals=[]
        for row in entry['rows']:
            proposals.append(render_proposal(row))
        entries.append('('+actual+',['+';'.join(proposals)+'])')
    lines += ['Definition candidates : list(Process*list OutputSliceProposal) := ['+';'.join(entries)+'].',
        'Goal True. let flags:=eval vm_compute in',
        f' (map(fun entry=>map(slice_dependencyb {p}(fst entry))(snd entry))candidates) in',
        ' idtac "SLICE_DEPENDENCY_FLAGS" flags. exact I. Qed.',
        f'Local Opaque {p} candidates.',
        f'Definition actual_dependency_catalog := checked_slice_catalog {p} candidates.',
        f'Theorem actual_catalog_sound : CatalogSound {p} actual_dependency_catalog.',
        f'Proof. exact(checked_output_slice_catalog {p} candidates). Qed.',
        'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_0". exact I. Qed.',
        'Print Assumptions actual_catalog_sound.']
    return ast,selected,unsupported,'\n'.join(lines)+'\n'


def parse_flags(log,selected):
    matches=re.findall(r'^SLICE_DEPENDENCY_FLAGS\s+(\[.*?\])\s*(?=Chars|\Z)',log,re.M|re.S)
    if len(matches)!=1:raise ValueError('missing or ambiguous checked row flags')
    body=matches[0].strip().replace(';',',')
    if re.sub(r'true|false|[\[\],\s]','',body):raise ValueError('invalid Coq flag list')
    flags=json.loads(body)
    if len(flags)!=len(selected) or any(len(xs)!=len(row['rows']) for xs,row in zip(flags,selected)):
        raise ValueError('checked rows do not align with actual candidates')
    return flags


def check(profile,output,timeout=1200):
    output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    ast,selected,unsupported,text=proposal(profile);output.mkdir(parents=True)
    path=output/'DependencySlices.v';path.write_text(text)
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedDependencySlices']
    r=dict(accepted=False,actual_program=profile['ast']['program'],ast_sha256=ast['source_sha256'],
      source_sha256=hashlib.sha256(text.encode()).hexdigest(),candidates=selected,unsupported=unsupported,
      complete_original_catalog=False,original_full_phase_proved=False,new_global_invariant_synthesized=False,
      itree_refinement_proved=False,llm_calls=0)
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    r.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        checked=parse_flags(c.stdout,selected);r['checked_flags']=checked
        r['checked_rows']=sum(sum(xs) for xs in checked);r['rejected_rows']=sum(len(xs)-sum(xs) for xs in checked)
        r['assumptions_closed']=scalar.audit_output(c.stdout,1)
        remaining=deadline-time.monotonic()
        if r['assumptions_closed'] and remaining>0:
            ks=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedDependencySlices.DependencySlices'],output/'coqchk.log',remaining)
            r.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    r['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(r,indent=2)+'\n');return r


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--profile',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    result=check(json.loads(a.profile.read_text()),a.output)
    print(json.dumps({k:v for k,v in result.items() if k not in ('candidates','unsupported','checked_flags')},indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
