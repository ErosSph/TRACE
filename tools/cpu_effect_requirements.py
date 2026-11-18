"""Compile complete effect trees to checked, state-threaded value conditions.

Reference values remain parameters. This preserves blocking temporaries, NBA
capture times and case priority; it does not infer ISA token ownership.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_operand_routes as routes
from cpu_certificate_acceptance import run_stage
rtl=origin.pending.rtl


class Compiler:
    def __init__(self):
        self.lines=[];self.memo={}

    def compile(self, effect):
        key=rtl.render(effect)
        if key in self.memo:return self.memo[key]
        n,a=effect.name,effect.args
        if n=='FEmpty':
            expr,wp,proof='FEmpty','identity_wp','empty_correct'
        elif n=='FAssign':
            args=' '.join(rtl.render(x)for x in a)
            expr=key;wp='assignment_wp '+args;proof='assignment_correct '+args
        elif n=='FIf':
            y=self.compile(a[1]);no=self.compile(a[2]);g=rtl.render(a[0])
            expr=f'FIf {g} {y} {no}'
            wp=f'conditional_wp {g} {y}_wp {no}_wp'
            proof=f'conditional_correct {g} _ _ _ _ {y}_correct {no}_correct'
        elif n=='FSeq':
            children=[self.compile(e)for e in a[0].args]
            expr='FSeq ['+';'.join(children)+']'
            wp='sequence_wp ['+';'.join(x+'_wp'for x in children)+']'
            proof='list_nil_correct'
            for child in reversed(children):
                proof=f'(list_cons_correct _ _ _ _ {child}_correct {proof})'
            proof='sequence_correct _ _ '+proof
        elif n=='FCase':
            scr=rtl.render(a[0]);arms=[];children=[]
            for arm in a[1].args:
                key,body=arm.args;child=self.compile(body)
                arms.append(f'({rtl.render(key)},{child})');children.append((key,child))
            expr=f'FCase {scr} ['+';'.join(arms)+']'
            transform='case_nil';proof=f'(case_nil_correct {scr})'
            for key,child in reversed(children):
                if key.name=='None':
                    transform=f'(case_default {child}_wp {transform})'
                    proof=f'(case_default_correct {scr} _ _ _ _ {child}_correct {proof})'
                elif key.name=='Some':
                    kval=rtl.render(key.args[0])
                    transform=f'(case_key {scr} {kval} {child}_wp {transform})'
                    proof=f'(case_key_correct {scr} {kval} _ _ _ _ {child}_correct {proof})'
                else:raise ValueError('unknown case key')
            wp=transform+' identity_wp';proof=f'case_correct {scr} _ _ {proof}'
        else:raise ValueError('unsupported effect constructor '+n)
        name='condition_effect_'+str(len(self.memo));self.memo[rtl.render(effect)]=name
        self.lines += [f'Definition {name}:EffectPlan:={expr}.',
            f'Definition {name}_wp:Transformer:={wp}.',
            f'Lemma {name}_correct:Correct {name} {name}_wp.',
            f'Proof. exact({proof}). Qed.']
        return name


def extend(ast,binding,analysis,source,count):
    compiler=Compiler();processes={};p=binding['program'];rows=[]
    selected={proc['name']:proc for proc,_ in analysis['plans']+analysis['effects']}
    for name,proc in selected.items():
        processes[name]=compiler.compile(rtl.effect_of(proc['body']))
    lines=['Require Import Lang.ExtendedSVEffectRequirements Ex.External.CPUReferenceCutTransfer.',
           'Import ExtendedSVEffectRequirements CPUReferenceCuts.CPUReferenceCuts CPUGeneratedJointTemplate.CPUGeneratedJointTemplate CPUReferenceCutTransfer.',*compiler.lines]
    for name,tree in processes.items():
        lines += [f'Lemma {name}_condition_checked:compile_effect(statement_fuel {p})',
            f' (process_body {ast["module"]}.{name})=Some {tree}.',
            'Proof. vm_compute. reflexivity. Qed.']
    for root in analysis['roots']:
        writers=[proc for proc in selected.values()if root in proc['writers']]
        if len(writers)!=1:raise ValueError('phase condition requires one complete writer')
        proc=writers[0];name=proc['name'];tree=processes[name]
        widths={int(node.args[2].args[0].name)for node in rtl.walk(proc['body'])
            if node.name=='SAssign'and node.args[2].name=='LVar'and rtl.root_of(node.args[2])==root}
        if len(widths)!=1:raise ValueError('unique whole-field width required')
        width=next(iter(widths));stem=f'root_{root}_effect_R'
        lines += [f'Definition {stem} ev pre expected:Prop:=',
            f' phase_wp {p} {ast["module"]}.{name} {width} {root} {tree}_wp ev pre expected.',
            f'Theorem {stem}_exact ev pre expected:changed_signal ev<>{root}%nat ->',
            f' ({stem} ev pre expected <->norm {width}(read_signal(PhaseSemantics {p} ev pre){root})=expected).',
            f'Proof. intro HE;unfold {stem};exact(phase_wp_exact {p} {ast["module"]}.{name}',
            f' {width} {root} {tree} {tree}_wp ev pre expected root_{root}_certificate',
            f' {name}_condition_checked {tree}_correct HE). Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions {stem}_exact.']
        count+=1
        lines += [f'Theorem {stem}_held_token_transfer {{Architecture Token:Type}}',
            ' (effect:Token->Architecture->option Architecture) (project:Architecture->Z)',
            ' ev pre initial advanced retiring kept added index token :',
            f' changed_signal ev<>{root}%nat ->',
            f' process_matches_states pre(phase_driven_state {p} ev pre){ast["module"]}.{name}=false ->',
            ' EffectChain effect initial retiring advanced ->',
            f' FieldAtToken effect project initial(retiring++kept)(length retiring+index)token(norm {width}(read_signal pre {root})) ->',
            f' FieldAtToken effect project advanced(kept++added)index token(norm {width}(read_signal(PhaseSemantics {p} ev pre){root})).',
            'Proof. intros HE HF HC HR.',
            f' assert(Hhold:{stem} ev pre(norm {width}(read_signal pre {root}))).',
            f' {{ unfold {stem},phase_wp;rewrite HF;split;[discriminate|reflexivity]. }}',
            f' pose proof(proj1({stem}_exact ev pre _ HE) Hhold)as HV.',
            ' rewrite HV.',
            f' exact(field_cycle effect project initial advanced retiring kept added index token',
            f' (norm {width}(read_signal pre {root})) HC HR). Qed.',
            f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{count}". exact I. Qed.',
            f'Print Assumptions {stem}_held_token_transfer.']
        count+=1;rows.append(dict(root=root,width=width,process=name,theorem=stem+'_exact',
            held_token_transfer=stem+'_held_token_transfer',actual_queue_transfer_proved=False))
    return source+'\n'+'\n'.join(lines)+'\n',count,rows,len(compiler.memo)


def check(ast_path,ast_module,output):
    # Import here to keep the existing mixed fallback free of import cycles.
    import cpu_operand_capture_proofs as captures
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,profile,paths=origin.raw_binding(ast_path,ast_module)
    roots=sorted({r['root']for r in routes.discover(ast)['routes']if r['crossed_sampling_boundary']})
    report=dict(accepted=False,roots=roots,old_inv_read=False,complete_R_generated=False,
        reference_binding_proved=False,operand_freshness_proved=False)
    if not roots:report['status']='no_copy_storage_discovered_not_a_completeness_claim'
    else:
        analysis,bad,missing=captures.mixed_analysis(ast,roots)
        if bad or missing:
            report.update(status='unsupported_complete_process',unsupported_roots=bad,unsupported_processes=missing)
        else:
            source=rtl.render_adapter(profile['ast']['module'],profile['ast']['program'],ast,analysis)
            count=3*len(analysis['plans'])+2*len(analysis['effects'])+len(roots)+len(analysis['plan_roots'])
            source,count,rows,nodes=extend(ast,profile['ast'],analysis,source,count)
            path=output/'EffectRequirements.v';path.write_text(source)
            report.update(relations=rows,transformer_nodes=nodes,audited_exports=count,
                source_sha256=hashlib.sha256(source.encode()).hexdigest())
            flags=list(rtl.framework.FLAGS)
            for row in paths:flags+=['-R',row['directory'],row['namespace']]
            flags+=['-R',str(output.resolve()),'GeneratedEffectRequirements']
            start=time.monotonic();deadline=start+1200
            c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],
                output/'coqc.log',deadline-time.monotonic())
            report.update(coqc_exit=c.returncode,coqc_timed_out=t)
            if c.returncode==0 and time.monotonic()<deadline:
                report['assumptions_closed']=origin.captures.audit_output(c.stdout,count)
                k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                    'GeneratedEffectRequirements.EffectRequirements'],output/'coqchk.log',deadline-time.monotonic())
                report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                    accepted=k.returncode==0 and report['assumptions_closed'])
            report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();result=check(a.ast,a.ast_module,a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
