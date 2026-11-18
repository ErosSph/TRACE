"""Infer and prove readonly packed instruction-input storage from raw RTL.

Only banks reached by actual carrier copy-frontiers are selected. Their ROM
role is a proposal; ISA address/byte-image correspondence is not assumed.
"""
from __future__ import annotations
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origin
import cpu_instruction_word_aliases as aliases
import cpu_comb_scalar_bindings as comb
from cpu_certificate_acceptance import run_stage


def discover(ast):
    data=origin.pending.analyze(ast);slots={s['carrier']for s in data['slots']}
    frontier={int(n.args[1].name)for s in data['slots']for n in origin.pending.data_leaves(origin.pending.rtl.Parser(s['capture']['next_expression']).complete())if n.name=='EVar'}-slots
    candidates=[]
    for source in sorted(frontier):
        chain=aliases.trace(ast,source);terminal=chain['terminal']
        writers=[p for p in ast['processes']if terminal in p['writers']]
        if len(writers)!=1:continue
        proc=writers[0];body=proc['body']
        if proc['kind']!='Combinational'or body.name!='SAssign'or body.args[0].name!='false':continue
        rhs=body.args[1]
        if rhs.name!='ESel'or rhs.args[0].name!='32'or rhs.args[1].name!='EVar':continue
        width=int(rhs.args[1].args[0].name);bank=int(rhs.args[1].args[1].name)
        if width<=32 or width%32!=0:continue
        if any(p['kind']in ('Sequential','Combinational')and bank in p['writers']for p in ast['processes']):continue
        candidates.append(dict(source=source,terminal=terminal,reader_process=proc['name'],
            bank_root=bank,bank_width=width,offset=origin.pending.rtl.render(rhs.args[2]),
            address_dependencies=origin.pending.roots(rhs.args[2]),alias_chain=chain,
            original_isa_address_correspondence_proved=False))
    return candidates


def render(ast_path,ast_module):
    ast,profile,paths=origin.raw_binding(ast_path,ast_module);rows=discover(ast)
    if not rows:raise ValueError('no supported readonly packed carrier input')
    roots=sorted({r for row in rows for r in [row['terminal'],*[e['root']for e in row['alias_chain']['edges']]]})
    _,analysis,prefix=comb.proposal(profile,roots)
    if analysis['residuals']:raise ValueError('actual reader residual: '+json.dumps(analysis['residuals']))
    ports={p['output_root']:i for i,p in enumerate(analysis['ports'])}
    program=profile['ast']['program'];count=len(analysis['ports'])
    lines=['Require Import Lang.ExtendedSVReadonlyInput Lang.ExtendedSVAutoAdapterPhase Lang.ExtendedSVWordInvariant',
        ' Lang.ExtendedSVRootProjection Lang.ExtendedSVProcessSlice.',
        'Import ExtendedSVReadonlyInput ExtendedSVAutoAdapterPhase ExtendedSVWordInvariant ExtendedSVRootProjection ExtendedSVProcessSlice.']
    for i,row in enumerate(rows):
        name='rom_'+str(i);root=row['bank_root']
        lines += [f'Lemma {name}_bound : ({root}<signal_count {program})%nat.',
            'Proof. apply Nat.ltb_lt. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_comb_frame : comb_root_unwrittenb {program} {root}=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Lemma {name}_no_clocked_writers : filter is_sequential(filter(writes_rootb {root})(processes {program}))=[].',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {name}_certificate : PlanRootCertificate {program} {root} [] :=',
            f' Build_PlanRootCertificate {program} {root} [] {name}_bound {name}_comb_frame {name}_no_clocked_writers (Forall_nil _).',
            f'Definition {name}_actual_phase := readonly_phase {program} {root} {name}_certificate.',
            f'Definition {name}_actual_history := readonly_history {program} {root} {name}_certificate.',
            f'Theorem {name}_frontier_read seed fixed : CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {row["source"]})=norm 32(eval_expr fixed port_{ports[row["terminal"]]}_rhs).',
            'Proof. intro HL.']
        term=f'(port_{ports[row["terminal"]]}_lfp seed fixed HL)'
        for edge in reversed(row['alias_chain']['edges']):
            index=ports[edge['root']]
            term=f'(eq_trans (eq_trans (port_{index}_lfp seed fixed HL)(norm_idempotent 32(read_signal fixed {edge["parent"]}))) {term})'
        lines += [f' exact {term}. Qed.']
        for suffix in ['actual_phase','actual_history','frontier_read']:
            lines += [f'Print Assumptions {name}_{suffix}.'];count+=1
    source=prefix+'\n'+'\n'.join(lines)+'\n'
    return dict(ast_sha256=ast['source_sha256'],coq_load_paths=paths,candidates=rows,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),audited_exports=count,old_inv_read=False),source


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    try:data,source=render(ast_path,ast_module)
    except ValueError as error:
        report=dict(accepted=False,native_started=False,residual=str(error),old_inv_read=False,itree_refinement_proved=False)
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    path=output/'ReadonlyInputs.v';path.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(origin.pending.rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedReadonlyInputs']
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origin.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='raw readonly input phase/history and actual LFP frontier read only',
        coqc_exit=c.returncode,coqc_timed_out=t,old_inv_read=False,
        isa_memory_correspondence_proved=False,external_installer_preservation_proved=False,itree_refinement_proved=False)
    report.update(source_sha256=data['source_sha256'],ast_sha256=data['ast_sha256'])
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and 'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedReadonlyInputs.ReadonlyInputs'],output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
