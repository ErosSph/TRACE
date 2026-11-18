"""Generate a sound catalog in original comb order, preserving original LFP fuel.

Fallback summaries, scalar-leaf shapes and checked per-output slices are selected
by syntax/checks, not CPU names or hand-written lists of exceptional processes.
Normalized stability is NOT yet raw-state LFP or phase legality.
"""
from __future__ import annotations
import argparse,hashlib,json,re,time
from pathlib import Path
import cpu_auto_adapter as adapter
import cpu_known_producers as known
import cpu_output_dependency_slices as slices
import cpu_scalar_captures as scalar
from cpu_certificate_acceptance import run_stage


def proposal(profile,cache_rows=False,shard_size=0,whole_node_cap=0,fast_converge=False):
    if type(cache_rows)is not bool:raise ValueError('catalog cache mode must be boolean')
    if type(shard_size)is not int or shard_size<0:raise ValueError('shard size must be a natural number')
    if shard_size:cache_rows=True
    known.completion_source(profile)
    b=profile['ast'];p=b['program'];ast=adapter.load_ast(adapter.ROOT/b['file'])
    sliced,unsupported=slices.analyze(ast);sliced={x['index']:x['rows'] for x in sliced}
    imports=[b['module'],*b.get('program_imports',[])]
    lines=['From Coq Require Import List Bool PeanoNat.',
      'Require Import Lang.ExtendedSV Lang.ExtendedSVExprAgreement Lang.ExtendedSVKnownInputs',
      ' Lang.ExtendedSVDependencyPropagation Lang.ExtendedSVDependencyCatalog',
      ' Lang.ExtendedSVOutputDependencySlice '+' '.join(imports)+'.',
      'Import ListNotations ExtendedSV ExtendedSVExprAgreement ExtendedSVKnownInputs',
      ' ExtendedSVDependencyPropagation ExtendedSVDependencyCatalog ExtendedSVOutputDependencySlice.']
    if fast_converge:
        lines[1]+=' Lang.ExtendedSVFastConvergence';lines.append('Import ExtendedSVFastConvergence.')
    entries=[];metadata=[];metadata_skipped=[]
    for index,proc in enumerate(ast['processes']):
        if proc['kind']!='Combinational':continue
        actual=ast['module']+'.'+proc['name'];candidates=['WholeSummary']
        leafs=sorted({(int(n.args[2].args[0].name),adapter.root_of(n.args[2]))
            for n in adapter.walk(proc['body']) if n.name=='SAssign' and n.args[2].name=='LVar'})
        if whole_node_cap and len(leafs)==1 and all(n.args[2].name=='LVar' for n in adapter.walk(proc['body']) if n.name=='SAssign') \
                and sum(1 for _ in adapter.walk(proc['body']))>whole_node_cap:
            # default-off candidate selection (single written scalar root with a ScalarLeaf proposal covering it): WholeSummary is an untrusted proposal; on very large
            # bodies its check can cost ~1000 s. The remaining proposals are still checked, and the
            # catalog convergence/writer-coverage checks below decide whether the result suffices.
            candidates.remove('WholeSummary');metadata_skipped.append(index)
        candidates += [f'(ScalarLeaf {w}%nat {r}%nat)' for w,r in leafs]
        candidates += ['(OutputSlice '+slices.render_proposal(row)+')' for row in sliced.get(index,[])]
        entries.append('('+actual+',['+';'.join(candidates)+'])')
        metadata.append(dict(index=index,process=proc['name'],scalar_leaf_candidates=leafs,
            slice_candidates=len(sliced.get(index,[]))))
    if shard_size:
        # Default-off. Same final statements: candidates is the concatenation of
        # the shards, actual_catalog the concatenation of the shard catalogs, and
        # actual_catalog_value_checked equates it to the unsharded definition.
        shards=[entries[i:i+shard_size] for i in range(0,len(entries),shard_size)]
        lines += [f'Definition candidates_{i} : list(Process*list DependencyProposal) := ['+';'.join(sh)+'].' for i,sh in enumerate(shards)]
        lines += ['Definition candidates : list(Process*list DependencyProposal) := '+' ++ '.join(f'candidates_{i}' for i in range(len(shards)))+'.',
          f'Lemma original_order : map fst candidates=filter is_comb(processes {p}).',
          'Proof. reflexivity. Qed.',
          f'Lemma cdc_app a b : checked_dependency_catalog {p}(a++b)=checked_dependency_catalog {p} a++checked_dependency_catalog {p} b.',
          'Proof. unfold checked_dependency_catalog. apply map_app. Qed.']
        for i in range(len(shards)):
            lines += [f'Definition catalog_{i} := Eval vm_compute in checked_dependency_catalog {p} candidates_{i}.',
              f'Lemma shard_{i} : catalog_{i}=checked_dependency_catalog {p} candidates_{i}.','Proof. vm_compute. reflexivity. Qed.']
        lines += ['Definition actual_catalog := '+' ++ '.join(f'catalog_{i}' for i in range(len(shards)))+'.']
    else:
      lines += ['Definition candidates : list(Process*list DependencyProposal) := ['+';'.join(entries)+'].',
      f'Lemma original_order : map fst candidates=filter is_comb(processes {p}).',
      'Proof. reflexivity. Qed.',
      f'Definition actual_catalog := '+('Eval vm_compute in 'if cache_rows else'')+f'checked_dependency_catalog {p} candidates.']
    if cache_rows:
        lines += [f'Lemma actual_catalog_value_checked : actual_catalog=checked_dependency_catalog {p} candidates.',
          ('Proof. unfold actual_catalog,candidates. repeat rewrite cdc_app. '+' '.join(f'rewrite <- shard_{i}.' for i in range(len(shards)))+' reflexivity. Qed.'
           if shard_size else 'Proof. vm_compute. reflexivity. Qed.')]
    lines += [
      f'Lemma actual_order : map fst actual_catalog=filter is_comb(processes {p}).',
      ('Proof. rewrite actual_catalog_value_checked;unfold checked_dependency_catalog. rewrite map_map. exact original_order. Qed.'if cache_rows else
       'Proof. unfold actual_catalog,checked_dependency_catalog. rewrite map_map. exact original_order. Qed.'),
      *((f'Definition writer_coverage := covers_fastb {p} actual_catalog.',) if fast_converge else (
      f'Definition writer_coverage := forallb(fun root=>existsb(fun wr=>Nat.eqb(snd wr)root)(catalog_outputs actual_catalog))',
      f' (flat_map process_writers(filter is_comb(processes {p}))).',)),
      'Goal True. let payload:=eval vm_compute in',
      (f' (let catalog:=actual_catalog in (fast2_convergesb {p} catalog,writer_coverage,' if fast_converge else f' (let catalog:=actual_catalog in (catalog_convergesb {p} catalog,writer_coverage,'),
      f' lfp_fuel {p},length catalog,length(catalog_outputs catalog))) in',
      ' lazymatch payload with (?stable,?covered,?budget,?count,?outputs)=>',
      ' idtac "CATALOG_CONVERGES" stable;idtac "CATALOG_COVERS_WRITERS" covered;',
      ' idtac "CATALOG_BUDGET" budget;idtac "CATALOG_PROCESSES" count;idtac "CATALOG_OUTPUTS" outputs end. exact I. Qed.',
      f'Local Opaque {p} candidates actual_catalog.',
      f'Theorem actual_catalog_sound : CatalogSound {p} actual_catalog.',
      ('Proof. rewrite actual_catalog_value_checked;exact(checked_dependency_catalog_sound '+p+' candidates). Qed.'if cache_rows else
       f'Proof. exact(checked_dependency_catalog_sound {p} candidates). Qed.'),
      'Theorem actual_original_budget_when_checked :',
      f' catalog_convergesb {p} actual_catalog=true ->forall s,',
      f' InputsAgree(comb_iter {p}(lfp_fuel {p})s)(comb_iter {p}(S(lfp_fuel {p}))s)(catalog_outputs actual_catalog).',
      f'Proof. exact(original_budget_catalog_agreement {p} actual_catalog actual_order actual_catalog_sound). Qed.']
    exports=(('actual_catalog_value_checked',)if cache_rows else())+('actual_catalog_sound','actual_original_budget_when_checked')
    for i,name in enumerate(exports):
        lines += [f'Goal True. idtac "AUTO_ADAPTER_ASSUMPTIONS_{i}". exact I. Qed.','Print Assumptions '+name+'.']
    if metadata_skipped:
        for m in metadata:
            if m['index'] in metadata_skipped:m['whole_summary_skipped']=True
    return ast,metadata,unsupported,'\n'.join(lines)+'\n'


def parse(log):
    result={}
    for key in ('CONVERGES','COVERS_WRITERS','BUDGET','PROCESSES','OUTPUTS'):
        matches=re.findall(r'^CATALOG_'+key+r'\s+(true|false|\d+)\s*$',log,re.M)
        if len(matches)!=1:raise ValueError('missing/ambiguous catalog metadata '+key)
        value=matches[0]
        if key in ('CONVERGES','COVERS_WRITERS'):
            if value not in ('true','false'):raise ValueError('invalid Boolean metadata')
            value=value=='true'
        else:value=int(value)
        result[key.lower()]=value
    return result


def check(profile,output,timeout=1200,cache_rows=False,shard_size=0,whole_node_cap=0,fast_converge=False):
    output=Path(output)
    if output.exists():raise ValueError('use a fresh result directory')
    ast,processes,unsupported,text=proposal(profile,cache_rows,shard_size,whole_node_cap,fast_converge);output.mkdir(parents=True)
    source=output/'Catalog.v';source.write_text(text)
    flags=list(adapter.framework.FLAGS)
    for e in profile.get('coq_load_paths',[]):flags+=['-R',e['directory'],e['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedDependencyCatalog']
    report=dict(accepted=False,actual_program=profile['ast']['program'],ast_sha256=ast['source_sha256'],
      source_sha256=hashlib.sha256(text.encode()).hexdigest(),processes=processes,unsupported_slices=unsupported,
      normalized_outputs_stable_proved=False,original_full_phase_proved=False,
      new_global_invariant_synthesized=False,itree_refinement_proved=False,llm_calls=0,cache_rows=cache_rows)
    if shard_size:report['shard_size']=shard_size
    if whole_node_cap:report['whole_node_cap']=whole_node_cap
    if fast_converge:report['fast_converge']=True
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(adapter.ROOT/'_opam/bin/coqc'),'-time',*flags,str(source.resolve())],output/'coqc.log',timeout)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coqc_seconds=time.monotonic()-start)
    if c.returncode==0:
        report['metadata']=parse(c.stdout)
        if report['metadata']['processes']!=len(processes):raise ValueError('original order count mismatch')
        report['assumptions_closed']=scalar.audit_output(c.stdout,3 if (cache_rows or shard_size) else 2)
        remaining=deadline-time.monotonic()
        if report['assumptions_closed'] and remaining>0:
            ks=time.monotonic()
            k,t=run_stage([str(adapter.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
              'GeneratedDependencyCatalog.Catalog'],output/'coqchk.log',remaining)
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,coqchk_seconds=time.monotonic()-ks,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--profile',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--shard-size',type=int,default=0,help='default-off: split catalog into shards of this many processes')
    parser.add_argument('--whole-node-cap',type=int,default=0,help='default-off: skip WholeSummary proposal for bodies with more AST nodes')
    parser.add_argument('--fast-converge',action='store_true',help='default-off: evaluate convergence with Lang.ExtendedSVFastConvergence')
    parser.add_argument('--timeout',type=int,default=1200);a=parser.parse_args()
    result=check(json.loads(a.profile.read_text()),a.output,a.timeout,False,a.shard_size,a.whole_node_cap,a.fast_converge)
    print(json.dumps({k:v for k,v in result.items() if k not in ('processes','unsupported_slices')},indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
