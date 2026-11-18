"""RTL-only pending compiler front end; no previous invariant is an input.

Emit a concrete nonempty-slot pending candidate only after structural role
checks, plus the missing semantic obligations. A checked capacity lemma is
NEVER reported as architectural pending correspondence or a complete INV.
"""
import argparse,copy,hashlib,json,time
from pathlib import Path
import cpu_pending_validity as validity
import cpu_pending_fetch_pairs as fetch
import cpu_pending_metadata_copies as metadata
import cpu_pending_recipe_coverage as origin_coverage
from cpu_certificate_acceptance import run_stage


def synthesize(ast):
    pending=validity.origins.pending;plan=pending.analyze(ast);coverage=validity.discover(ast)
    fetch_pairs=fetch.discover(ast)
    refined=copy.deepcopy(plan);bindings={row['carrier']:row for row in coverage['pairs']}
    pc_bindings={row['carrier']:row for row in fetch_pairs['pairs']}
    scalars={row['root']:row for row in plan['scalar_transitions']}
    for slot in refined['slots']:
        row=bindings.get(slot['carrier'])
        slot['valid_candidates']=[]if row is None else[row['valid_root']]
        # Identical payload copies are not independent PC-role evidence.
        expression=validity.origins.pending.rtl.Parser(slot['capture']['next_expression']).complete()
        duplicates=[]
        for pc in slot['pc_candidates']:
            peer=validity.origins.pending.rtl.Parser(scalars[pc]['next_expression']).complete()
            def rename(e):
                rtl=validity.origins.pending.rtl
                if e.name=='EVar'and e.args[0].name=='32'and e.args[1].name==str(pc):
                    return rtl.Term('EVar',(rtl.Term('32'),rtl.Term(str(slot['carrier']))))
                return rtl.Term(e.name,tuple(rename(a)for a in e.args))
            if rename(peer)==expression:duplicates.append(pc)
        slot['duplicate_payload_peers']=duplicates
        slot['pc_candidates']=[p for p in slot['pc_candidates']if p not in duplicates]
        if slot['carrier']in pc_bindings:
            slot['pc_candidates']=[pc_bindings[slot['carrier']]['pc_root']]
    order=pending.candidate_order(refined)
    candidate=pending.render_candidate(refined)
    metadata_relations=metadata.discover(ast)
    covered_fields=origin_coverage.discover(ast,metadata_relations,coverage)
    obligations=[dict(id='acceptance_identity',needs='environment response/ROM word and PC address relation'),
        dict(id='carrier_completeness',needs='include decoded metadata and FIFO tokens, not only full-word registers'),
        dict(id='pc_binding',needs='prove paired PC belongs to captured instruction; same process is not sufficient'),
        dict(id='validity_coverage',needs='derive upstream known labels at each enabled capture'),
        dict(id='age_and_retirement',needs='unique admission history, real commit owner and in-order removal'),
        dict(id='flush_cancel',needs='derive exact youngest cancellation suffix and rollback from real RTL'),
        dict(id='initialization',needs='prove original configured reset enters the generated relation'),
        dict(id='cycle_preservation',needs='prove original configured complete cycle preserves all relation fields'),
        dict(id='isa_effect',needs='prove commit corresponds to original run1 and restores architectural relation'),
        dict(id='progress',needs='derive finite waiting from original environment, not assume future correctness')]
    return dict(schema_version=1,input_boundary='raw constructor RTL only',ast_sha256=ast['source_sha256'],
        old_inv_read=False,old_pending_read=False,old_cpu_theorems_used=False,
        validity_rules=coverage,fetch_pair_rules=fetch_pairs,metadata_relations=metadata_relations,
        metadata_origin_coverage=covered_fields,
        metadata_relations_require_native_checks=True,slots=refined['slots'],candidate_order=order,
        candidate_pending_generated=candidate is not None,
        candidate_scope='physical full-word slot snapshot; PC pairing and complete ISA identity unproved',
        obligations=obligations,llm_calls=0,pending_correspondence_proved=False,
        global_inv_proved=False,itree_refinement_proved=False),candidate


def run(ast_path,ast_module,output,check=False,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    ast,profile,paths=validity.origins.raw_binding(ast_path,ast_module)
    plan,source=synthesize(ast);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    (output/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
    report={k:plan[k]for k in('input_boundary','old_inv_read','old_pending_read','old_cpu_theorems_used',
        'candidate_pending_generated','candidate_scope','llm_calls','pending_correspondence_proved','global_inv_proved','itree_refinement_proved')}
    report.update(accepted=False,native_started=False)
    if source is not None:
        path=output/'PendingCandidate.v';path.write_text(source)
        report['source_sha256']=hashlib.sha256(source.encode()).hexdigest()
        if check:
            flags=list(validity.origins.pending.rtl.framework.FLAGS)+['-R',str(output.resolve()),'GeneratedPendingCandidate']
            start=time.monotonic();deadline=start+timeout
            c,t=run_stage([str(validity.origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
            report.update(native_started=True,coqc_exit=c.returncode,coqc_timed_out=t)
            if c.returncode==0:
                closed=c.stdout.count('Closed under the global context')==1 and 'Axioms:'not in c.stdout
                report['assumptions_closed']=closed
                if closed and time.monotonic()<deadline:
                    k,t=run_stage([str(validity.origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,
                        '-norec','GeneratedPendingCandidate.PendingCandidate'],output/'coqchk.log',deadline-time.monotonic())
                    report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
            report['overall_seconds']=time.monotonic()-start
            if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    if not report['native_started']:report['residual']='no unique candidate'if source is None else'native check not requested'
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--check',action='store_true');a=p.parse_args()
    r=run(a.ast,a.ast_module,a.output,a.check);print(json.dumps(r,indent=2))
    raise SystemExit(0 if not a.check or r['accepted']else 1)
