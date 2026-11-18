"""Infer validity companions from raw RTL capture/hold/kill expressions.

No old INV, architectural mapping, pending definition or CPU lemma is read.
The generated theorem proves conditional *actual phase* coverage. Its upstream
label premises, admission order and commit binding are NOT discharged here.
"""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_origins as origins
from cpu_certificate_acceptance import run_stage


def is_var(e,width,root=None):
    return e.name=='EVar'and e.args[0].name==str(width)and(root is None or e.args[1].name==str(root))


def is_const(e,width,value):
    return e.name=='EConst'and e.args[0].name==str(width)and e.args[1].name==str(value)


def hold_valid(e,root):
    if is_var(e,1,root)or is_const(e,1,0):return True
    return e.name=='ECond'and e.args[0].name=='1'and all(hold_valid(x,root)for x in e.args[2:])


def pair_rule(word,valid,carrier,validroot):
    if is_const(valid,1,0):return dict(proof='apply CoveredInvalid.',captures=0,sources=[])
    if is_var(word,32,carrier):
        if hold_valid(valid,validroot):return dict(proof='apply CoveredLeaf.',captures=0,sources=[])
        return None
    if is_var(word,32)and is_const(valid,1,1):
        return dict(proof='apply CoveredLeaf.',captures=1,sources=[int(word.args[1].name)])
    if word.name==valid.name=='ECond'and word.args[0].name=='32'and valid.args[0].name=='1'and word.args[1]==valid.args[1]:
        yes=pair_rule(word.args[2],valid.args[2],carrier,validroot)
        no=pair_rule(word.args[3],valid.args[3],carrier,validroot)
        if yes is not None and no is not None:
            return dict(proof='apply CoveredCond.\n'+yes['proof']+'\n'+no['proof'],
                captures=yes['captures']+no['captures'],sources=sorted(set(yes['sources']+no['sources'])))
    return None


def all_copy(e):
    """Every leaf of the captured word is a plain 32-bit signal copy (AllCopy in Coq)."""
    if e.name=='EVar'and e.args[0].name=='32':return True
    return e.name=='ECond'and e.args[0].name=='32'and all_copy(e.args[2])and all_copy(e.args[3])


def subterms(t):
    yield t
    for a in getattr(t,'args',()):
        if hasattr(a,'name')and hasattr(a,'args'):yield from subterms(a)


def mentions(t,width,root):
    return any(x.name=='EVar'and x.args[0].name==str(width)and x.args[1].name==str(root)for x in subterms(t))


def kill_counters(ast,plan,carrier):
    """Predicate-validity rule: a registered counter C masks consumers of the carrier,
    `ECond _ (URedOr C) 0 (... carrier ...)`; the slot is valid exactly when C = 0."""
    found={}
    for process in ast['processes']:
        for t in subterms(process['body']):
            if t.name=='ECond'and len(t.args)==4:
                g=t.args[1]
                if g.name=='EUnary'and g.args[1].name=='URedOr'and g.args[2].name=='EVar':
                    var=g.args[2];zero=t.args[2]
                    c=int(var.args[1].name);w=int(var.args[0].name)
                    if zero.name=='EConst'and zero.args[1].name=='0'and mentions(t.args[3],32,carrier)\
                       and c in plan['sequential_state_roots']and c!=carrier:
                        found[c]=w
    return found


def discover(ast):
    plan=origins.pending.analyze(ast);pairs=[];residuals=[]
    for slot in plan['slots']:
        candidates=[];carrier=slot['carrier']
        word=origins.pending.rtl.Parser(slot['capture']['next_expression']).complete()
        for peer in plan['scalar_transitions']:
            if peer['width']!=1 or peer['process']!=slot['capture']['process']or peer['events']!=slot['capture']['events']:continue
            valid=origins.pending.rtl.Parser(peer['next_expression']).complete()
            rule=pair_rule(word,valid,carrier,peer['root'])
            if rule is not None and rule['captures']:
                candidates.append(dict(carrier=carrier,valid_root=peer['root'],process=peer['process'],
                    word_expression=slot['capture']['next_expression'],valid_expression=peer['next_expression'],**rule))
        if not candidates and all_copy(word):
            counters=kill_counters(ast,plan,carrier)
            if len(counters)==1:
                (c,w),=counters.items()
                candidates.append(dict(carrier=carrier,valid_root=c,valid_width=w,predicate='zero',kind='kill_counter',
                    process=None,word_expression=slot['capture']['next_expression'],valid_expression=None,
                    proof='',captures=0,sources=[]))
        if len(candidates)==1:pairs+=candidates
        else:residuals.append(dict(carrier=carrier,reason='missing or ambiguous capture/hold/kill validity companion',
            candidates=candidates,empty_fallback=False))
    return dict(pairs=pairs,residuals=residuals,old_inv_read=False,old_pending_read=False,
        upstream_validity_proved=False,global_inv_proved=False,itree_refinement_proved=False)


def render(ast_path,ast_module):
    ast,profile,paths=origins.raw_binding(ast_path,ast_module);data=discover(ast)
    if not data['pairs']:raise ValueError('no unique supported validity pair; no empty fallback')
    selected=sorted({r for pair in data['pairs']for r in(pair['carrier'],pair['valid_root'])})
    _,residuals,outputs,source,count=origins.expressions.proposal(profile,selected)
    if residuals:raise ValueError('scalar compiler residual: '+json.dumps(residuals))
    program=profile['ast']['program'];predicate=any(p.get('kind')=='kill_counter'for p in data['pairs'])
    lines=[
        'Require Import Lang.ExtendedSVInstructionOrigin Lang.ExtendedSVOriginCoverage Lang.ExtendedSVScalarHistory'
        +(' Lang.ExtendedSVOriginCoveragePredicate.'if predicate else'.'),
        'Import ExtendedSVInstructionOrigin ExtendedSVOriginCoverage ExtendedSVScalarHistory'
        +(' ExtendedSVOriginCoveragePredicate.'if predicate else'.'),
        f'Local Opaque {program}.']
    procs={row['root']:row['process']for row in outputs}
    for pair in data['pairs']:
        if pair.get('kind')=='kill_counter':
            r=pair['carrier'];v=pair['valid_root'];w=pair['valid_width'];proc=ast['module']+'.'+procs[v];stem=f'coverage_{r}_{v}'
            lines += [f'Lemma {stem}_checked : AllCopy root_{r}_expression.',
                f'Proof. unfold root_{r}_expression. repeat constructor. Qed.',
                f'Lemma {stem}_valid_self_width : self_widthb {w} {v} root_{v}_expression=true.',
                'Proof. vm_compute. reflexivity. Qed.',
                f'Definition {stem}_valid_certificate : ScalarCertificate {program} {v} {w} {proc} root_{v}_expression :=',
                f' Build_ScalarCertificate _ _ _ _ _ root_{v}_comb_frame {stem}_valid_self_width root_{v}_expression_phase.',
                f'Theorem {stem}_actual_phase (Label:Type) ev pre (old:option Label) sampled :',
                f' changed_signal ev<>{v}%nat ->',
                f' (norm {w}(read_signal pre {v})=0%Z ->exists label,old=Some label) ->',
                f' (forall source,copy_source(phase_driven_state {program} ev pre)root_{r}_expression=Some source ->',
                f'  norm {w}(eval_expr(phase_driven_state {program} ev pre)root_{v}_expression)=0%Z ->',
                '  exists label,sampled source=Some label) ->',
                f' norm {w}(read_signal(PhaseSemantics {program} ev pre){v})=0%Z ->',
                f' exists label,@phase_origin Label {program} {proc} root_{r}_expression ev pre old sampled=Some label.',
                f'Proof. exact(@actual_phase_coverage_pred Label {program} {v} {w} (fun z=>z=0%Z) {proc}',
                f' root_{r}_expression root_{v}_expression {stem}_checked {stem}_valid_certificate ev pre old sampled). Qed.']
            for suffix in ['checked','actual_phase']:
                lines += [f'Print Assumptions {stem}_{suffix}.'];count+=1
            continue
        r=pair['carrier'];v=pair['valid_root'];proc=ast['module']+'.'+pair['process'];stem=f'coverage_{r}_{v}'
        lines += [f'Lemma {stem}_checked : CopyCovered root_{r}_expression root_{v}_expression.',
            f'Proof. unfold root_{r}_expression,root_{v}_expression. {pair["proof"]} Qed.',
            f'Lemma {stem}_valid_self_width : self_widthb 1 {v} root_{v}_expression=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Definition {stem}_valid_certificate : ScalarCertificate {program} {v} 1 {proc} root_{v}_expression :=',
            f' Build_ScalarCertificate _ _ _ _ _ root_{v}_comb_frame {stem}_valid_self_width root_{v}_expression_phase.',
            f'Theorem {stem}_actual_phase (Label:Type) ev pre (old:option Label) sampled :',
            f' changed_signal ev<>{v}%nat ->',
            f' (norm 1(read_signal pre {v})<>0%Z ->exists label,old=Some label) ->',
            f' (forall input,copy_source(phase_driven_state {program} ev pre)root_{r}_expression=Some input ->',
            f'  norm 1(eval_expr(phase_driven_state {program} ev pre)root_{v}_expression)<>0%Z ->',
            '  exists label,sampled input=Some label) ->',
            f' norm 1(read_signal(PhaseSemantics {program} ev pre){v})<>0%Z ->',
            f' exists label,@phase_origin Label {program} {proc} root_{r}_expression ev pre old sampled=Some label.',
            f'Proof. exact(@actual_phase_coverage Label {program} {v} {proc}',
            f' root_{r}_expression root_{v}_expression {stem}_checked {stem}_valid_certificate ev pre old sampled). Qed.']
        for suffix in ['checked','actual_phase']:
            lines += [f'Print Assumptions {stem}_{suffix}.'];count+=1
    return dict(**data,coq_load_paths=paths,ast_sha256=ast['source_sha256'],audited_exports=count),source+'\n'+'\n'.join(lines)+'\n'


def check(ast_path,ast_module,output,timeout=1200):
    if not 0<timeout<=1200:raise ValueError('native budget must be <=1200 seconds')
    data,source=render(ast_path,ast_module);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    path=output/'Validity.v';path.write_text(source);(output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(origins.pending.rtl.framework.FLAGS)
    for b in data['coq_load_paths']:flags+=['-R',b['directory'],b['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedValidity']
    start=time.monotonic();deadline=start+timeout
    c,t=run_stage([str(origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(path.resolve())],output/'coqc.log',timeout)
    report=dict(accepted=False,scope='raw-RTL validity pairing and conditional actual phase coverage',
        old_inv_read=False,old_pending_read=False,coqc_exit=c.returncode,coqc_timed_out=t,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),ast_sha256=data['ast_sha256'],
        pair_count=len(data['pairs']),upstream_validity_proved=False,global_inv_proved=False,itree_refinement_proved=False)
    if c.returncode==0:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and 'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        if closed and time.monotonic()<deadline:
            k,t=run_stage([str(origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedValidity.Validity'],
                output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0)
    report['overall_seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(path.with_suffix('.vo').read_bytes()).hexdigest()
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--ast',type=Path,required=True)
    p.add_argument('--ast-module',required=True);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output)
    print(json.dumps(r,indent=2));raise SystemExit(0 if r['accepted']else 1)
