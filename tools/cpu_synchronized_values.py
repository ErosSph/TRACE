"""Prove word/decoded-field coupling including zero, without external labels."""
import argparse,hashlib,json,time
from pathlib import Path
import cpu_pending_projection_origins as projections
from cpu_certificate_acceptance import run_stage
rtl=projections.rtl


class RecipeParser(rtl.Parser):
    """Extend the closed grammar locally, never mutate the RTL parser tables."""
    def parse(self):
        if self.pos<len(self.tokens):
            token=self.tokens[self.pos]
            if token in ('Hold','Capture','Unknown'):
                self.take();return rtl.Term(token)
            if token=='Select':
                self.take();return rtl.Term(token,tuple(self.parse()for _ in range(3)))
        return super().parse()


def total(recipe):
    if recipe.name=='Hold':return 'apply TotalHold.'
    if recipe.name=='Capture':return 'apply TotalCapture.'
    if recipe.name=='Select':return 'apply TotalSelect.\n'+total(recipe.args[1])+'\n'+total(recipe.args[2])
    raise ValueError('unknown path is not a total capture/hold recipe')


def pairs(rows):
    result=[]
    for i,a in enumerate(rows):
        capture=rtl.Parser(a['capture']).complete()
        if a['width']!=32 or not projections.is_hold(capture,32,a['source']):continue
        parsed=RecipeParser(a['recipe']).complete()
        try:total(parsed)
        except ValueError:continue
        for j,b in enumerate(rows):
            if a['root']!=b['root']and all(a[k]==b[k]for k in ['process','source','recipe']):result.append((i,j))
    return result


def render(ast_path,ast_module):
    ast,profile,paths=projections.origins.raw_binding(ast_path,ast_module)
    rows=projections.discover(ast)['projections'];matches=pairs(rows)
    if not matches:raise ValueError('no total same-phase word/field pair; no vacuous coupling')
    roots=sorted({rows[i]['root']for pair in matches for i in pair})
    data,source=projections.render(ast_path,ast_module,selected_roots=roots)
    rows=data['projections'];matches=pairs(rows);p=profile['ast']['program']
    lines=['Require Import Lang.ExtendedSVSynchronizedValue.',
           'Import ExtendedSVSynchronizedValue.']
    anchors=sorted({i for i,j in matches})
    for i in anchors:
        a=rows[i];root=a['root'];src=a['source']
        lines += [f'Lemma word_identity_{i} z:projection_{i}_reference z=norm 32 z.',
            f'Proof. unfold projection_{i}_reference,projection_{i}_capture,capture_value.',
            ' cbn[eval_expr]. rewrite read_signal_write_same,norm_idempotent. reflexivity. Qed.',
            f'Lemma total_recipe_{i}:TotalRecipe projection_{i}_recipe.',
            f'Proof. unfold projection_{i}_recipe. {total(RecipeParser(a["recipe"]).complete())} Qed.',
            f'Lemma word_phase_{i} ev pre (old incoming:option Z) label:',
            f' changed_signal ev<>{root}%nat ->',
            f' (forall l,old=Some l ->norm 32(read_signal pre {root})=norm 32 l) ->',
            f' (forall l,incoming=Some l ->norm 32(read_signal(phase_driven_state {p} ev pre){src})=norm 32 l) ->',
            f' projection_{i}_origin Z ev pre old incoming=Some label ->',
            f' norm 32(read_signal(PhaseSemantics {p} ev pre){root})=norm 32 label.',
            'Proof. intros HE HO HI HT.',
            f' assert(HO2:forall l,old=Some l ->norm 32(read_signal pre {root})=projection_{i}_reference l).',
            f' {{ intros l H. rewrite word_identity_{i}. exact(HO l H). }}',
            f' pose proof(projection_{i}_actual_phase Z (fun z=>z) ev pre old incoming label HE HO2 HI HT)as H.',
            f' rewrite word_identity_{i} in H. exact H. Qed.']
    for i,j in matches:
        a,b=rows[i],rows[j];proc=ast['module']+'.'+a['process'];src=a['source'];w=b['width']
        lines += [f'Lemma reference_agrees_{i}_{j} x y:norm 32 x=norm 32 y ->projection_{j}_reference x=projection_{j}_reference y.',
            f'Proof. exact(reference_word_agree {src} projection_{j}_capture {w} x y projection_{j}_inputs). Qed.',
            f'Definition coupled_value_{i}_{j}:=',
            f' @actual_coupled_phase {p} {proc} projection_{i}_recipe {a["root"]} {b["root"]} {src} {w}',
            f' projection_{j}_reference reference_agrees_{i}_{j} word_phase_{i}',
            f' (@projection_{j}_actual_phase Z (fun z=>z)) total_recipe_{i}.',
            f'Print Assumptions coupled_value_{i}_{j}.']
    data['coupled_pairs']=[dict(carrier=rows[i]['root'],target=rows[j]['root'])for i,j in matches]
    data['audited_exports']+=len(matches)
    return data,source+'\n'+'\n'.join(lines)+'\n',paths


def check(ast_path,ast_module,output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    report=dict(accepted=False,old_inv_read=False,complete_R_generated=False,
        zero_architectural_effect_proved=False,scope='same-phase word/decoded-field relation, including zero words')
    try:data,source,paths=render(ast_path,ast_module)
    except ValueError as exc:
        report.update(status='unsupported_total_coupling',residual=str(exc))
        (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report
    file=output/'SynchronizedValues.v';file.write_text(source)
    (output/'plan.json').write_text(json.dumps(data,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(output.resolve()),'GeneratedSynchronizedValues']
    start=time.monotonic();deadline=start+1200
    c,t=run_stage([str(projections.origins.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],output/'coqc.log',1200)
    report.update(coqc_exit=c.returncode,coqc_timed_out=t,coupled_pairs=data['coupled_pairs'],
        source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if c.returncode==0 and time.monotonic()<deadline:
        closed=c.stdout.count('Closed under the global context')==data['audited_exports']and'Axioms:'not in c.stdout
        report['assumptions_closed']=closed
        k,t=run_stage([str(projections.origins.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
            'GeneratedSynchronizedValues.SynchronizedValues'],output/'coqchk.log',deadline-time.monotonic())
        report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,accepted=k.returncode==0 and closed)
    report['seconds']=time.monotonic()-start
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();r=check(a.ast,a.ast_module,a.output);print(json.dumps(r,indent=2))
    raise SystemExit(0 if r['accepted']else 1)
