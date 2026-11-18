"""Exact controller-to-mux data paths, with checked alias connections."""
import cpu_selector_sources as wires
rtl=wires.rtl
cases=wires.selectors.branches.cases

def select(expression,width,sw,selector,code):
    if expression.name!='ECond':return expression,'apply Leaf.'
    w,g,yes,no=expression.args
    if w.name!=str(width)or g.name!='EBinary'or g.args[0].name!='1'or g.args[1].name!='BEq':
        raise ValueError('non-case branch in data mux')
    a,b=g.args[2:]
    if a!=rtl.Parser(f'(EVar {sw} {selector})').complete()or b.name!='EConst'or b.args[0].name!=str(sw):
        raise ValueError('mux uses a different selector or width')
    take=int(b.args[1].name)%(1<<sw)==code
    leaf,proof=select(yes if take else no,width,sw,selector,code)
    return leaf,('eapply Yes;[reflexivity|]. 'if take else'eapply No;[vm_compute;discriminate|]. ')+proof

def discover(ast,rows):
    result=[]
    for row in rows:
        s=row['selector'];matches=[]
        for proc in ast['processes']:
            p=cases.case_plan(proc)
            if p is None or p[0]!=32:continue
            scr=cases.unwrap(proc['body']).args[0]
            if scr.name!='EVar'or scr.args[0].name!=str(s['width']):continue
            root=int(scr.args[1].name);control=wires.trace(ast,s['width'],root)
            if control['terminal']!=s['root']:continue
            leaf,proof=select(p[2],32,s['width'],root,row['code'])
            if leaf.name!='EVar'or leaf.args[0].name!='32':continue
            data=wires.trace(ast,32,int(leaf.args[1].name))
            if data['kind']in ['cycle','multiple_writers']or data['terminal']==p[1]:continue
            matches.append(dict(process=proc['name'],output=p[1],selector=root,control=control,
                leaf=rtl.render(leaf),proof=proof,data=data,code=row['code'],sw=s['width']))
        if len(matches)!=1:raise ValueError('no unique physical data mux for selected controller')
        result.append(matches[0])
    return result

def render(ast_path,module,rows):
    ast,profile,_=wires.selectors.origin.raw_binding(ast_path,module)
    paths=discover(ast,rows);program=profile['ast']['program']
    combs=[p for p in ast['processes']if p['kind']=='Combinational']
    edges={e['root']:e for r in paths for path in [r['control'],r['data']]for e in path['edges']}
    blocks=[];ports=[]
    for root,e in sorted(edges.items()):
        proc=next(p for p in combs if p['name']==e['process']);st=cases.unwrap(proc['body'])
        blocks.append(dict(process=proc['name'],comb_index=combs.index(proc),assignments=[st]))
        ports.append(dict(block_index=len(blocks)-1,assignment_index=0,process=proc['name'],width=e['width'],output_root=root,rhs=st.args[1]))
    from cpu_rf_read_ports import render as render_ports
    source='Module W.\n'+render_ports(profile['ast'],ast,dict(blocks=blocks,ports=ports,residuals=[]),opaque_single=True)+'\nEnd W.\n'
    muxes={r['output']:r for r in paths}
    for root,r in muxes.items():
        text,_=cases.render(ast_path,module,r['process'],structural=True)
        source+=f'Module M{root}.\n{text}\nEnd M{root}.\n'
    source+=f'''From Coq Require Import ZArith.
Require Import {module} Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVSelectedData.
Import ExtendedSV ExtendedSVWordInvariant ExtendedSVSelectedData.
Local Opaque {program}.
'''
    indices={p['output_root']:i for i,p in enumerate(ports)}
    def term(path,width):
        result='eq_refl'
        for e in reversed(path['edges']):
            step=f'(eq_trans(W.port_{indices[e["root"]]}_lfp seed fixed HL)(norm_idempotent {width}(read_signal fixed {e["parent"]})))'
            result=f'(eq_trans {step} {result})'
        return result
    for i,r in enumerate(paths):
        root=r['output'];sw=r['sw'];code=r['code']
        source+=f'''Lemma data_certificate_{i}:Selects 32 {sw} {r['selector']} {code} M{root}.case_expression {r['leaf']}.
Proof. unfold M{root}.case_expression. {r['proof']} Qed.
Theorem data_{i}_lfp seed fixed:CombLFP {program} seed fixed ->
 norm {sw}(read_signal fixed {r['control']['terminal']})={code}%Z ->
 norm 32(read_signal fixed {root})=norm 32(read_signal fixed {r['data']['terminal']}).
Proof. intros HL HS;pose proof {term(r['control'],sw)} as HW.
rewrite(M{root}.case_actual_lfp seed fixed HL).
rewrite(selected_data _ _ _ _ _ _ data_certificate_{i} fixed(eq_trans HW HS)).
change(norm 32(norm 32(read_signal fixed {r['data']['input']}))=norm 32(read_signal fixed {r['data']['terminal']})).
rewrite norm_idempotent;exact {term(r['data'],32)}. Qed.
'''
    return source,paths
