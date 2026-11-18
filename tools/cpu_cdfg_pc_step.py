"""Discover the actual PC cone and prove its original phase projection.

This is a consumer of the pinned CDFG and original Coq AST, not a replacement
CPU evaluator. Controller conditions are explicit proof obligations, not Env.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import cpu_add_admission_reference as admission
import cpu_blocking_case_binding as case
import cpu_scalar_expressions as scalar
import cpu_comb_scalar_bindings as comb
from cpu_certificate_acceptance import run_stage

rtl = scalar.adapter


def unique_symbols(graph):
    result={}
    for symbol in graph['symbols']:
        if symbol['coq_root']in result:
            raise ValueError('ambiguous graph/Coq signal identity')
        result[symbol['coq_root']]=symbol
    return result


def agree_open_cone(graph, query, cone):
    """Check every generated equation; retain unsupported controllers as cuts.

    The full graph query stays saved. An open cut is NOT an assertion that the
    signal is external or irrelevant: its value remains a theorem premise.
    """
    if graph['obligations']:
        raise ValueError('unresolved original graph obligations')
    symbols={s['path']:s for s in graph['symbols']}
    nodes={n['symbol']['coq_root']:n for n in query['nodes']}
    for row in cone['nodes']:
        node=nodes.get(row['root'])
        if node is None:
            raise ValueError('missing graph equation for actual PC cone')
        deps=sorted((symbols[d]['width'],symbols[d]['coq_root'])for d in node['dependencies'])
        if node['symbol']['width']!=row['width']or deps!=sorted(map(tuple,row['dependencies'])):
            raise ValueError('graph/Coq local PC dependency or width mismatch')
    open_cuts=[]
    by_root=unique_symbols(graph)
    for row in cone['boundaries']:
        symbol=by_root[row['root']]
        if symbol['width']!=row['width']:
            raise ValueError('PC boundary width mismatch')
        if row['reason']=='unsupported_process':
            if row['root']not in nodes:
                raise ValueError('missing original controller at open PC cut')
            open_cuts.append(dict(**row,symbol=symbol,discharged=False))
        elif query['boundaries'].get(symbol['path'])!=row['reason']:
            raise ValueError('PC timing/state boundary mismatch')
    return open_cuts


def alias_chain(raw, root, width):
    edges = []; seen = set(); current = root
    while current not in seen:
        seen.add(current)
        writers = [p for p in raw['processes'] if current in p['writers']]
        if len(writers) != 1:
            break
        p = writers[0]; st = p['body']
        if p['kind'] != 'Combinational' or st.name != 'SAssign':
            break
        nba, rhs, lhs = st.args
        if (nba.name != 'false' or rhs.name != 'EVar' or lhs.name != 'LVar'
                or int(rhs.args[0].name) != width or int(lhs.args[0].name) != width):
            break
        parent = int(rhs.args[1].name)
        edges.append(dict(root=current, parent=parent, process=p['name']))
        current = parent
    else:
        raise ValueError('cycle in actual PC alias connection')
    return dict(source=root, terminal=current, width=width, edges=edges)


def unique_assignment(raw, root):
    writers = [p for p in raw['processes'] if root in p['writers']]
    if len(writers) != 1 or writers[0]['kind'] != 'Combinational':
        raise ValueError('PC arithmetic requires one actual combinational writer')
    st = writers[0]['body']
    if st.name != 'SAssign' or st.args[0].name != 'false' or st.args[2].name != 'LVar':
        raise ValueError('unsupported PC arithmetic assignment')
    return st.args[1]


def discover(c, raw, profile, graph):
    ref = admission.discover(c, raw, profile, graph)
    pc = ref['pc_state_root']
    _, residuals, outputs, _, _ = scalar.proposal(profile, {pc})
    if residuals or len(outputs) != 1:
        raise ValueError('unique supported original PC scalar update required')
    row = outputs[0]; e = row['expression']
    # reset ? (enable ? input : old_pc) : 0, preserving the original guards.
    if e.name != 'ECond' or e.args[1].name != 'EVar' or e.args[2].name != 'ECond':
        raise ValueError('unsupported PC reset/enable shape')
    w, reset, branch, zero = e.args
    _, enable, data, hold = branch.args
    if (w.name != '32' or reset.args[0].name != '1' or enable.name != 'EVar'
            or enable.args[0].name != '1' or data.name != 'EVar' or data.args[0].name != '32'
            or rtl.render(hold) != f'(EVar 32 {pc})' or rtl.render(zero) != '(EConst 32 0)'):
        raise ValueError('PC width/reset/hold mismatch')
    reset_root = int(reset.args[1].name); enable_root = int(enable.args[1].name)
    data_root = int(data.args[1].name)
    data_path = alias_chain(raw, data_root, 32)
    muxes = [p for p in raw['processes'] if data_path['terminal'] in p['writers']]
    if len(muxes) != 1:
        raise ValueError('ambiguous actual PC mux')
    mux = muxes[0]; mp = case.case_plan(mux)
    if not mp or mp[:2] != (32, data_path['terminal']):
        raise ValueError('PC input is not a supported whole blocking case mux')
    body = case.unwrap(mux['body']); selector = body.args[0]
    if selector.name != 'EVar' or selector.args[0].name != '2':
        raise ValueError('unsupported actual PC selector width')
    selector_root = int(selector.args[1].name)
    arms = {rtl.render(key): case.unwrap(st).args[1] for key, st in (a.args for a in body.args[1].args)}
    sequential = arms.get('(Some (EConst 2 0))')
    if sequential is None or sequential.name != 'EVar' or sequential.args[0].name != '32':
        raise ValueError('missing actual sequential PC mux arm')
    sum_path = alias_chain(raw, int(sequential.args[1].name), 32)
    low = unique_assignment(raw, sum_path['terminal'])
    if low.name != 'ESel' or low.args[0].name != '32' or low.args[1].name != 'EVar' or low.args[2].name != 'EConst' or low.args[2].args[1].name != '0':
        raise ValueError('PC sum is not an actual low-32 projection')
    if low.args[1].args[0].name != '33':
        raise ValueError('PC adder carry width mismatch')
    wide_root = int(low.args[1].args[1].name); wide = unique_assignment(raw, wide_root)
    if wide.name != 'EBinary' or wide.args[:2] != (rtl.Term('33'), rtl.Term('BAdd')):
        raise ValueError('unsupported actual PC adder')
    inner, carry = wide.args[2:]
    if inner.name != 'EBinary' or inner.args[:2] != (rtl.Term('33'), rtl.Term('BAdd')):
        raise ValueError('unsupported actual PC adder operands')
    def unsigned_input(term, width):
        if (term.name != 'EExtend' or term.args[0].name != '33' or term.args[1].name != 'false'
                or term.args[2].name != 'EVar' or int(term.args[2].args[0].name) != width):
            raise ValueError('PC adder signedness or width mismatch')
        return int(term.args[2].args[1].name)
    a, b = (unsigned_input(x, 32) for x in inner.args[2:])
    ci = unsigned_input(carry, 1)
    input_path = alias_chain(raw, a, 32)
    if input_path['terminal'] != pc or rtl.render(unique_assignment(raw, b)) != '(EConst 32 4)' or rtl.render(unique_assignment(raw, ci)) != '(EConst 1 0)':
        raise ValueError('actual sequential cone is not original PC plus four')
    chains = dict(data=data_path, select=alias_chain(raw, selector_root, 2),
                  enable=alias_chain(raw, enable_root, 1), sum=sum_path, input=input_path)
    roots = {edge['root'] for chain in chains.values() for edge in chain['edges']}
    roots |= {sum_path['terminal'], wide_root, b, ci}
    _, wires, _ = comb.proposal(profile, roots)
    if wires['residuals']:
        raise ValueError('unresolved PC arithmetic/wiring obligations')
    by_root = unique_symbols(graph); queries = {}
    for root in [pc, data_root, selector_root, enable_root]:
        symbol = by_root[root]
        query = admission.fetch.cdfg.backward_slice(graph, symbol['path'])
        cone = admission.fetch.cdfg.cone.cone(raw, symbol['width'], root)
        open_cuts=agree_open_cone(graph, query, cone)
        queries[str(root)] = dict(symbol=symbol, query=query, coq_cone=cone,open_cuts=open_cuts)
    return dict(pc=pc, process=row['process'], reset=reset_root, enable=enable_root, data=data_root,
        selector=selector_root, mux_process=mux['name'], chains=chains, wide=wide_root,
        adder_inputs=[a,b,ci], roots=sorted(roots), queries=queries,
        ast_sha256=raw['source_sha256'])


def render(c, raw, profile, plan):
    pc, p = plan['pc'], profile['ast']['program']
    _, _, _, scalar_source, _ = scalar.proposal(profile, {pc})
    _, wires, wires_source = comb.proposal(profile, plan['roots'])
    mux_source, _ = case.render(c['ast'], c['ast_module'], plan['mux_process'], structural=True)
    ports = {row['output_root']: i for i, row in enumerate(wires['ports'])}
    source = f"Require Import {c['ast_module']}.\nModule Scalar.\n" + scalar_source + '\nEnd Scalar.\n'
    source += 'Module Wires.\n' + wires_source + '\nEnd Wires.\n'
    source += 'Module Mux.\n' + mux_source + '\nEnd Mux.\n'
    source += '''From Coq Require Import ZArith List Bool Lia.
Require Import Lang.ExtendedSV Lang.ExtendedSVWordInvariant Lang.ExtendedSVScalarExpression.
Import ExtendedSV ExtendedSVWordInvariant ExtendedSVScalarExpression.
Local Open Scope Z_scope.
Lemma narrow_32_33 x:norm 32(norm 33 x)=norm 32 x.
Proof. change(Z.land(Z.land x 8589934591)4294967295=Z.land x 4294967295).
 rewrite <-Z.land_assoc;reflexivity. Qed.
Lemma widen_32_33 x:norm 33(norm 32 x)=norm 32 x.
Proof. change(Z.land(Z.land x 4294967295)8589934591=Z.land x 4294967295).
 rewrite <-Z.land_assoc;reflexivity. Qed.
'''
    for name, chain in plan['chains'].items():
        w = chain['width']; term = 'eq_refl'
        for edge in reversed(chain['edges']):
            term = f'(eq_trans(eq_trans(Wires.port_{ports[edge["root"]]}_lfp seed fixed HL)(norm_idempotent {w}(read_signal fixed {edge["parent"]}%nat))){term})'
        source += f'''Lemma {name}_wire seed fixed:CombLFP {p} seed fixed ->
 norm {w}(read_signal fixed {chain['source']}%nat)=norm {w}(read_signal fixed {chain['terminal']}%nat).
Proof. intro HL;exact {term}. Qed.
'''
    a,b,ci = plan['adder_inputs']; low = plan['chains']['sum']['terminal']; wide = plan['wide']
    source += f'''Local Opaque {p} PhaseSemantics.
Lemma actual_p4 seed fixed:CombLFP {p} seed fixed ->
 norm 32(read_signal fixed {low}%nat)=norm 32(norm 32(read_signal fixed {pc}%nat)+4).
Proof. intro HL.
 rewrite(Wires.port_{ports[low]}_lfp seed fixed HL);unfold Wires.port_{ports[low]}_rhs;cbn[eval_expr].
 change(norm 6 0)with 0;rewrite Z.shiftr_0_r.
 change(norm 32(norm 32(norm 33(read_signal fixed {wide}%nat)))=norm 32(norm 32(read_signal fixed {pc}%nat)+4)).
 rewrite norm_idempotent.
 rewrite(Wires.port_{ports[wide]}_lfp seed fixed HL);unfold Wires.port_{ports[wide]}_rhs;cbn[eval_expr].
 rewrite(Wires.port_{ports[b]}_lfp seed fixed HL),(Wires.port_{ports[ci]}_lfp seed fixed HL),(input_wire seed fixed HL).
 unfold Wires.port_{ports[b]}_rhs,Wires.port_{ports[ci]}_rhs;cbn[eval_expr].
 repeat rewrite norm_idempotent.
 change(norm 32(norm 33(norm 33(norm 33(norm 32(read_signal fixed {pc}%nat))+4)+0))=
 norm 32(norm 32(read_signal fixed {pc}%nat)+4)).
 rewrite widen_32_33,Z.add_0_r,!narrow_32_33;reflexivity. Qed.
Lemma actual_sequential_input seed fixed:CombLFP {p} seed fixed ->
 norm 2(read_signal fixed {plan['chains']['select']['terminal']}%nat)=0 ->
 norm 32(read_signal fixed {plan['data']}%nat)=norm 32(norm 32(read_signal fixed {pc}%nat)+4).
Proof. intros HL HS.
 rewrite(data_wire seed fixed HL),(Mux.case_actual_lfp seed fixed HL).
 unfold Mux.case_expression;cbn[eval_expr].
 rewrite(select_wire seed fixed HL),HS.
 change(norm 32(norm 32(norm 32(read_signal fixed {plan['chains']['sum']['source']}%nat)))=
 norm 32(norm 32(read_signal fixed {pc}%nat)+4)).
 rewrite !norm_idempotent,(sum_wire seed fixed HL);exact(actual_p4 seed fixed HL). Qed.
Theorem actual_sequential_pc_phase seed ev pre:
 changed_signal ev<>{pc}%nat ->CombLFP {p} seed(phase_driven_state {p} ev pre) ->
 process_matches_states pre(phase_driven_state {p} ev pre){raw['module']}.{plan['process']}=true ->
 norm 1(read_signal(phase_driven_state {p} ev pre){plan['reset']}%nat)=1 ->
 norm 1(read_signal(phase_driven_state {p} ev pre){plan['chains']['enable']['terminal']}%nat)=1 ->
 norm 2(read_signal(phase_driven_state {p} ev pre){plan['chains']['select']['terminal']}%nat)=0 ->
 norm 32(read_signal(PhaseSemantics {p} ev pre){pc}%nat)=norm 32(norm 32(read_signal pre {pc}%nat)+4).
Proof. intros HE HL HM HR HW HS.
 rewrite(Scalar.root_{pc}_expression_phase ev pre HE),HM.
 unfold Scalar.root_{pc}_expression;cbn[eval_expr].
 rewrite HR,(enable_wire seed _ HL),HW;cbn[Z.eqb].
 rewrite !norm_idempotent,(actual_sequential_input seed _ HL HS).
 rewrite(sampled_root_preserved {p} ev pre {pc}%nat Scalar.root_{pc}_comb_frame HE);reflexivity. Qed.
Goal True. idtac "PC_STEP_AUDIT". exact I. Qed.
Print Assumptions narrow_32_33.
Print Assumptions widen_32_33.
Print Assumptions actual_p4.
Print Assumptions actual_sequential_input.
Print Assumptions actual_sequential_pc_phase.
'''
    return source


def check(c, output):
    out=Path(output);out.mkdir(parents=True,exist_ok=False)
    graph=admission.fetch.cdfg.checked_graph(c['graph'],c['ast'],out/'replayed')
    raw,profile,paths=admission.fetch.cdfg.raw_binding(c['ast'],c['ast_module'])
    plan=discover(c,raw,profile,graph);text=render(c,raw,profile,plan)
    file=out/'PCStep.v';file.write_text(text)
    for name,value in [('plan',plan),('providers',paths)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    flags=list(rtl.framework.FLAGS)
    for row in paths:flags+=['-R',row['directory'],row['namespace']]
    flags+=['-R',str(out.resolve()),'GeneratedPCStep']
    start=time.monotonic()
    cc,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqc.resources').resolve()),
        str(rtl.ROOT/'_opam/bin/coqc'),'-time',*flags,str(file.resolve())],out/'coqc.log',1200)
    report=dict(accepted=False,coqc_exit=cc.returncode,coqc_timed_out=timed,
        ast_sha256=raw['source_sha256'],graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(),
        source_sha256=hashlib.sha256(text.encode()).hexdigest(),old_inv_read=False,
        controller_conditions_derived=False,frontier_relation_restored=False,
        full_R_generated=False,itree_refinement_proved=False,external_llm_api_calls=0)
    if cc.returncode==0:
        audit=cc.stdout.split('PC_STEP_AUDIT')[-1]
        closed=audit.count('Closed under the global context')==5 and 'Axioms:' not in cc.stdout
        kk,timed=run_stage(['/usr/bin/time','-v','-o',str((out/'coqchk.resources').resolve()),
            str(rtl.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec','GeneratedPCStep.PCStep'],
            out/'coqchk.log',max(.1,1200-(time.monotonic()-start)))
        report.update(accepted=closed and kk.returncode==0,assumptions_closed=closed,
            coqchk_exit=kk.returncode,coqchk_timed_out=timed)
    report['seconds']=time.monotonic()-start
    if report['accepted']:report['object_sha256']=hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['inputs','output']:parser.add_argument('--'+name,required=True)
    args=parser.parse_args()
    try:result=check(json.loads(Path(args.inputs).read_text()),args.output)
    except Exception as exc:
        out=Path(args.output)
        if out.is_dir()and not(out/'report.json').exists():
            (out/'report.json').write_text(json.dumps(dict(accepted=False,stage='preflight',error=str(exc),cli_exit=1),indent=2)+'\n')
        raise
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted']else 1)
