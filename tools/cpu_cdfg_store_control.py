"""Discover the real byte-bank write path and prove non-store ISA controls.

Names do not assign memory roles. Indexed byte writes identify a candidate bank;
its actual outer guard is traced through scalar captures to the controller.
The graph proposes the path, while original-AST observations prove each result.
No old CPU R/INV is an input, and no replacement RTL or ISA is evaluated.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import time

import cpu_cdfg_rising_joint as rising
import cpu_guarded_write as guarded
from cpu_add_admission_ledger import checked_provider
from cpu_certificate_acceptance import run_stage


pc = rising.prefill.bubble.invalid.fetch.pc


def byte_write_graph(raw, graph, proc, bank):
    """Compare ordered data/address/guard/phase signatures, not signal names.

    These checks identify candidates. The emitted NbPlan is separately checked
    against the original Coq body, including actual address expressions.
    This check does NOT assert pyslang-to-Coq translation equivalence.
    """
    symbols = pc.unique_symbols(graph)
    by_path = {s['path']:s for s in graph['symbols']}
    path = symbols[bank['root']]['path']
    edges = [e for e in graph['edges'] if e['target'] == path]
    rows = []
    def inputs(expression):
        return sorted({int(n.args[1].name) for n in pc.rtl.walk(expression) if n.name == 'EVar'})
    def visit(st, guards):
        if st.name == 'SSeq':
            for child in st.args[0].args:
                visit(child, guards)
        elif st.name == 'SIf':
            guard, yes, no = st.args
            if guard.name != 'EVar' or guard.args[0].name != '1':
                raise ValueError('unsupported byte-write branch expression')
            r = int(guard.args[1].name)
            visit(yes, guards + [(r, True)]); visit(no, guards + [(r, False)])
        elif st.name == 'SAssign':
            _, rhs, lhs = st.args
            rows.append(dict(data=inputs(rhs), address=inputs(lhs.args[2]), guards=guards))
        elif st.name != 'SSkip':
            raise ValueError('unsupported byte-write statement')
    visit(proc['body'], [])
    if len(edges) != len(rows) or len({e['process'] for e in edges}) != 1:
        raise ValueError('missing or extra original byte-write graph edge')
    signatures = []
    for row, edge in zip(rows, edges):
        conditions = []
        for guard in edge['guards']:
            exprs = guard['condition']
            if (len(exprs) != 1 or exprs[0]['kind'] != 'NamedValueExpression'
                    or exprs[0]['width'] != 1):
                raise ValueError('byte-write graph guard is not an actual one-bit read')
            conditions.append((by_path[exprs[0]['symbol']]['coq_root'], guard['taken']))
        data = sorted(by_path[p]['coq_root'] for p in edge['data'])
        address = sorted(by_path[p]['coq_root'] for p in edge['address'])
        if data != row['data'] or address != row['address'] or conditions != row['guards']:
            raise ValueError('byte-write data/address/guard dependency mismatch')
        if (edge['assignment'] != 'nonblocking' or edge['reads_version'] != 'procedural_current'
                or edge['writes_version'] != 'next' or edge['left']['width'] != 8
                or edge['left']['value']['width'] != bank['width']):
            raise ValueError('byte-write graph width or assignment phase mismatch')
        signatures.append(dict(edge_id=edge['id'], **row))
    graph_proc = next(p for p in graph['processes'] if p['id'] == edges[0]['process'])
    timing = graph_proc['body']['timing']
    events = re.findall(r'event_edge := (Posedge|Negedge); event_signal := (\d+)', proc['events'])
    if (len(events) != 1 or timing['kind'] != 'SignalEventControl' or timing.get('iff') is not None
            or timing['edge'] != {'Posedge':'EdgeKind.PosEdge', 'Negedge':'EdgeKind.NegEdge'}[events[0][0]]
            or timing['expr']['kind'] != 'NamedValueExpression' or timing['expr']['width'] != 1
            or by_path[timing['expr']['symbol']]['coq_root'] != int(events[0][1])):
        raise ValueError('byte-write graph clock phase mismatch')
    return dict(symbol=symbols[bank['root']], graph_process=graph_proc['id'],
        ordered_assignments=signatures, timing=timing, translation_equivalence_proved=False)


def scalar_row(raw, root):
    found = pc.scalar.scalar.analyze(raw, {root})
    writers = [(p, nb) for p, nb in found['analysis']['plans'] if root in p['writers']]
    if found['residuals'] or len(writers) != 1:
        raise ValueError('one supported original scalar capture required')
    proc, nb = writers[0]
    expression = pc.scalar.compile_expression(pc.scalar.slices.slice_plan(nb, root), root, 1,
        pc.rtl.Term('EVar', (pc.rtl.Term('1'), pc.rtl.Term(str(root)))))
    if (expression is None or expression.name != 'ECond'
            or expression.args[1].name != 'EVar' or expression.args[1].args[0].name != '1'
            or expression.args[2].name != 'EVar' or expression.args[2].args[0].name != '1'
            or pc.rtl.render(expression.args[3]) != '(EConst 1 0)'):
        raise ValueError('store control must be an actual reset/one-bit capture')
    return dict(root=root, width=1, process=proc['name'], events=proc['events'],
        expression=pc.rtl.render(expression), reset=int(expression.args[1].args[1].name),
        input=int(expression.args[2].args[1].name))


def discover(c, raw, profile, graph):
    plan = rising.discover(c, raw, profile, graph)
    symbols = pc.unique_symbols(graph)
    candidates = []
    for proc in raw['processes']:
        if proc['kind'] != 'Sequential':
            continue
        writes = [n for n in pc.rtl.walk(proc['body']) if n.name == 'SAssign']
        if not writes:
            continue
        leaves = [n.args[2] for n in writes]
        if not all(n.args[0].name == 'true' for n in writes):
            continue
        if not all(l.name == 'LSel' and l.args[0].name == '8'
                   and l.args[1].name == 'LVar' for l in leaves):
            continue
        roots = {(int(l.args[1].args[0].name), int(l.args[1].args[1].name)) for l in leaves}
        if len(roots) != 1:
            raise ValueError('ambiguous multi-bank byte-write process')
        width, root = next(iter(roots))
        body = proc['body']
        while body.name == 'SSeq' and len(body.args[0].args) == 1:
            body = body.args[0].args[0]
        if (body.name != 'SIf' or body.args[0].name != 'EVar'
                or body.args[0].args[0].name != '1' or body.args[2].name != 'SSkip'):
            raise ValueError('byte-bank writes are not all guarded by one actual enable')
        if len([p for p in raw['processes'] if root in p['writers']]) != 1:
            raise ValueError('byte bank has additional writers')
        if width % 8 or symbols[root]['width'] != width:
            raise ValueError('byte-bank bit width mismatch')
        candidates.append(dict(root=root, width=width, process=proc['name'], events=proc['events'],
            guard=int(body.args[0].args[1].name), assignments=len(writes),
            plan=pc.rtl.render(pc.rtl.plan_of(proc['body']))))
    if len(candidates) != 1:
        raise ValueError('one unambiguous original byte bank required')
    bank = candidates[0]
    bank_proc = next(p for p in raw['processes'] if p['name'] == bank['process'])
    bank['graph_binding'] = byte_write_graph(raw, graph, bank_proc, bank)
    control = bank['guard']; chain = []; seen = set()
    while control not in seen:
        seen.add(control)
        aliases = pc.alias_chain(raw, control, 1)
        terminal = aliases['terminal']
        query = pc.admission.fetch.cdfg.backward_slice(graph, symbols[control]['path'])
        cone = pc.admission.fetch.cdfg.cone.cone(raw, 1, control)
        pc.agree_open_cone(graph, query, cone)
        writers = [p for p in raw['processes'] if terminal in p['writers']]
        if len(writers) != 1:
            raise ValueError('store-control trace has ambiguous writer')
        if writers[0]['kind'] == 'Combinational':
            controller = writers[0]
            break
        row = scalar_row(raw, terminal)
        chain.append(dict(aliases=aliases, query=query, cone=cone, **row))
        control = row['input']
    else:
        raise ValueError('cyclic store-control capture path')
    if not chain:
        raise ValueError('no physical pipeline capture on the store path')
    pairs = guarded.discover(raw)
    matches = [(i, row) for i, row in enumerate(pairs)
               if row['write'] == terminal and row['gate'] == plan['enable_root']
               and row['process'] == controller['name']]
    if len(matches) != 1:
        raise ValueError('store path lacks a checked whole-controller enable correlation')
    index, pair = matches[0]
    if controller['name'] != plan['enable_process']:
        raise ValueError('store and acceptance controls are not from the same original process')
    selectors = {int(n.args[0].args[1].name) for n in pc.rtl.walk(controller['body'])
        if n.name == 'SCase' and n.args[0].name == 'EVar' and n.args[0].args[0].name == '7'}
    if len(selectors) != 1:
        raise ValueError('ambiguous original instruction opcode selector')
    opcode = next(iter(selectors))
    opcode_cone = pc.admission.fetch.cdfg.cone.cone(raw, 7, opcode)
    opcode_query = pc.admission.fetch.cdfg.backward_slice(graph, symbols[opcode]['path'])
    pc.admission.fetch.cdfg.agree(graph, opcode_query, opcode_cone)
    if opcode_cone['boundaries'] != [dict(width=32, root=plan['pair']['carrier'], reason='sequential')]:
        raise ValueError('store opcode does not come from the same captured instruction')
    plan.update(byte_bank=bank, store_captures=chain,
        store_controller=dict(root=terminal, process=controller['name'],
            alias_tail=aliases, query=query, cone=cone,
            guard_pair_index=index, guard_pair=pair, opcode=opcode,
            opcode_cone=opcode_cone, opcode_query=opcode_query))
    return plan


def render(c, raw, profile, plan, shallow_specialization=False):
    p, am = profile['ast']['program'], raw['module']
    ctl = plan['store_controller']; root = ctl['root']; opcode = ctl['opcode']
    # The complete original blocking process is observed, preserving priority and
    # read-after-write. This is not a hand-written truth table for a named signal.
    obs, _, report = rising.prefill.bubble.invalid.fetch.obs.render(
        c['ast'], c['ast_module'], ctl['process'], root, 1)
    if report['ast_sha256'] != raw['source_sha256']:
        raise ValueError('original blocking observation source changed')
    expr = f'Store.expr_{report["rules"] - 1}'
    comb_index = [r['name'] for r in raw['processes'] if r['kind'] == 'Combinational'].index(ctl['process'])
    source = 'Module Store.\n' + obs + '\nEnd Store.\n'
    source += f'''From Coq Require Import List ZArith Bool.
Require Import {c['ast_module']} Lang.ExtendedSV Lang.ExtendedSVWordInvariant
 Lang.ExtendedSVExpressionBinding Lang.ExtendedSVProjectionConnection Lang.ExtendedSVExpressionFold
 GeneratedPCControl.PCControl.
Import ListNotations ExtendedSV ExtendedSVWordInvariant ExtendedSVExpressionBinding
 ExtendedSVProjectionConnection ExtendedSVExpressionFold.
Local Open Scope Z_scope.
Local Opaque {p} PhaseSemantics.
Definition original_combs:=filter is_comb(processes {p}).
Lemma registered:nth_error original_combs {comb_index}%nat=Some {am}.{ctl['process']}.
Proof. vm_compute;reflexivity. Qed.
Lemma connected:expression_bindingb original_combs {comb_index}%nat {root}%nat {expr}=true.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_store_control_lfp seed fixed:CombLFP {p} seed fixed ->
 norm 1(read_signal fixed {root}%nat)=norm 1(eval_expr fixed {expr}).
Proof. exact(checked_expression_binding {p} original_combs {comb_index}%nat {am}.{ctl['process']}
 1 {root}%nat {expr} seed fixed eq_refl registered Store.actual_observation connected). Qed.
Definition opcode_binding (value:Z)(w x:nat):option Expr:=
 if Nat.eqb w 7%nat && Nat.eqb x {opcode}%nat then Some(EConst 7 value)else None.
Definition selected value:=fold_expression(substitute(opcode_binding value){expr}).
Lemma specialized seed fixed value:
 CombLFP {p} seed fixed ->norm 7(read_signal fixed {opcode}%nat)=norm 7 value ->
 norm 1(read_signal fixed {root}%nat)=norm 1(eval_expr fixed(selected value)).
Proof. intros HL HO;rewrite(actual_store_control_lfp seed fixed HL).
 assert(HS:eval_expr fixed(substitute(opcode_binding value){expr})=eval_expr fixed {expr}).
 {{ apply substitute_sound;intros w x rhs HB;unfold opcode_binding in HB.
    destruct(Nat.eqb w 7%nat && Nat.eqb x {opcode}%nat)eqn:HC;[|discriminate].
    apply andb_true_iff in HC as[HW HX];apply Nat.eqb_eq in HW,HX;subst w x.
    inversion HB;subst rhs;cbn[eval_expr];rewrite norm_idempotent;exact HO. }}
 rewrite <-HS,<-(fold_expression_sound(substitute(opcode_binding value){expr})fixed);reflexivity. Qed.
'''
    for value in [0, 19, 51]:
        source += f'''Lemma opcode_{value}_checked:selected {value}=EConst 1 0.
Proof. vm_compute;reflexivity. Qed.
Theorem actual_opcode_{value}_nonstore seed fixed:CombLFP {p} seed fixed ->
 norm 7(read_signal fixed {opcode}%nat)={value} ->norm 1(read_signal fixed {root}%nat)=0.
Proof. intros HL HO;rewrite(specialized seed fixed {value} HL HO),opcode_{value}_checked;reflexivity. Qed.
'''
    word = plan['pair']['carrier']; pcctl = 'GeneratedPCControl.PCControl'
    source += f'''Theorem actual_original_ADD_nonstore seed fixed code rd rs1 rs2:
 CombLFP {p} seed fixed ->norm 32(read_signal fixed {word}%nat)=norm 32 code ->
 Decode.decode Decode.RV32I code=Decode.IInstruction(Decode.Add rd rs1 rs2) ->
 norm 1(read_signal fixed {root}%nat)=0.
Proof. intros HL HW HD;apply(actual_opcode_51_nonstore seed fixed HL).
 pose proof({pcctl}.Opcode.cone_{opcode}_actual seed fixed HL)as HO.
 let expression:=eval cbv in {pcctl}.Opcode.cone_{opcode} in
 change(norm 7(read_signal fixed {opcode}%nat)=norm 7(eval_expr fixed expression))in HO.
 cbn[eval_expr]in HO;rewrite HW in HO;repeat rewrite norm_idempotent in HO.
 exact(eq_trans HO({pcctl}.original_ADD_opcode code rd rs1 rs2 HD)). Qed.
Theorem actual_bubble_nonstore seed fixed:
 CombLFP {p} seed fixed ->norm 32(read_signal fixed {word}%nat)=norm 32 {plan['bubble']} ->
 norm 1(read_signal fixed {root}%nat)=0.
Proof. intros HL HW;apply(actual_opcode_19_nonstore seed fixed HL).
 pose proof({pcctl}.Opcode.cone_{opcode}_actual seed fixed HL)as HO.
 let expression:=eval cbv in {pcctl}.Opcode.cone_{opcode} in
 change(norm 7(read_signal fixed {opcode}%nat)=norm 7(eval_expr fixed expression))in HO.
 cbn[eval_expr]in HO;rewrite HW in HO;exact HO. Qed.
Goal True. idtac "STORE_CONTROL_AUDIT". exact I. Qed.
'''
    exports = ['actual_store_control_lfp', 'specialized']
    for value in [0, 19, 51]:
        exports += [f'opcode_{value}_checked', f'actual_opcode_{value}_nonstore']
    exports += ['actual_original_ADD_nonstore', 'actual_bubble_nonstore']
    source += ''.join(f'Print Assumptions {name}.\n' for name in exports)
    if shallow_specialization:
        old = f''' rewrite <-HS,<-(fold_expression_sound(substitute(opcode_binding value){expr})fixed);reflexivity. Qed.'''
        new = f''' exact(eq_trans(f_equal(norm 1)(eq_sym HS))
   (f_equal(norm 1)(eq_sym(fold_expression_sound(substitute(opcode_binding value){expr})fixed)))). Qed.'''
        if source.count(old) != 1:
            raise ValueError('original specialization proof changed')
        source = source.replace(old, new, 1)
    return source, exports


def check(c, output, shallow_specialization=False, baseline=None, budget_seconds=1200):
    if not 0 < budget_seconds <= 1200:
        raise ValueError('native attempt budget must be within 20 minutes')
    out = Path(output); out.mkdir(parents=True, exist_ok=False)
    graph = pc.admission.fetch.cdfg.checked_graph(c['graph'], c['ast'], out / 'replayed')
    raw, profile, _ = pc.admission.fetch.cdfg.raw_binding(c['ast'], c['ast_module'])
    plan = discover(c, raw, profile, graph)
    paths = checked_provider(c['cycle_joint'], 'CycleJoint.v', raw['source_sha256'],
        ['actual_ADD_whole_clock_cycle_preserves_same_joint'])
    paths += [dict(namespace='GeneratedClockCycleJoint', directory=str(Path(c['cycle_joint']).resolve()))]
    source, exports = render(c, raw, profile, plan, shallow_specialization)
    if shallow_specialization:
        if baseline is None:
            raise ValueError('an actual native 20-minute baseline is required before repair')
        old_dir = Path(baseline); old = json.loads((old_dir/'report.json').read_text())
        original, _ = render(c, raw, profile, plan)
        if not (old.get('coqc_timed_out') is True and old.get('coqc_exit') == 124
                and old.get('seconds',0) >= 1200 and (old_dir/'StoreControl.v').read_text() == original
                and old.get('source_sha256') == hashlib.sha256(original.encode()).hexdigest()):
            raise ValueError('unchanged actual 20-minute baseline required')
        pins=[]
        for target in exports:
            # Lemmas and Theorems are both accepted; the entire header is pinned.
            before=original.split(target,1)[1].split('Proof.',1)[0]
            after=source.split(target,1)[1].split('Proof.',1)[0]
            if before != after:
                raise ValueError('specialization repair changed a target')
            pins.append(dict(target=target,signature_sha256=hashlib.sha256(before.encode()).hexdigest()))
        (out/'same-target-repair.json').write_text(json.dumps(dict(baseline=str(old_dir),
            repair='explicit equality composition; no rewriting through the large expression',
            targets=pins,RTL_changed=False,ISA_changed=False,environment_changed=False),indent=2)+'\n')
    file = out / 'StoreControl.v'; file.write_text(source)
    for key, value in [('plan', plan), ('providers', paths), ('exports', exports)]:
        (out / (key + '.json')).write_text(json.dumps(value, indent=2) + '\n')
    flags = list(pc.rtl.framework.FLAGS)
    for row in paths:
        flags += ['-R', row['directory'], row['namespace']]
    flags += ['-R', str(out.resolve()), 'GeneratedStoreControl']; start = time.monotonic()
    cc, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqc.resources').resolve()),
        str(pc.rtl.ROOT / '_opam/bin/coqc'), '-time', *flags, str(file.resolve())], out / 'coqc.log', budget_seconds)
    report = dict(accepted=False, coqc_exit=cc.returncode, coqc_timed_out=timed,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(), ast_sha256=raw['source_sha256'],
        graph_sha256=hashlib.sha256(Path(c['graph']).read_bytes()).hexdigest(), old_inv_read=False,
        original_ADD_and_bubble_store_control_zero=False, full_R_generated=False,
        full_cycle_preservation_proved=False, itree_refinement_proved=False, external_llm_api_calls=0,
        shallow_specialization_repair=shallow_specialization,native_budget_seconds=budget_seconds)
    if cc.returncode == 0:
        audit = cc.stdout.split('STORE_CONTROL_AUDIT')[-1]
        closed = audit.count('Closed under the global context') == len(exports) and 'Axioms:' not in audit
        kk, timed = run_stage(['/usr/bin/time', '-v', '-o', str((out / 'coqchk.resources').resolve()),
            str(pc.rtl.ROOT / '_opam/bin/coqchk'), '-silent', *flags, '-norec',
            'GeneratedStoreControl.StoreControl'], out / 'coqchk.log', max(.1, budget_seconds - (time.monotonic() - start)))
        ok = closed and kk.returncode == 0
        report.update(accepted=ok, coqchk_exit=kk.returncode, coqchk_timed_out=timed,
            assumptions_closed=closed, original_ADD_and_bubble_store_control_zero=ok)
    report['seconds'] = time.monotonic() - start
    if report['accepted']:
        report['object_sha256'] = hashlib.sha256(file.with_suffix('.vo').read_bytes()).hexdigest()
    (out / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ['inputs', 'output']:
        parser.add_argument('--' + key, required=True)
    parser.add_argument('--shallow-specialization',action='store_true')
    parser.add_argument('--baseline')
    parser.add_argument('--budget-seconds',type=float,default=1200)
    args = parser.parse_args()
    try:
        result = check(json.loads(Path(args.inputs).read_text()), args.output,
            args.shallow_specialization,args.baseline,args.budget_seconds)
    except Exception as exc:
        out = Path(args.output)
        if out.is_dir() and not (out / 'report.json').exists():
            (out / 'report.json').write_text(json.dumps(dict(accepted=False,
                stage='preflight', error=str(exc), cli_exit=1), indent=2) + '\n')
        raise
    print(json.dumps(result, indent=2)); raise SystemExit(0 if result['accepted'] else 1)
