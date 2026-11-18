"""Bind RF address cones to instruction-word fields using actual LFP proofs.

Reference word equality remains explicit until token-history ownership is
proved. Registered or multi-source addresses are residuals, never guessed.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_pending_connected_projections as connected
import cpu_rf_read_ports as readers
import cpu_blocking_case_binding as case_binding
import cpu_operand_tagged_origins as tagged_origins
from cpu_certificate_acceptance import run_stage

origin = connected.origin
rtl = connected.rtl


def support_frontier(ast):
    """Stop at the first nontrivial writer, keeping every data/control input."""
    todo = sorted({int(n.args[1].name) for port in readers.analyze(ast)['ports']
        for n in rtl.walk(port['rhs']) if n.name=='EVar' and int(n.args[0].name) in (5,6)})
    seen=set(); cases={}; residuals=[]; registers=[]
    while todo:
        root=todo.pop()
        if root in seen:continue
        seen.add(root)
        writers=[p for p in ast['processes'] if p['kind']!='Initial' and root in p['writers']]
        if not any(p['kind']=='Combinational' for p in writers):
            registers.append(root);continue
        if len(writers)!=1:
            residuals.append(dict(root=root,reason='non-unique writer'));continue
        proc=writers[0];body=case_binding.unwrap(proc['body'])
        if body.name=='SAssign' and body.args[0].name=='false' and body.args[2].name=='LVar':
            todo.extend(origin.pending.roots(body.args[1]));continue
        plan=case_binding.case_plan(proc)
        if plan is not None and plan[1]==root:
            cases[proc['name']]=dict(process=proc['name'],root=root,width=plan[0],
                expression=rtl.render(plan[2]),source_line=proc['line'])
        else:
            residuals.append(dict(root=root,process=proc['name'],source_line=proc['line'],
                reason='complete branch process needs another checked expression rule'))
    return dict(cases=list(cases.values()),residuals=residuals,
        temporal_or_external_boundaries=sorted(registers),semantic_roles_proved=False)


def discover(ast,requested=None):
    cones = connected.Cones(ast)
    address_inputs = sorted(set(requested)) if requested is not None else sorted({(int(n.args[0].name), int(n.args[1].name))
        for port in readers.analyze(ast)['ports'] for n in rtl.walk(port['rhs'])
        if n.name == 'EVar' and int(n.args[0].name) in (5, 6)})
    rows, residuals = [], []
    for width, root in address_inputs:
        variable = rtl.Term('EVar', (rtl.Term(str(width)), rtl.Term(str(root))))
        try:
            expanded = cones.expand(variable)
        except ValueError as exc:
            residuals.append(dict(root=root, reason=str(exc)))
            continue
        leaves = [n for n in rtl.walk(expanded) if n.name == 'EVar']
        sources = {int(n.args[1].name) for n in leaves if n.args[0].name == '32'}
        if len(sources) != 1 or any(n.args[0].name != '32' for n in leaves):
            residuals.append(dict(root=root, reason='address requires registered history or multiple sources',
                expression=rtl.render(expanded)))
            continue
        rows.append(dict(root=root, width=width, source=next(iter(sources)),
                         expanded=rtl.render(expanded)))
    order = cones.closure([rtl.Term('EVar', (rtl.Term(str(r['width'])),rtl.Term(str(r['root'])))) for r in rows])
    return rows, residuals, cones, order


def render(ast_path, ast_module,requested=None):
    ast, profile, paths = origin.raw_binding(ast_path, ast_module)
    rows, residuals, cones, order = discover(ast,requested)
    report = dict(old_inv_read=False, token_identity_proved=False,
        operand_freshness_proved=False, complete_R_generated=False,
        origins=rows, residuals=residuals, ast_sha256=ast['source_sha256'])
    if not rows:
        return report, None, paths, 0
    _, analysis, source = connected.comb.proposal(profile, order)
    if analysis['residuals']:
        report['connection_residuals'] = analysis['residuals']
        return report, None, paths, 0
    ports = {p['output_root']: i for i,p in enumerate(analysis['ports'])}
    program = profile['ast']['program']
    lines = ['Require Import Lang.ExtendedSVProjectionConnection Lang.ExtendedSVWordInvariant Lang.ExtendedSVProjectionOrigin.',
        'Import ExtendedSVProjectionConnection ExtendedSVWordInvariant ExtendedSVProjectionOrigin.',
        f'Local Opaque {program}.']
    for root in order:
        node = cones.nodes[root]
        width = node['width']
        children = cones.bindings(node['rhs'])
        entries = ';'.join(f'Build_Binding {cones.nodes[r]["width"]} {r} address_{r}_expanded' for r in children)
        lines += [f'Definition address_{root}_bindings:list Binding:=[{entries}].',
            f'Lemma address_{root}_agree seed fixed:CombLFP {program} seed fixed ->',
            f' BindingsAgree fixed address_{root}_bindings.',
            f'Proof. intro HL. unfold address_{root}_bindings,BindingsAgree.']
        for r in children:
            lines += [f' constructor;[exact(address_{r}_sound seed fixed HL)|].']
        lines += [' constructor. Qed.',
            f'Definition address_{root}_expanded:=substitute(lookup_binding address_{root}_bindings)port_{ports[root]}_rhs.',
            f'Lemma address_{root}_sound seed fixed:CombLFP {program} seed fixed ->',
            f' norm {width}(read_signal fixed {root})=norm {width}(eval_expr fixed address_{root}_expanded).',
            f'Proof. intro HL. exact(eq_trans(port_{ports[root]}_lfp seed fixed HL)',
            f' (f_equal(norm {width})(eq_sym(bindings_substitute_sound address_{root}_bindings port_{ports[root]}_rhs fixed',
            f' (address_{root}_agree seed fixed HL))))). Qed.']
    for row in rows:
        r,w,src = row['root'],row['width'],row['source']
        lines += [f'Definition address_{r}_reference word:=norm {w}(capture_value {src} address_{r}_expanded word).',
            f'Lemma address_{r}_inputs:capture_inputs_onlyb {src} address_{r}_expanded=true.',
            'Proof. vm_compute. reflexivity. Qed.',
            f'Theorem address_{r}_instruction seed fixed word:CombLFP {program} seed fixed ->',
            f' norm 32(read_signal fixed {src})=norm 32 word ->',
            f' norm {w}(read_signal fixed {r})=address_{r}_reference word.',
            f'Proof. intros HL HW. rewrite(address_{r}_sound seed fixed HL).',
            f' unfold address_{r}_reference. rewrite(capture_value_sound {src} address_{r}_expanded fixed word address_{r}_inputs HW).',
            ' reflexivity. Qed.', f'Print Assumptions address_{r}_instruction.']
    return report, source+'\n'+'\n'.join(lines)+'\n', paths, len(analysis['ports'])+len(rows)


def check(ast_path, ast_module, output):
    output = Path(output); output.mkdir(parents=True, exist_ok=False)
    report, source, paths, count = render(ast_path, ast_module)
    report['accepted'] = False
    ast, _, _ = origin.raw_binding(ast_path, ast_module)
    support=support_frontier(ast)
    report['support_frontier']=support
    report['case_support_checks']=[case_binding.check(ast_path,ast_module,row['process'],
        output/('case-'+row['process']),structural=True) for row in support['cases']]
    # A read address may itself be a register. Reuse inferred capture/hold
    # history, not a combinational equality to the currently visible word.
    registered = [r['root'] for r in report['residuals']
        if r['reason']=='address requires registered history or multiple sources']
    if registered:
        ast, _, _ = origin.raw_binding(ast_path, ast_module)
        inferred = connected.direct.discover(ast)
        available = {r['root'] for r in inferred['projections']}
        selected = sorted(set(registered)&available)
        if selected:
            report['registered_origins'] = connected.direct.check(ast_path, ast_module,
                output/'registered', selected_roots=selected)
            report['registered_roots'] = selected
    if source is not None:
        path = output/'AddressOrigins.v'; path.write_text(source)
        report['source_sha256'] = hashlib.sha256(source.encode()).hexdigest()
        flags = list(rtl.framework.FLAGS)
        for row in paths: flags += ['-R', row['directory'], row['namespace']]
        flags += ['-R', str(output.resolve()), 'GeneratedAddressOrigins']
        start = time.monotonic(); deadline = start+1200
        c,t = run_stage([str(origin.ROOT/'_opam/bin/coqc'), '-time', *flags,str(path.resolve())],
                        output/'coqc.log',deadline-time.monotonic())
        report.update(coqc_exit=c.returncode, coqc_timed_out=t)
        if c.returncode == 0 and time.monotonic()<deadline:
            report['assumptions_closed'] = c.stdout.count('Closed under the global context')==count and 'Axioms:' not in c.stdout
            k,t = run_stage([str(origin.ROOT/'_opam/bin/coqchk'),'-silent',*flags,'-norec',
                'GeneratedAddressOrigins.AddressOrigins'],output/'coqchk.log',deadline-time.monotonic())
            report.update(coqchk_exit=k.returncode,coqchk_timed_out=t,
                accepted=k.returncode==0 and report['assumptions_closed'])
        report['seconds'] = time.monotonic()-start
    if source is None and report.get('registered_origins', {}).get('accepted'):
        report['accepted'] = True
    covered = {r['root'] for r in report['origins']} if source is not None and report['accepted'] else set()
    if report.get('registered_origins', {}).get('accepted'):
        covered.update(report['registered_roots'])
    outstanding = {r['root'] for r in report['origins']+report['residuals']}-covered
    six_bit_inputs = {int(n.args[1].name) for port in readers.analyze(ast)['ports']
        for n in rtl.walk(port['rhs']) if n.name=='EVar' and n.args[0].name=='6'}
    if outstanding & six_bit_inputs:
        tagged_plan, tagged_source, _, _ = tagged_origins.render(ast_path, ast_module)
        if tagged_source is not None and outstanding & {r['root'] for r in tagged_plan['origins']}:
            result = tagged_origins.check(ast_path, ast_module, output/'tagged')
            report['tagged_origins'] = result
            if result['accepted']:
                covered.update(r['root'] for r in result['origins'])
                report['accepted'] = True
    report['unresolved_roots'] = sorted({r['root'] for r in report['origins']+report['residuals']}-covered)
    report['all_discovered_addresses_covered'] = report['accepted'] and not report['unresolved_roots']
    (output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();result=check(a.ast,a.ast_module,a.output)
    print(json.dumps(result,indent=2));raise SystemExit(0 if result['accepted'] else 1)
