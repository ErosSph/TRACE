"""Raw RTL data routes from RF ports to operand captures and selection cones.

Routes are structural candidates, not forwarding correctness. Controls are
retained but never mistaken for data transport. Sequential edges keep their
sampling boundary. No previous invariant or role profile is an input.
"""
import argparse
import json
from pathlib import Path
import cpu_pending_origins as origin
import cpu_rf_read_ports as ports

rtl = origin.pending.rtl


def alternatives(expression, width, choices=()):
    if expression.name == 'ECond' and expression.args[0].name == str(width):
        _, guard, yes, no = expression.args
        yield from alternatives(yes, width, choices+((rtl.render(guard), True),))
        yield from alternatives(no, width, choices+((rtl.render(guard), False),))
    elif expression.name == 'EExtend' and expression.args[0].name == str(width) \
            and expression.args[1].name == 'false' and expression.args[2].name == 'EVar' \
            and expression.args[2].args[0].name == str(width):
        yield choices, int(expression.args[2].args[1].name), expression
    elif expression.name == 'EVar' and expression.args[0].name == str(width):
        yield choices, int(expression.args[1].name), expression
    else:
        yield choices, None, expression


def source_kind(source, expression, known):
    """Structural only: a signal outside RF reachability is NOT a forward.

    ISA register/immediate/PC ownership still needs a checked instruction
    relation; this classification must not manufacture one from a mux.
    """
    if source is not None:
        return 'transported_rf_data' if source in known else 'unclassified_external_data'
    if expression.name == 'EConst':
        return 'constant_data'
    if set(origin.pending.roots(expression)) & known:
        return 'transformed_rf_data'
    return 'unclassified_expression'


def port_provenance(seeds,assignments):
    """May-origins through same-width copies only, including cycles/joins.
    Never identify different ports just because both eventually read the RF.
    Arithmetic is a terminal obligation, not identity transport.
    """
    origins={root:{root}for root in seeds}
    while True:
        changed=False
        for row in assignments:
            if not row['whole']:continue
            incoming=set().union(*(origins.get(source,set())for _,source,_ in row['leaves']))
            if not incoming:continue
            previous=origins.setdefault(row['root'],set())
            if not incoming<=previous:previous.update(incoming);changed=True
        if not changed:return origins


def discover(ast):
    readers = ports.analyze(ast)
    seeds = sorted({p['output_root'] for p in readers['ports'] if p['width'] == 32})
    assignments = []
    for proc in ast['processes']:
        for outer, statement in origin.pending.paths(proc['body']):
            nba, rhs, lhs = statement.args
            root = rtl.root_of(lhs)
            whole = lhs.name == 'LVar' and lhs.args[0].name == '32'
            leaves = list(alternatives(rhs, 32)) if whole else []
            assignments.append(dict(process=proc['name'], kind=proc['kind'],
                events=proc['events'], source_line=proc['line'], root=root,
                nba=nba.name == 'true', outer_conditions=list(outer),
                lhs=rtl.render(lhs), rhs=rtl.render(rhs), whole=whole,
                leaves=leaves, read_roots=origin.pending.roots(rhs)))
    provenance=port_provenance(seeds,assignments)
    known=set(provenance)
    routes, terminals = [], []
    for row in assignments:
        carriers = [dict(source=source, conditions=list(conditions), expression=rtl.render(leaf),
                         origin_ports=sorted(provenance[source]))
                    for conditions, source, leaf in row['leaves'] if source in known]
        if not carriers:
            if set(row['read_roots']) & known:
                terminals.append(dict(**{k: v for k, v in row.items() if k != 'leaves'},
                    origin_ports=sorted(set().union(*(provenance.get(r,set())for r in row['read_roots'])))))
            continue
        alternatives_out = [dict(source=source, conditions=list(conditions), expression=rtl.render(leaf),
                                 source_kind=source_kind(source, leaf, known),
                                 origin_ports=sorted(set().union(*(provenance.get(r,set())for r in origin.pending.roots(leaf)))))
                            for conditions, source, leaf in row['leaves']]
        routes.append(dict(**{k:v for k,v in row.items() if k not in ('leaves','read_roots')},
            origin_ports=sorted(provenance.get(row['root'],set())),
            incoming=carriers, alternatives=alternatives_out,
            crossed_sampling_boundary=row['kind']=='Sequential',
            obligations=['actual process/path semantics', 'ISA operand kind (register/immediate/PC/transformed data)', 'valid token ownership',
                         'source reference cut', 'selection equals newest eligible older write']))
    return dict(ast_sha256=ast['source_sha256'], read_ports=seeds,
        port_provenance={str(root):sorted(origins)for root,origins in sorted(provenance.items())},
        provenance_is_conditional_may_dependence=True,
        reader_residuals=readers['residuals'], reached_roots=sorted(known),
        routes=routes, terminal_consumers=terminals, old_inv_read=False,
        arithmetic_is_not_identity=True, semantic_routes_checked=False,
        rf_reachability_is_not_forwarding=True,
        operand_freshness_proved=False, complete_R_generated=False)


def run(ast_path, ast_module, output):
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    ast,_,_=origin.raw_binding(ast_path,ast_module)
    plan=discover(ast)
    (output/'routes.json').write_text(json.dumps(plan,indent=2)+'\n')
    summary=dict(accepted=False, analysis_completed=True, old_inv_read=False,
        read_ports=len(plan['read_ports']), routes=len(plan['routes']),
        multi_origin_roots=sum(len(v)>1 for v in plan['port_provenance'].values()),
        provenance_is_conditional_may_dependence=True,
        sequential_routes=sum(r['crossed_sampling_boundary'] for r in plan['routes']),
        selections=sum(bool(r['outer_conditions']) or len(r['alternatives'])>1 for r in plan['routes']),
        terminal_consumers=len(plan['terminal_consumers']),
        semantic_routes_checked=False, operand_freshness_proved=False, complete_R_generated=False)
    (output/'report.json').write_text(json.dumps(summary,indent=2)+'\n')
    return summary


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['ast','ast-module','output']:p.add_argument('--'+name,required=True)
    a=p.parse_args();print(json.dumps(run(a.ast,a.ast_module,a.output),indent=2))
