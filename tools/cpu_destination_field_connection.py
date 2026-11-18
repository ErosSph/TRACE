"""Connect raw RTL Rd fields to destinations extracted from original ExecuteI.

Sampled word identity and branch/phase conditions remain explicit premises.
No old CPU invariant is used, and a bit field is not a retirement certificate.
"""
import argparse
import hashlib
import json
import time
from pathlib import Path
import cpu_decoded_address_connection as inputs
import cpu_isa_destination_certificate as isa
from cpu_certificate_acceptance import run_stage


def render(ast, profile, exports):
    fields = inputs.fields
    p = profile['ast']['program']
    selected = fields.discover(ast)
    expressions = fields.paths.expressions.proposal(profile, selected['Sequential'])[2] if selected['Sequential'] else []
    procs = {x['root']: x['process'] for x in expressions}
    lines = ['From Coq Require Import ZArith List.',
        'Require Import GeneratedInstructionFields.InstructionFields GeneratedISADestinations.ISADestinations',
        ' Ex.External.CPUInstructionFields Ex.External.CPUISANormalizedInputs Lang.ExtendedSV Lang.ExtendedSVExpressionPath.',
        'Import ListNotations ExtendedSV ExtendedSVExpressionPath CPUInstructionFields CPUISANormalizedInputs.']
    used = []
    for row in exports:
        if row['field'] != 'Rd':
            continue
        name, root, source, width = [row[k] for k in ['name', 'root', 'source', 'width']]
        if row['kind'] == 'TaggedCombinational':
            args, sample, post = 'seed fixed', 'fixed', 'fixed'
            premises = [f'CombLFP {p} seed fixed']
            intro = 'HL'
            actual = f'root_{root}_actual_carrier seed fixed HL'
        elif row['kind'] == 'Combinational':
            args, sample, post = 'seed fixed', 'fixed', 'fixed'
            premises = [f'CombLFP {p} seed fixed',
                f'PathHolds fixed {row["original"]} {name}_choices']
            intro = 'HL HP'
            actual = f'{name}_actual seed fixed HL HP'
        else:
            args = 'ev pre'
            sample, post = f'(phase_driven_state {p} ev pre)', f'(PhaseSemantics {p} ev pre)'
            choices = row['base'][:-len('_phase')] + '_choices'
            premises = [f'changed_signal ev<>{root}%nat',
                f'process_matches_states pre {sample} {ast["module"]}.{procs[root]}=true',
                f'PathHolds {sample} {row["original"]} {choices}']
            intro = 'HE HT HP'
            actual = f'{name}_actual ev pre HE HT HP'
        lines += [f'Theorem {name}_destination {args} code instruction address rest:',
            ' ->\n'.join(premises) + ' ->',
            f'norm 32(read_signal {sample} {source})=norm 32 code ->',
            'Decode.decode Decode.RV32I code=Decode.IInstruction instruction ->',
            'destination_registers instruction=address::rest ->',
            f'norm {width}(read_signal {post} {root})=address.',
            f'Proof. intros {intro} HW HD HS.',
            f'pose proof({actual})as HF.',
            f'rewrite <-(normalized_field (read_signal {sample} {source}) Rd),HW,normalized_field in HF.',
            'exact(eq_trans HF(eq_sym(original_destination_address code instruction address rest HD HS))). Qed.',
            f'Print Assumptions {name}_destination.']
        used.append(row)
    return '\n'.join(lines) + '\n', used


def check(ast_path, ast_module, provider, isa_provider, output, tagged_provider=None):
    out = Path(output)
    out.mkdir(parents=True, exist_ok=False)
    ast, profile, paths = inputs.origin.raw_binding(ast_path, ast_module)
    profile['coq_load_paths'] = paths
    _, residuals, exports, field_source, _, _ = inputs.fields.proposal(profile)
    if residuals or not inputs.provider_ok(provider, field_source):
        raise ValueError('fresh raw field certificate must match checked provider')
    if tagged_provider is not None:
        import cpu_operand_tagged_origins as tagged
        _, tagged_source, _, _ = tagged.render(ast_path, ast_module)
        folder = Path(tagged_provider)
        tr = json.loads((folder/'report.json').read_text())
        tf = folder/'TaggedAddresses.v'
        if not (tagged_source is not None and tr.get('accepted') is True
                and tr.get('assumptions_closed') is True
                and tr.get('coqc_exit') == tr.get('coqchk_exit') == 0
                and tr.get('source_sha256') == hashlib.sha256(tagged_source.encode()).hexdigest()
                and tf.read_text() == tagged_source and tf.with_suffix('.vo').is_file()):
            raise ValueError('raw full-width tagged field certificate mismatch')
        _, remaining, tagged_rows, _, _, _ = tagged.tagged.proposal(profile, opaque_program_connection=True)
        if remaining:
            raise ValueError('unproved tagged field residuals')
        exports += [dict(kind='TaggedCombinational', name=f'tagged_root_{r["root"]}',
                         root=r['root'], source=r['origin']['terminal'], width=6, field=r['field'])
                    for r in tagged_rows if r['field']=='Rd']
    isa_provider = Path(isa_provider)
    isa_source = isa.render((isa.synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text())
    proof = isa_provider/'ISADestinations.v'
    rp = json.loads((isa_provider/'report.json').read_text())
    if not (rp.get('accepted') is True and rp.get('original_assumptions_only') is True
            and rp.get('coqc_exit') == rp.get('coqchk_exit') == 0
            and rp.get('source_sha256') == hashlib.sha256(isa_source.encode()).hexdigest()
            and proof.read_text() == isa_source and proof.with_suffix('.vo').is_file()):
        raise ValueError('original ISA destination certificate mismatch')
    source, used = render(ast, profile, exports)
    source = f'Require Import {ast_module}.\n' + source
    if tagged_provider is not None:
        source = 'Require Import GeneratedTaggedAddresses.TaggedAddresses.\n' + source
    file = out/'DestinationFields.v'
    file.write_text(source)
    report = dict(accepted=False, rd_fields=len(used), old_inv_read=False,
        instruction_scope=isa.synthesis.instruction_scopes.for_input(ast_path, ast_module),
        current_token_identity_proved=False, actual_retirement_binding_proved=False,
        complete_R_generated=False, source_sha256=hashlib.sha256(source.encode()).hexdigest())
    if used:
        flags = list(inputs.origin.pending.rtl.framework.FLAGS)
        for path in paths:
            flags += ['-R', path['directory'], path['namespace']]
        if tagged_provider is not None:
            flags += ['-R', str(Path(tagged_provider).resolve()), 'GeneratedTaggedAddresses']
        flags += ['-R', str(Path(provider).resolve()), 'GeneratedInstructionFields',
                  '-R', str(isa_provider.resolve()), 'GeneratedISADestinations',
                  '-R', str(out.resolve()), 'GeneratedDestinationFields']
        start = time.monotonic()
        c, timeout = run_stage([str(inputs.origin.ROOT/'_opam/bin/coqc'), '-time', *flags, str(file.resolve())], out/'coqc.log', 1200)
        report.update(coqc_exit=c.returncode, coqc_timed_out=timeout)
        if c.returncode == 0:
            closed = c.stdout.count('Closed under the global context') == len(used) and 'Axioms:' not in c.stdout
            k, timeout = run_stage([str(inputs.origin.ROOT/'_opam/bin/coqchk'), '-silent', *flags,
                '-norec', 'GeneratedDestinationFields.DestinationFields'], out/'coqchk.log', max(.1, 1200-(time.monotonic()-start)))
            report.update(coqchk_exit=k.returncode, coqchk_timed_out=timeout,
                          assumptions_closed=closed, accepted=closed and k.returncode == 0)
        report['seconds'] = time.monotonic()-start
    else:
        report['status'] = 'no_supported_rd_field'
    (out/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ['ast', 'ast-module', 'provider', 'isa-provider', 'output']:
        parser.add_argument('--'+arg, required=True)
    parser.add_argument('--tagged-provider')
    a = parser.parse_args()
    result = check(a.ast, a.ast_module, a.provider, a.isa_provider, a.output, a.tagged_provider)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result['accepted'] else 1)
