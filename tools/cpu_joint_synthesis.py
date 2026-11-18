"""Generate NEW Joint/ITree certificates from checked LOCAL component bindings.

Profiles are versioned framework inputs. Proof applications use a closed JSON
grammar (symbols/binders/application); no free-form model tactics are executed.
The design-specific local lemmas are reused, not claimed as newly discovered.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from cpu_certificate_acceptance import render_proof_argument, SYMBOL

PROOFS = ('architecture', 'startup', 'empty_queue', 'boot', 'local_transfer', 'bounded_progress')
BOUNDARY_PROOFS = PROOFS[:-1]


def render(binding: dict) -> str:
    if binding.get('evidence_origin') != 'existing_local_component_proofs':
        raise ValueError('explicit local proof provenance required')
    mode = binding.get('transfer_mode','queue')
    if mode not in {'queue','streaming','boundary_entry'}:
        raise ValueError('unknown transfer mode')
    required = BOUNDARY_PROOFS if mode == 'boundary_entry' else PROOFS
    if set(binding['proofs']) != set(required):
        raise ValueError('all six checked local obligations are required' if mode != 'boundary_entry'
                         else 'all five checked segment obligations are required')
    imports = binding['imports']
    opens = binding.get('open_modules', [])
    binders = binding['arguments']
    if not isinstance(imports, list) or not all(isinstance(x,str) and SYMBOL.fullmatch(x) for x in imports):
        raise ValueError('invalid framework imports')
    if not isinstance(opens,list) or not all(isinstance(x,str) and SYMBOL.fullmatch(x) for x in opens):
        raise ValueError('invalid framework modules')
    if not isinstance(binders,list) or not all(isinstance(x,str) and SYMBOL.fullmatch(x) and '.' not in x for x in binders):
        raise ValueError('invalid binders')
    fuel = binding.get('search_fuel')
    if mode != 'boundary_entry':
        if type(fuel) is not int or not 0 <= fuel <= 1024:
            raise ValueError('search fuel must be a bounded natural')
    elif fuel is not None:
        raise ValueError('segment certificates must not silently impose a search bound')
    term = lambda x: render_proof_argument(x, binders)
    target, pending, physical = (term(binding[k]) for k in ('target','pending','physical'))
    proofs = {k: term(binding['proofs'][k]) for k in required}
    scope = 'CPUGeneratedJointITree.CPUGeneratedJointITree'
    if mode == 'boundary_entry':
        boundary = 'CPUGeneratedBoundary.CPUGeneratedBoundary'
        certificate_type = f'{boundary}.EntryCertificate'
        entry = term(binding['entry'])
        constructor = [f' {boundary}.generated_boundary_certificate ({target}) ({pending}) ({physical})',
            f'   ({entry}) ' + ' '.join(f'({proofs[k]})' for k in required) + '.']
        lift = boundary+'.generated_boundary_infinite_refinement'
    else:
        certificate_type = 'CPUDesignTarget.CPUDesignTarget.Certificate'
        builder = 'generated_streaming_certificate' if mode == 'streaming' else 'generated_certificate'
        constructor = [f' {scope}.{builder} ({target}) ({pending}) ({physical})',
            f'   ({scope}.generated_search_rank ({target}) {fuel})',
            '   ' + ' '.join(f'({proofs[k]})' for k in PROOFS[:-1]),
            f'   ({scope}.generated_search_wait_decreases ({target}) ({pending}) ({physical})',
            f'     {fuel} ({proofs["bounded_progress"]})).']
        lift = 'CPUDesignTarget.CPUDesignTarget.pinned_target_infinite_refinement'
    lines = [
        '(** Generated from LOCAL component evidence, not an old global certificate. *)',
        'From Coq Require Import ZArith List.',
        'Require Import Ex.External.CPUGeneratedJointITree Ex.External.CPUDesignTarget',
        ' ' + ' '.join(imports) + '.',
        *(['Require Import Ex.External.CPUGeneratedBoundary.'] if mode == 'boundary_entry' else []),
        *(['Import ' + ' '.join(opens) + '.'] if opens else []),
        'Module GeneratedJointContract.',
        'Definition assembled ' + binding['binders'] + ' :',
        f' {certificate_type} ({target}) :=',
        *constructor,
        'Local Opaque assembled.',
        'Definition infinite_refinement ' + binding['binders'] + ' :=',
        f' {lift} ({target})',
        '   (assembled ' + ' '.join(binders) + ').',
        'End GeneratedJointContract.',
        'Goal True. idtac "AUTO_CONTRACT_CERTIFICATE_ASSUMPTIONS". exact I. Qed.',
        'Print Assumptions GeneratedJointContract.assembled.',
        'Goal True. idtac "AUTO_CONTRACT_INFINITE_ASSUMPTIONS". exact I. Qed.',
        'Print Assumptions GeneratedJointContract.infinite_refinement.',
        '',
    ]
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binding',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    source = render(json.loads(args.binding.read_text()))
    with args.output.open('x') as out:
        out.write(source)


if __name__ == '__main__':
    main()
