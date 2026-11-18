"""Generate bounded, type-directed selection of checked local proof witnesses.

The candidate pool supplies closed applicative terms or opt-in lemma symbols,
never tactics. Every certificate slot searches the SAME pool; Coq checks the
witness and may infer lemma arguments from the goal and local assumptions.
This is witness selection/instantiation, not invariant discovery or proof
synthesis from RTL. Headers and modes remain the trusted synthesis inputs.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from cpu_certificate_acceptance import render_proof_argument, SYMBOL
from cpu_joint_synthesis import render, PROOFS, BOUNDARY_PROOFS

MAX_CANDIDATES = 32


def _pool(binding: dict) -> list[dict]:
    if 'lemma_candidates' in binding:
        if 'proof_candidates' in binding:
            raise ValueError('lemma_candidates and proof_candidates are mutually exclusive')
        symbols = binding['lemma_candidates']
        if (not isinstance(symbols, list) or not 1 <= len(symbols) <= MAX_CANDIDATES
                or not all(isinstance(name, str) and SYMBOL.fullmatch(name) for name in symbols)):
            raise ValueError('lemma candidate pool must contain 1 to 32 valid symbols')
        return [{'symbol': name} for name in dict.fromkeys(symbols)]
    explicit = 'proof_candidates' in binding
    if explicit:
        nodes = binding['proof_candidates']
        if not isinstance(nodes, list) or not nodes or len(nodes) > MAX_CANDIDATES:
            raise ValueError('proof candidate pool must contain 1 to 32 terms')
    else:
        proofs = binding.get('proofs')
        if not isinstance(proofs, dict) or not proofs:
            raise ValueError('missing proof candidate pool')
        # The role keys are deliberately never consulted for assignment.
        nodes = list(proofs.values())
    arguments = binding.get('arguments')
    if not isinstance(arguments, list):
        raise ValueError('invalid binders')
    unique = {}
    for node in nodes:
        rendered = render_proof_argument(node, arguments)
        unique.setdefault(rendered, node)
    if not unique or len(unique) > MAX_CANDIDATES:
        raise ValueError('proof candidate pool must contain 1 to 32 distinct terms')
    # An explicit pool may prioritize candidates. Fallback mapping insertion
    # order and role labels do not affect even the emitted search ordering.
    return list(unique.values()) if explicit else [unique[k] for k in sorted(unique)]


def render_search(binding: dict) -> str:
    if not isinstance(binding, dict):
        raise ValueError('invalid joint binding')
    pool = _pool(binding)
    mode = binding.get('transfer_mode', 'queue')
    required = BOUNDARY_PROOFS if mode == 'boundary_entry' else PROOFS
    # Reuse the current trusted header/mode validation and audit/lifting text.
    # Dummy role entries only satisfy that renderer's input schema; none is
    # used as a slot assignment in the output below.
    normalized = dict(binding)
    normalized['proofs'] = {role: pool[0] for role in required}
    source = render(normalized)
    arguments = binding['arguments']
    term = lambda node: render_proof_argument(node, arguments)
    target, pending, physical = (term(binding[k]) for k in ('target', 'pending', 'physical'))
    candidates = [term(node) for node in pool]
    if 'lemma_candidates' in binding:
        # Both tactics are fixed framework code. solve prevents a candidate
        # from being accepted merely because eapply created unresolved goals.
        # Some local interfaces reduce to universally quantified transfer
        # obligations. Preserve the direct application attempt first, then
        # expose their quantified state/evidence before trying the same lemma.
        branches = [branch for candidate in candidates for branch in (
            'solve [ eapply ' + candidate + '; eassumption ]',
            'solve [ repeat intro; eapply ' + candidate + '; eassumption ]')]
    else:
        branches = ['exact (' + candidate + ')' for candidate in candidates]
    search = 'first [ ' + ' | '.join(branches) + ' ].'
    scope = 'CPUGeneratedJointITree.CPUGeneratedJointITree'
    if mode == 'boundary_entry':
        boundary = 'CPUGeneratedBoundary.CPUGeneratedBoundary'
        certificate_type = boundary + '.EntryCertificate'
        application = (f'{boundary}.generated_boundary_certificate ({target}) '
                       f'({pending}) ({physical}) ({term(binding["entry"])})')
        holes = 5
    else:
        certificate_type = 'CPUDesignTarget.CPUDesignTarget.Certificate'
        builder = 'generated_streaming_certificate' if mode == 'streaming' else 'generated_certificate'
        fuel = binding['search_fuel']
        application = (f'{scope}.{builder} ({target}) ({pending}) ({physical}) '
                       f'({scope}.generated_search_rank ({target}) {fuel})')
        holes = 6
    lines = [
        'Definition assembled ' + binding['binders'] + ' :',
        f' {certificate_type} ({target}).',
        'Proof.',
        ' refine (' + application + ' ' + ' '.join('_' for _ in range(holes)) + ').',
        *[' - ' + search for _ in range(5)],
    ]
    if mode != 'boundary_entry':
        lines += [f' - apply ({scope}.generated_search_wait_decreases ({target}) ({pending}) ({physical}) {fuel}).',
                  '   ' + search]
    lines += ['Defined.', '']
    start = source.index('Definition assembled ')
    end = source.index('Local Opaque assembled.', start)
    return source[:start] + '\n'.join(lines) + source[end:]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binding', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source = render_search(json.loads(args.binding.read_text()))
    with args.output.open('x') as output:
        output.write(source)


if __name__ == '__main__':
    main()
