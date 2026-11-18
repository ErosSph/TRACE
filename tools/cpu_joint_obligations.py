"""Emit auditable residuals for the NEW pending-effect invariant, not old Inv.

This is an obligation planner, not a proof synthesizer.  Candidate roles and
old checked contracts cannot discharge these obligations.  A future backend
must supply proof terms checked against the pinned target and original ISA.
"""
from __future__ import annotations
import hashlib
from pathlib import Path


ROLE_OBLIGATIONS = (
    ('commit_identity', 'Original observer identifies completed, non-flushed instructions, including instructions without RF writes.'),
    ('architecture_binding', 'Physical pins retired PC/nextPC/RF/ROM/RAM and the pending-effect frontier; speculative agreement alone is insufficient.'),
    ('instruction_identity', 'Pending tokens identify actual instructions in architecture order across real pipeline phases.'),
    ('operand_freshness', 'Selected operands equal the newest matching producer or the retired RF value.'),
    ('stall_flush_validity', 'Stalls preserve token ownership; flush removes only effects absent from the valid pending chain, or proves rollback.'),
    ('memory_correspondence', 'Requests, responses, byte lanes and memory updates belong to the matching instruction and environment.'),
    ('initialization', 'Actual reset/startup yields empty certified queue and Physical boot initial initial.'),
    ('local_cycle_transfer', 'Actual cycle retires exactly the original observer prefix, preserves its suffix, and admits checked ISA effects.'),
    ('progress', 'A concrete well-founded silent-cycle rank decreases under the declared response environment.'),
)


def plan(profile: dict, root: Path) -> dict:
    """Record exact imported syntax/runtime while keeping semantic holes open."""
    ast = profile['ast']
    source = Path(ast['file'])
    if not source.is_absolute():
        source = root / source
    result = {
        'schema_version': 1,
        'status': 'unproved_generation_obligations',
        'design': profile.get('design', 'new-design'),
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'syntax_module': ast['module'],
        'actual_program': ast['program'],
        'runtime_fields': dict(profile.get('fields', {})),
        'existing_global_evidence_discharges_new_obligations': False,
        'role_suggestions_are_proofs': False,
        'goal_complete': False,
        'invariant': 'exists frontier, Physical s retired frontier /\\ EffectChain checked_pc_effect retired (pending s) frontier',
        'isa_effect': 'PC identity AND original FormalSpec.run1 succeeds',
        'composition_theorem': 'CPUGeneratedJointITree.CPUGeneratedJointITree.generated_infinite_refinement',
        'required_checked_arguments': [
            'Hphysical: Physical implies pinned target_arch_relation',
            'Hstartup: original reset scheduler equivalent to original boot scheduler',
            'Hempty: pending original_boot = []',
            'Hboot: Physical original_boot original_isa_initial original_isa_initial',
            'Hlocal: LocalCycleTransfers for original cycle and original commit observer',
            'Hrank: OrderedWaitDecreases for GeneratedJoint and concrete rank',
        ],
        'automatic_rank_alternative': {
            'theorem': 'CPUGeneratedJointITree.CPUGeneratedJointITree.generated_infinite_refinement_with_search',
            'rank': 'distance returned by first_commit over ORIGINAL target_cycle and target_commits',
            'replaces': 'Hrank',
            'requires': 'Hbounded: forall s a, GeneratedJoint s a -> exists distance, first_commit fuel s = Some distance',
            'status': 'design_bound_unproved',
            'may_add_environment_assumption': False,
        },
        'obligations': [
            {'id': name, 'statement': text, 'status': 'unproved',
             'may_assume_cpu_correctness': False}
            for name, text in ROLE_OBLIGATIONS
        ],
        'restrictions': [
            'No arbitrary Coq text from an LLM is executed by this planner.',
            'No new program restriction silently replaces the pinned domain.',
            'A proof of the generic composition theorem is not a proof of its design-specific premises.',
        ],
    }
    mode = profile.get('joint_binding', {}).get('transfer_mode', 'queue')
    result['configured_transfer_mode'] = mode
    if mode == 'boundary_entry':
        result['composition_theorem'] = 'CPUGeneratedBoundary.CPUGeneratedBoundary.generated_boundary_infinite_refinement'
        result['required_checked_arguments'] = [
            'Hphysical: Physical implies ORIGINAL target_arch_relation',
            'Hstartup: ORIGINAL reset scheduler equivalent to checked entry scheduler',
            'Hempty: pending checked_entry = []',
            'Hentry: Physical checked_entry ORIGINAL_isa_initial ORIGINAL_isa_initial',
            'Hlocal: actual finite FirstVisibleCycle and StreamingTransfer restore GeneratedJoint',
        ]
        result['automatic_rank_alternative'] = {
            'status':'not_required_for_finite_commit_segments',
            'progress':'REAL finite FirstVisibleCycle is part of every local segment witness',
            'may_add_environment_assumption':False,
        }
    elif mode == 'streaming':
        result['composition_theorem'] = 'CPUGeneratedJointITree.CPUGeneratedJointITree.generated_streaming_certificate'
        result['required_checked_arguments'][4] = 'Hlocal: LocalStreamingTransfers for ORIGINAL cycle and observer'
    return result
