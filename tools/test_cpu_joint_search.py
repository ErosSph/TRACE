import copy
import json
from pathlib import Path
import unittest

from cpu_joint_search import render_search
from cpu_joint_synthesis import PROOFS


def binding():
    return {'evidence_origin': 'existing_local_component_proofs',
            'imports': ['New.LocalProofs'], 'binders': 'words', 'arguments': ['words'],
            'target': {'symbol': 'New.target', 'arguments': [{'binder': 'words'}]},
            'pending': {'symbol': 'New.pending'}, 'physical': {'symbol': 'New.Physical'},
            'search_fuel': 3,
            'proofs': {role: {'symbol': 'New.witness' + str(n)} for n, role in enumerate(PROOFS)}}


class JointSearchTests(unittest.TestCase):
    def test_symbol_only_search_infers_arguments_with_fixed_tactics(self):
        b = binding()
        b['lemma_candidates'] = ['New.witness', 'eq_refl', 'New.witness']
        del b['proofs']
        text = render_search(b)
        self.assertEqual(text.count('solve [ eapply New.witness; eassumption ]'), 6)
        self.assertEqual(text.count('solve [ eapply eq_refl; eassumption ]'), 6)
        self.assertNotIn('exact (New.witness)', text)
        self.assertIn('generated_search_wait_decreases', text)

    def test_symbol_only_quantified_transfer_gets_repeated_intro_fallback(self):
        b = binding(); b['lemma_candidates'] = ['New.transfer', 'New.other']
        text = render_search(b)
        direct = 'solve [ eapply New.transfer; eassumption ]'
        fallback = 'solve [ repeat intro; eapply New.transfer; eassumption ]'
        self.assertEqual(text.count(direct), 6)
        self.assertEqual(text.count(fallback), 6)
        for line in text.splitlines():
            if 'first [' in line:
                self.assertLess(line.index(direct), line.index(fallback))
                self.assertLess(line.index(fallback), line.index('eapply New.other'))

    def test_symbol_only_pool_rejects_tactics_applications_and_bad_bounds(self):
        for pool in [[], None, {}, ['New.x'] * 33, ['New.x words'],
                     ['New.x; admit'], ['solve [auto]'], [{'symbol': 'New.x'}], [True]]:
            b = binding(); b['lemma_candidates'] = pool
            with self.subTest(pool=pool), self.assertRaises(ValueError): render_search(b)
        b = binding(); b['lemma_candidates'] = ['New.x']
        b['proof_candidates'] = [{'symbol': 'New.x'}]
        with self.assertRaisesRegex(ValueError, 'mutually exclusive'): render_search(b)

    def test_symbol_only_boundary_search_keeps_five_unbounded_segment_slots(self):
        b = binding(); b['transfer_mode'] = 'boundary_entry'
        b['entry'] = {'symbol': 'New.entry'}; del b['search_fuel']
        b['lemma_candidates'] = ['New.witness']
        text = render_search(b)
        self.assertEqual(text.count('solve [ eapply New.witness; eassumption ]'), 5)
        self.assertNotIn('generated_search_rank', text)

    def test_actual_bzeeno_symbol_search_never_restores_manual_arguments(self):
        root = Path(__file__).resolve().parents[1]
        profile = json.loads((root / 'framework/auto-contract-profiles/bzeeno.json').read_text())
        b = profile['joint_binding']
        b['lemma_candidates'] = [node['symbol'] for node in b.pop('proofs').values()]
        searches = [line for line in render_search(b).splitlines() if 'first [' in line]
        self.assertEqual(len(searches), 6)
        for line in searches:
            self.assertNotIn(' words', line)
            self.assertNotIn(' cert', line)
            self.assertIn('eassumption', line)

    def test_every_slot_tries_same_pool_not_role_assignment(self):
        source = render_search(binding())
        searches = [line.strip() for line in source.splitlines() if 'first [' in line]
        self.assertEqual(len(searches), 6)
        self.assertEqual(len(set(line.removeprefix('- ') for line in searches)), 1)
        for n in range(6):
            self.assertEqual(source.count('exact (New.witness' + str(n) + ')'), 6)

    def test_role_keys_and_insertion_order_are_irrelevant(self):
        original = binding()
        shuffled = copy.deepcopy(original)
        shuffled['proofs'] = {str(n): value for n, value in
                              enumerate(reversed(list(original['proofs'].values())))}
        self.assertEqual(render_search(original), render_search(shuffled))

    def test_explicit_candidates_override_missing_or_invalid_rolemap(self):
        b = binding()
        b['proof_candidates'] = [{'symbol': 'New.only'}, {'symbol': 'New.only'}]
        b['proofs'] = 'not consulted'
        text = render_search(b)
        self.assertEqual(text.count('exact (New.only)'), 6)
        self.assertNotIn('New.witness', text)
        del b['proofs']
        self.assertEqual(render_search(b), text)

    def test_explicit_priority_is_preserved_and_pool_bound_is_enforced(self):
        b = binding()
        b['proof_candidates'] = [{'symbol': 'New.z'}, {'symbol': 'New.a'}]
        text = render_search(b)
        self.assertIn('first [ exact (New.z) | exact (New.a) ].', text)
        b = binding()
        b['proofs'] = {str(n): {'symbol': 'New.x' + str(n)} for n in range(33)}
        with self.assertRaises(ValueError): render_search(b)
        b['proofs'] = {str(n): {'symbol': 'New.same'} for n in range(40)}
        self.assertEqual(render_search(b).count('exact (New.same)'), 6)

    def test_cycle_modes_keep_pinned_generic_constructors_and_audits(self):
        for mode, builder in [('queue', 'generated_certificate'),
                              ('streaming', 'generated_streaming_certificate')]:
            b = binding(); b['transfer_mode'] = mode
            text = render_search(b)
            self.assertIn(builder, text)
            self.assertIn('generated_search_wait_decreases', text)
            self.assertIn('pinned_target_infinite_refinement', text)
            self.assertIn('AUTO_CONTRACT_CERTIFICATE_ASSUMPTIONS', text)
            self.assertIn('AUTO_CONTRACT_INFINITE_ASSUMPTIONS', text)

    def test_boundary_has_five_searches_no_uniform_fuel(self):
        b = binding(); b['transfer_mode'] = 'boundary_entry'
        b['entry'] = {'symbol': 'New.entry'}
        del b['search_fuel']
        text = render_search(b)
        self.assertEqual(text.count('first ['), 5)
        self.assertIn('generated_boundary_certificate', text)
        self.assertIn('generated_boundary_infinite_refinement', text)
        self.assertNotIn('generated_search_rank', text)
        b['search_fuel'] = 3
        with self.assertRaises(ValueError): render_search(b)

    def test_missing_empty_oversized_or_malformed_pool_rejected(self):
        for pool in [[], {}, None, [{'symbol': 'New.x'}] * 33,
                     ['exact New.x'], [{'symbol': 'New.x; admit'}],
                     [{'tactic': 'auto'}], [{'binder': 'unbound'}],
                     [{'nat': True}]]:
            b = binding(); b['proof_candidates'] = pool
            with self.subTest(pool=pool), self.assertRaises(ValueError): render_search(b)
        for value in [{}, None, []]:
            b = binding(); b['proofs'] = value
            with self.assertRaises(ValueError): render_search(b)
        b = binding(); del b['proofs']
        with self.assertRaises(ValueError): render_search(b)

    def test_bad_modes_provenance_and_terms_rejected(self):
        for key, value in [('transfer_mode', 'unbounded'), ('search_fuel', True),
                           ('evidence_origin', 'old_global_certificate'),
                           ('pending', {'symbol': 'foo. Admitted.'})]:
            b = binding(); b[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): render_search(b)

    def test_real_profiles_only_reuse_local_candidate_witnesses(self):
        root = Path(__file__).resolve().parents[1]
        for path in (root / 'framework/auto-contract-profiles').glob('*.json'):
            profile = json.loads(path.read_text())
            if 'joint_binding' not in profile:
                continue
            text = render_search(profile['joint_binding'])
            for forbidden in ['all38_ordered_cycle_safety', 'all38_progress',
                              'actual_ordered_cycle_safety', 'actual_ordered_wait_decreases',
                              '.checked_certificate', 'Admitted', 'admit']:
                self.assertNotIn(forbidden, text)

    def test_registered_symbol_pools_include_the_checked_annotation_witnesses(self):
        root = Path(__file__).resolve().parents[1]
        for path in (root / 'framework/auto-contract-profiles').glob('*.json'):
            binding = json.loads(path.read_text()).get('joint_binding', {})
            if 'lemma_candidates' in binding:
                with self.subTest(profile=path.stem):
                    self.assertTrue({node['symbol'] for node in binding['proofs'].values()}
                        <= set(binding['lemma_candidates']))


if __name__ == '__main__':
    unittest.main()
