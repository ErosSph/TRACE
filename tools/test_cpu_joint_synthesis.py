import unittest
from cpu_joint_synthesis import render, PROOFS


def binding():
    return {'evidence_origin':'existing_local_component_proofs',
        'imports':['New.LocalProofs'],'binders':'words','arguments':['words'],
        'target':{'symbol':'New.target','arguments':[{'binder':'words'}]},
        'pending':{'symbol':'New.pending'},'physical':{'symbol':'New.Physical'},
        'search_fuel':3,'proofs':{p:{'symbol':'New.'+p} for p in PROOFS}}


class JointSynthesisTests(unittest.TestCase):
    def test_closed_term_generator_uses_new_joint_and_search(self):
        text = render(binding())
        self.assertIn('generated_certificate',text)
        self.assertIn('generated_search_rank',text)
        self.assertIn('generated_search_wait_decreases',text)
        self.assertIn('pinned_target_infinite_refinement',text)
        self.assertNotIn('Admitted',text)

    def test_missing_local_transfer_is_rejected(self):
        b = binding(); del b['proofs']['local_transfer']
        with self.assertRaisesRegex(ValueError,'six'):
            render(b)

    def test_streaming_uses_same_pinned_target_and_search(self):
        b=binding(); b['transfer_mode']='streaming'
        text=render(b)
        self.assertIn('generated_streaming_certificate',text)
        self.assertIn('New.target words',text)
        self.assertIn('generated_search_wait_decreases',text)

    def test_boundary_entry_uses_real_segments_without_fuel(self):
        b=binding(); b['transfer_mode']='boundary_entry'
        b['entry']={'symbol':'New.first_operand'}
        del b['search_fuel']; del b['proofs']['bounded_progress']
        text=render(b)
        self.assertIn('EntryCertificate',text)
        self.assertIn('generated_boundary_certificate',text)
        self.assertIn('generated_boundary_infinite_refinement',text)
        self.assertNotIn('search_rank',text)
        b['search_fuel']=3
        with self.assertRaisesRegex(ValueError,'search bound'): render(b)

    def test_unknown_semantic_mode_rejected(self):
        b=binding(); b['transfer_mode']='ignore_stalls'
        with self.assertRaisesRegex(ValueError,'transfer mode'): render(b)

    def test_typed_entry_literal_is_not_arbitrary_coq(self):
        from cpu_certificate_acceptance import render_proof_argument
        self.assertEqual(render_proof_argument({'nat':4},[]),'4%nat')
        for value in [True,-1,1025,'4; admit']:
            with self.assertRaises(ValueError): render_proof_argument({'nat':value},[])

    def test_no_free_form_llm_code_or_new_environment(self):
        b = binding(); b['proofs']['bounded_progress']={'symbol':'Axiom CPU_correct : False.'}
        with self.assertRaises(ValueError): render(b)
        b = binding(); b['evidence_origin']='new_invariant_discovered'
        with self.assertRaises(ValueError): render(b)

    def test_no_boolean_or_unbounded_fuel(self):
        for fuel in [True,-1,1025,'3']:
            b = binding(); b['search_fuel']=fuel
            with self.assertRaises(ValueError): render(b)

    def test_bzeeno_recipe_uses_local_not_old_global_proofs(self):
        import json
        import cpu_auto_adapter as adapter
        profile = json.loads((adapter.ROOT/'framework/auto-contract-profiles/bzeeno.json').read_text())
        text = render(profile['joint_binding'])
        self.assertIn('actual_local_transfers',text)
        self.assertIn('actual_bounded_progress',text)
        for forbidden in ['actual_ordered_cycle_safety','actual_ordered_wait_decreases','checked_certificate']:
            self.assertNotIn(forbidden,text)


if __name__ == '__main__': unittest.main()
