import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_root_free_producers as root
import cpu_auto_pipeline as pipeline

def profile():return {'ast':{'module':'Renamed.AST','program':'Runtime.original','program_imports':['Original.Runtime']}}

class RootFreeGeneratorTests(unittest.TestCase):
    def test_pipeline_requires_checked_provider_and_public_assembly(self):
        for p,component in (({},None),(profile(),None),(profile(),{'accepted':False})):
            with patch.object(pipeline.root_free_producers,'check') as check:
                self.assertIsNone(pipeline.check_root_free_components(p,component,Path('/tmp'),1200))
            check.assert_not_called()
        p=profile()
        with patch.object(pipeline.root_free_producers,'check',return_value={'accepted':False}) as check:
            result=pipeline.check_root_free_components(p,{'accepted':True},Path('/tmp'),1200)
        self.assertFalse(result['accepted'])
        check.assert_called_once_with(p,Path('/tmp/known-producers'),Path('/tmp/root-free-producers'),
            1200,use_public_assembly=True)

    def test_original_program_and_checked_residual_order(self):
        text=root.proposal(profile())
        self.assertIn('ProducerIdempotent Runtime.original',text)
        self.assertIn('Known.remaining_order',text)
        self.assertIn('Original.Runtime.',text)
        self.assertIn('complete_registry_from_residual',text)
        self.assertEqual(text.count('eval vm_compute'),1)
        self.assertNotIn('Admitted',text)
        self.assertNotIn('Pico',text)

    def test_import_injection_rejected(self):
        p=profile();p['ast']['program']='Bad. Admitted.'
        with self.assertRaises(ValueError):root.proposal(p)

    def test_explicit_public_terms_preserve_obligation_statements(self):
        old=root.proposal(profile());new=root.proposal(profile(),True)
        import re
        pattern=r'(?ms)^((?:Theorem)\s+\w+.*?)(?=^Proof\.)'
        self.assertEqual(re.findall(pattern,old),re.findall(pattern,new))
        self.assertIn('exact(checked_root_free_order Runtime.original Known.remaining_order)',new)
        self.assertIn('known_then_root_free_complete Runtime.original Known.base_residual HC',new)
        self.assertEqual(new.count('eval vm_compute'),1)
        with self.assertRaises(ValueError):root.proposal(profile(),'true')

    def test_residual_positions_are_not_source_indices(self):
        r=root.parse('ROOT_FREE_TOTAL 4\nROOT_FREE_POSITIONS [0;2]\n')
        self.assertEqual(r,dict(before=4,newly_accepted=2,remaining=2,covered_residual_positions=[0,2]))
        for text in ('ROOT_FREE_TOTAL 1\nROOT_FREE_POSITIONS [1]\n',
                     'ROOT_FREE_TOTAL 4\nROOT_FREE_POSITIONS [2;0]\n',
                     'ROOT_FREE_TOTAL 0\nROOT_FREE_TOTAL 0\nROOT_FREE_POSITIONS []\n'):
            with self.assertRaises(ValueError):root.parse(text)

if __name__=='__main__':unittest.main()
