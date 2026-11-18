import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_auto_pipeline as pipeline


class BoundedCatalogPipelineTests(unittest.TestCase):
    def test_optional_and_missing_ast_do_not_invoke_native(self):
        with patch.object(pipeline.dependency_catalog,'check') as check:
            self.assertIsNone(pipeline.check_bounded_catalog_components({},Path('/tmp'),1200))
            result=pipeline.check_bounded_catalog_components({'bounded_catalog_library_stem':'New'},Path('/tmp'),1200)
        check.assert_not_called();self.assertFalse(result['accepted'])

    def test_incomplete_catalog_does_not_launch_phase(self):
        p={'ast':{},'bounded_catalog_library_stem':'Other'}
        for accepted,converges,coverage in ((False,True,True),(True,False,True),(True,True,False)):
            with patch.object(pipeline.dependency_catalog,'check',return_value=dict(accepted=accepted,
                    metadata=dict(converges=converges,covers_writers=coverage))), \
                 patch.object(pipeline.bounded_catalog_phase,'check') as phase, \
                 patch.object(pipeline.bounded_catalog_library,'publish') as publish:
                result=pipeline.check_bounded_catalog_components(p,Path('/tmp'),1200)
            self.assertFalse(result['accepted']);phase.assert_not_called();publish.assert_not_called()

    def test_failed_phase_does_not_publish(self):
        p={'ast':{},'bounded_catalog_library_stem':'Other'}
        for accepted,proved in ((False,True),(True,False)):
            with patch.object(pipeline.dependency_catalog,'check',return_value=dict(accepted=True,
                    metadata=dict(converges=True,covers_writers=True))), \
                 patch.object(pipeline.bounded_catalog_phase,'check',return_value=dict(accepted=accepted,
                    original_full_phase_under_catalog_shape_proved=proved)), \
                 patch.object(pipeline.bounded_catalog_library,'publish') as publish:
                result=pipeline.check_bounded_catalog_components(p,Path('/tmp'),1200)
            self.assertFalse(result['accepted']);publish.assert_not_called()

    def test_success_publishes_exact_original_provider_without_claiming_itree(self):
        p={'ast':{},'bounded_catalog_library_stem':'Other'};out=Path('/tmp')
        with patch.object(pipeline.dependency_catalog,'check',return_value=dict(accepted=True,
                metadata=dict(converges=True,covers_writers=True))), \
             patch.object(pipeline.bounded_catalog_phase,'check',return_value=dict(accepted=True,
                original_full_phase_under_catalog_shape_proved=True)) as phase, \
             patch.object(pipeline.bounded_catalog_library,'publish',return_value={'accepted':True}) as publish:
            result=pipeline.check_bounded_catalog_components(p,out,1200)
        phase.assert_called_once_with(p,out/'dependency-catalog',out/'bounded-catalog-phase',
            1200,share_static_catalog=True)
        publish.assert_called_once_with(p,out/'dependency-catalog',out/'bounded-catalog-phase',
            'Other',out/'persistent-bounded-catalog',1200)
        self.assertTrue(result['accepted'])
        for key in ('actual_consumer_reconnected','existing_shape_compatibility_proved',
                    'new_global_invariant_synthesized','itree_refinement_proved'):
            self.assertFalse(result[key])


if __name__=='__main__':unittest.main()
