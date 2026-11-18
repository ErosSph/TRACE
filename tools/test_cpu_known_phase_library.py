import unittest
import json
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_known_phase_library as library
import cpu_known_producers as known
import cpu_phase_from_known as phase
import cpu_auto_pipeline as pipeline

def profile():
    return {'ast':{'module':'Renamed.AST','program':'Runtime.original',
        'program_imports':['Original.Runtime']}}

class PortableKnownPhaseTests(unittest.TestCase):
    def test_pipeline_never_publishes_missing_or_unchecked_phase(self):
        for component in (None,{'accepted':False},
                          {'accepted':True,'original_full_phase_proved':False}):
            with patch.object(pipeline.known_phase_library,'publish') as publish:
                result=pipeline.persist_known_phase({'known_phase_library_stem':'Other'},component,Path('/tmp'),1200)
            publish.assert_not_called();self.assertFalse(result['accepted'])

    def test_pipeline_optional_export_passes_exact_provider_paths(self):
        with patch.object(pipeline.known_phase_library,'publish',return_value={'accepted':True}) as publish:
            self.assertIsNone(pipeline.persist_known_phase({},None,Path('/tmp'),1200))
            p={'known_phase_library_stem':'Other'}
            result=pipeline.persist_known_phase(p,{'accepted':True,'original_full_phase_proved':True},Path('/tmp'),1200)
        self.assertTrue(result['accepted'])
        publish.assert_called_once_with(p,Path('/tmp/known-producers'),Path('/tmp/phase-from-known'),
            'Other',Path('/tmp/persistent-known-phase'),1200)

    def test_portable_imports_and_original_program(self):
        with patch.object(known.registry,'proposal',return_value=({'source_sha256':'test'},'',2)):
            rows=library.sources(profile(),'NewCPUAuto')
        self.assertEqual([r[0] for r in rows],['NewCPUAuto'+s for s in ('Known','Complete','Eligibility','Phase')])
        self.assertEqual([r[2] for r in rows],[2,1,1,2])
        for _,text,_ in rows:
            self.assertNotIn('GeneratedKnownProducers.',text)
            self.assertNotIn('GeneratedKnownPhase.',text)
            self.assertIn('Runtime.original',text)
            self.assertNotIn('Admitted',text)
        self.assertIn('Module Known := Ex.Generated.NewCPUAutoKnown.',rows[1][1])
        self.assertIn('original_positive_phase Runtime.original',rows[3][1])

    def test_unsafe_stems_rejected_before_generation(self):
        for stem in ('../Bad','A.B','Bad. Admitted.','',None):
            with self.assertRaises(ValueError):library.sources(profile(),stem)

    def test_parameterized_imports_reject_injection(self):
        for bad in ('Bad. Admitted.','../Bad',None):
            with self.assertRaises(ValueError):known.completion_source(profile(),bad)
            with self.assertRaises(ValueError):phase.header(profile(),bad)
            with self.assertRaises(ValueError):phase.phase_source(profile(),eligibility_module=bad)

    def test_incomplete_or_ineligible_evidence_never_publishes(self):
        for complete,eligible in ((False,True),(True,False),(False,False)):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);provider=root/'provider';candidate=root/'candidate'
                provider.mkdir();candidate.mkdir()
                (provider/'report.json').write_text(json.dumps({'accepted':True,
                    'complete_original_producer_list_proved':complete}))
                (candidate/'report.json').write_text(json.dumps({'accepted':eligible,
                    'original_full_phase_proved':eligible}))
                with patch.object(library,'run_stage') as native:
                    with self.assertRaises(ValueError):
                        library.publish(profile(),provider,candidate,'OtherCPU',root/'out')
                native.assert_not_called()
                self.assertFalse((root/'out').exists())

    def test_changed_existing_library_refused_before_any_writes(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);dest=root/'src/Ex/Generated';dest.mkdir(parents=True)
            (dest/'OtherCPUComplete.v').write_text('user content')
            plan=[('OtherCPUKnown','new proof',2),('OtherCPUComplete','different proof',1)]
            with patch.object(library.adapter,'ROOT',root), \
                 patch.object(library,'validate_provider',return_value={}), \
                 patch.object(library,'sources',return_value=plan), \
                 patch.object(library,'run_stage') as native:
                with self.assertRaises(ValueError):
                    library.publish(profile(),root,root,'OtherCPU',root/'out')
            native.assert_not_called()
            self.assertFalse((dest/'OtherCPUKnown.v').exists())
            self.assertEqual((dest/'OtherCPUComplete.v').read_text(),'user content')

if __name__=='__main__':unittest.main()
