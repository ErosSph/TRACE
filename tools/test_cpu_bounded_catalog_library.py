import hashlib,json,tempfile,unittest
from pathlib import Path
from unittest.mock import patch
import cpu_bounded_catalog_library as library


class BoundedCatalogLibraryTests(unittest.TestCase):
    def test_portable_module_and_unchanged_original_program(self):
        profile={'ast':{'module':'Other.AST','program':'Other.runtime'}}
        with patch.object(library.catalog,'proposal',return_value=({},[],[],'catalog proof')):
            plan=library.sources(profile,'NewCPU',True)
        self.assertEqual([r[0] for r in plan],['NewCPUCatalog','NewCPUPhase'])
        self.assertEqual([r[2] for r in plan],[2,7])
        self.assertIn('Module Catalog := Ex.Generated.NewCPUCatalog.',plan[1][1])
        self.assertIn('CatalogShape Other.runtime',plan[1][1])
        self.assertNotIn('GeneratedDependencyCatalog.Catalog',plan[1][1])

    def test_unsafe_stems_rejected_before_ast_load(self):
        for stem in ('../x','A.B','Bad. Admitted.','',None):
            with patch.object(library.catalog,'proposal') as propose:
                with self.assertRaises(ValueError):library.sources({},stem,True)
            propose.assert_not_called()

    def test_unchecked_or_incomplete_provider_never_runs_native(self):
        for accepted,coverage,phase_ok in ((False,True,True),(True,False,True),(True,True,False)):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);provider=root/'p';candidate=root/'c';provider.mkdir();candidate.mkdir()
                (provider/'report.json').write_text(json.dumps({'accepted':accepted,
                    'metadata':{'converges':True,'covers_writers':coverage}}))
                (candidate/'report.json').write_text(json.dumps({'accepted':phase_ok,
                    'original_full_phase_under_catalog_shape_proved':phase_ok}))
                with patch.object(library,'run_stage') as native:
                    with self.assertRaises(ValueError):
                        library.publish({},provider,candidate,'Test',root/'out')
                native.assert_not_called();self.assertFalse((root/'out').exists())

    def test_source_or_budget_mismatch_rejected(self):
        digest=lambda s:hashlib.sha256(s.encode()).hexdigest()
        for changed in ('source','budget','program','ast','hash'):
            with tempfile.TemporaryDirectory() as tmp:
                root=Path(tmp);provider=root/'p';candidate=root/'c';provider.mkdir();candidate.mkdir()
                r=dict(accepted=True,metadata=dict(converges=True,covers_writers=True,budget=9),
                    actual_program='Original.p',ast_sha256='ast',source_sha256=digest('catalog'))
                q=dict(accepted=True,original_full_phase_under_catalog_shape_proved=True,
                    actual_program='Original.p',ast_sha256='ast',source_sha256=digest('phase'),
                    provider_source_sha256=digest('catalog'),original_iteration_budget=9,share_static_catalog=True)
                if changed=='budget':q['original_iteration_budget']=1
                if changed=='program':q['actual_program']='Other.p'
                if changed=='ast':q['ast_sha256']='other'
                if changed=='hash':q['source_sha256']='other'
                (provider/'report.json').write_text(json.dumps(r));(candidate/'report.json').write_text(json.dumps(q))
                (provider/'Catalog.v').write_text('catalog')
                (candidate/'Phase.v').write_text('different' if changed=='source' else 'phase')
                with patch.object(library.catalog,'proposal',return_value=({'source_sha256':'ast'},[],[],'catalog')), \
                     patch.object(library.phase,'phase_source',return_value='phase'):
                    with self.assertRaises(ValueError):
                        library.validate_provider({'ast':{'program':'Original.p'}},provider,candidate)

    def test_existing_user_library_never_overwritten(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);dest=root/'src/Ex/Generated';dest.mkdir(parents=True)
            (dest/'TestPhase.v').write_text('user content')
            with patch.object(library.adapter,'ROOT',root), \
                 patch.object(library,'validate_provider',return_value=({},{})), \
                 patch.object(library,'sources',return_value=[('TestCatalog','new',2),('TestPhase','changed',7)]), \
                 patch.object(library,'run_stage') as native:
                with self.assertRaises(ValueError):library.publish({},root,root,'Test',root/'out')
            native.assert_not_called()
            self.assertFalse((dest/'TestCatalog.v').exists())
            self.assertFalse((root/'out').exists())
            self.assertEqual((dest/'TestPhase.v').read_text(),'user content')


if __name__=='__main__':unittest.main()
