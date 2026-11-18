import unittest
from unittest.mock import patch
import cpu_bounded_catalog_phase as phase

class BoundedCatalogPhaseTests(unittest.TestCase):
    def test_explicit_original_shape_event_and_budget(self):
        p={'ast':{'module':'Renamed.AST','program':'Runtime.original','program_imports':['Original.Runtime']}}
        text=phase.phase_source(p)
        self.assertIn('CatalogEvent Runtime.original Catalog.actual_catalog ev',text)
        self.assertIn('CatalogShape Runtime.original Catalog.actual_catalog pre',text)
        self.assertIn('bounded_catalog_checksb Runtime.original',text)
        self.assertIn('Catalog.actual_order Catalog.actual_catalog_sound',text)
        self.assertNotIn('lfp_fuel:=1',text)
        self.assertNotIn('Admitted',text)
        self.assertEqual(text.count('Print Assumptions'),4)

    def test_untrusted_runtime_import_rejected(self):
        with self.assertRaises(ValueError):phase.phase_source({'ast':{'module':'Bad. Admitted.','program':'P.p'}})

    def test_portable_catalog_import_is_typed_alias_not_text_injection(self):
        p={'ast':{'module':'Renamed.AST','program':'Runtime.original'}}
        text=phase.phase_source(p,True,'Ex.Generated.ExampleCatalog')
        self.assertIn('Module Catalog := Ex.Generated.ExampleCatalog.',text)
        self.assertNotIn('GeneratedDependencyCatalog.Catalog',text)
        self.assertIn('Catalog.actual_catalog_sound',text)
        for name in ('Bad. Admitted.',None,'Bad\nX','-R'):
            with self.assertRaises(ValueError):phase.phase_source(p,True,name)

    def test_verified_sharing_preserves_all_original_public_obligations(self):
        import re
        p={'ast':{'module':'Renamed.AST','program':'Runtime.original'}}
        old=phase.phase_source(p);new=phase.phase_source(p,True)
        declarations=lambda text:dict((name,decl) for decl,name in re.findall(
            r'(?ms)^((?:Lemma|Theorem)\s+(\w+)\b.*?)(?=^Proof\.)',text))
        before=declarations(old);after=declarations(new)
        for name,decl in before.items():self.assertEqual(decl,after[name])
        self.assertIn('Eval vm_compute in Catalog.actual_catalog',new)
        self.assertIn('Catalog.actual_catalog=cached_catalog',new)
        self.assertIn('catalog_outputs cached_catalog=cached_outputs',new)
        self.assertIn('eq_trans(f_equal(bounded_catalog_checksb Runtime.original)',new)
        self.assertEqual(new.count('Print Assumptions'),7)
        self.assertNotIn('Admitted',new)
        self.assertNotIn('cast_no_check',new)
        with self.assertRaises(ValueError):phase.phase_source(p,'true')

if __name__=='__main__':unittest.main()
