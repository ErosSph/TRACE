import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_comb_rule_registry as r


class RegistryTests(unittest.TestCase):
    def proposal(self, full=False):
        profile={'ast':dict(file='unused',module='Unknown.AST',program='Unknown.actual_program')}
        with patch.object(r.adapter,'load_ast',return_value={'source_sha256':'abc'}):
            return r.proposal(profile,full)

    def test_same_catalog_for_unknown_cpu_and_actual_program(self):
        _,text,count=self.proposal()
        self.assertIn('filter is_comb(processes Unknown.actual_program)',text)
        self.assertIn('certified_order producer_rules actual_order',text)
        self.assertIn('residual_order producer_rules actual_order',text)
        self.assertIn('ordered_check producer_rules transport_rules actual_order=true ->',text)
        self.assertEqual(count,2)
        self.assertNotIn('actual_order_check :',text)
        self.assertNotIn('Admitted',text)

    def test_complete_order_requires_actual_boolean_proof(self):
        _,text,count=self.proposal(True)
        self.assertIn('Lemma actual_order_check : ordered_check producer_rules transport_rules actual_order=true.',text)
        self.assertIn('exact(original_ordered_when_checked actual_order_check)',text)
        self.assertEqual(count,3)

    def test_real_runtime_fuel_not_syntax_default_or_forced_one(self):
        _,text,_=self.proposal()
        self.assertIn('lfp_fuel Unknown.actual_program',text)
        self.assertNotIn('lfp_fuel:=1',text)
        self.assertIn('Nat.ltb 0(statement_fuel Unknown.actual_program)',text)

    def test_actual_coq_counts_are_complete_and_unambiguous(self):
        log='REGISTRY_TOTAL 55\nREGISTRY_ACCEPTED 52\nREGISTRY_RESIDUAL 3\nREGISTRY_LFP_FUEL 9\n'
        self.assertEqual(r.counts(log),dict(total=55,accepted=52,residual=3,lfp_fuel=9))
        for bad in [log+'REGISTRY_TOTAL 55\n',log.replace('RESIDUAL 3','RESIDUAL 2'),log.replace('REGISTRY_LFP_FUEL 9','')]:
            with self.assertRaises(ValueError):r.counts(bad)

    def test_mode_is_not_implicitly_enabled_by_truthy_input(self):
        with self.assertRaises(ValueError):self.proposal('yes')

    def test_emission_cannot_escape_generated_root_or_overwrite_other_source(self):
        with tempfile.TemporaryDirectory()as directory:
            root=Path(directory).resolve();path=root/'src/Ex/Generated/New.v'
            with patch.object(r.adapter,'ROOT',root),patch.object(r,'proposal',return_value=(None,'candidate source',2)):
                with self.assertRaises(ValueError):r.emit_library({},root/'Other.v')
                r.emit_library({},path)
                self.assertEqual(path.read_text(),'candidate source')
                path.write_text('user change')
                with self.assertRaises(ValueError):r.emit_library({},path)
                self.assertEqual(path.read_text(),'user change')

    def test_source_injection_in_program_or_import_is_rejected_before_ast_load(self):
        for field in ('program','module'):
            for bad in ('P. Admitted.','P\nRequire Import Evil','fun x => x'):
                ast=dict(file='unused',module='New.AST',program='New.program');ast[field]=bad
                with patch.object(r.adapter,'load_ast')as read:
                    with self.assertRaisesRegex(ValueError,'symbols'):r.proposal({'ast':ast})
                    read.assert_not_called()

    def test_import_container_is_not_silently_coerced_to_characters(self):
        ast=dict(file='unused',module='New.AST',program='New.program',program_imports='Extra')
        with self.assertRaisesRegex(ValueError,'list of symbols'):r.proposal({'ast':ast})


if __name__=='__main__':unittest.main()
