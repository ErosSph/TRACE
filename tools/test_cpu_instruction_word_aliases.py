import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_auto_adapter as a
import cpu_instruction_word_aliases as w


def proc(name,kind,body):
    term=a.Parser(body).complete()
    return dict(name=name,kind=kind,body=term,
        writers=sorted({a.root_of(n.args[2]) for n in a.walk(term) if n.name=='SAssign'}))


class InstructionWordAliasTests(unittest.TestCase):
    def test_persistent_source_matching_is_not_kernel_evidence(self):
        with tempfile.TemporaryDirectory() as tmp,patch.object(w,'proposal',
                return_value=({},[],[{}],'generated\n',2)):
            path=Path(tmp)/'Aliases.v'
            result=w.emit_library({},path)
            self.assertFalse(result['coq_checked'])
            self.assertFalse(result['current_isa_token_identity_proved'])
            self.assertTrue(w.emit_library({},path,True)['source_matches_generator'])
            with self.assertRaisesRegex(ValueError,'exists'):w.emit_library({},path)
            with patch.object(w,'proposal',return_value=({},[],[{}],'other',2)):
                with self.assertRaisesRegex(ValueError,'differs'):w.emit_library({},path,True)

    def test_direct_aliases_stop_at_real_sequential_carrier(self):
        model={'processes':[proc('process_0','Combinational','SAssign false (EVar 32 4) (LVar 32 2)'),
            proc('process_1','Sequential','SAssign true (EVar 32 7) (LVar 32 4)')]}
        chain=w.trace(model,2)
        self.assertEqual(chain['terminal'],4)
        self.assertEqual(chain['boundary'],'sequential_carrier')
        self.assertEqual(len(chain['edges']),1)

    def test_mux_not_guessed_to_be_an_alias(self):
        model={'processes':[proc('process_0','Combinational',
            'SAssign false (ECond 32 (EVar 1 1) (EVar 32 4) (EVar 32 7)) (LVar 32 2)')]}
        chain=w.trace(model,2)
        self.assertEqual(chain['terminal'],2);self.assertEqual(chain['edges'],[])
        self.assertEqual(chain['boundary'],'conditional_or_computed_source')

    def test_cycles_and_depth_exhaustion_not_silently_cut(self):
        model={'processes':[proc('process_0','Combinational','SAssign false (EVar 32 4) (LVar 32 2)'),
            proc('process_1','Combinational','SAssign false (EVar 32 2) (LVar 32 4)')]}
        with self.assertRaisesRegex(ValueError,'cycle'):w.trace(model,2)
        with self.assertRaisesRegex(ValueError,'budget'):w.trace(model,2,budget=1)

    def test_competing_writers_are_a_boundary(self):
        model={'processes':[proc('process_0','Combinational','SAssign false (EVar 32 4) (LVar 32 2)'),
            proc('process_1','Combinational','SAssign false (EVar 32 7) (LVar 32 2)')]}
        chain=w.trace(model,2)
        self.assertEqual(chain['edges'],[])
        self.assertEqual(chain['boundary'],'non_unique_or_external_source')

    def test_only_actual_field_sources_seed_discovery(self):
        model={'processes':[proc('process_0','Sequential',
            'SAssign true (ESel 5 (EVar 32 7) (EConst 5 7)) (LVar 5 9)')]}
        self.assertEqual(w.sources(model),[7])

    def test_generated_origin_uses_checked_combinational_coefficients(self):
        model={'module':'Unnamed','processes':[
            proc('process_0','Combinational','SAssign false (EVar 32 4) (LVar 32 2)'),
            proc('process_1','Sequential','SAssign true (EVar 32 7) (LVar 32 4)'),
            proc('process_2','Sequential','SAssign true (ESel 5 (EVar 32 2) (EConst 5 7)) (LVar 5 9)')]}
        profile={'ast':dict(file='unused',module='Unknown.AST',program='Unknown.program')}
        with patch.object(a,'load_ast',return_value=model):
            _,residuals,chains,source,count=w.proposal(profile)
        self.assertFalse(residuals);self.assertEqual(chains[0]['terminal'],4)
        self.assertEqual(count,3)
        self.assertIn('checked_scalar_block_binding Unknown.program',source)
        self.assertIn('source_2_word_origin',source)
        self.assertIn('field_reference (read_signal fixed 4%nat) field',source)
        self.assertNotIn('Admitted',source)


if __name__=='__main__':unittest.main()
