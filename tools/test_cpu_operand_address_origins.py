import unittest
import tempfile
from pathlib import Path
from contextlib import ExitStack
from unittest.mock import patch
import cpu_operand_address_origins as a


class AddressOriginTests(unittest.TestCase):
    def discover(self, kind, rhs):
        ast = dict(processes=[dict(name='p', kind=kind, writers=[3],
            body=a.rtl.Parser('SAssign false '+rhs+' (LVar 5 3)').complete())])
        with patch.object(a.readers, 'analyze', return_value=dict(ports=[
                dict(rhs=a.rtl.Parser('EVar 5 3').complete())])):
            return a.discover(ast)

    def test_direct_word_field(self):
        rows, residuals, _, _ = self.discover('Combinational',
            '(ESel 5 (EVar 32 9) (EConst 5 15))')
        self.assertEqual(rows[0]['source'], 9)
        self.assertFalse(residuals)

    def test_registered_address_is_not_current_word(self):
        rows, residuals, _, _ = self.discover('Sequential',
            '(ESel 5 (EVar 32 9) (EConst 5 15))')
        self.assertFalse(rows)
        self.assertTrue(residuals)

    def test_multiple_words_not_silently_identified(self):
        rows, residuals, _, _ = self.discover('Combinational',
            '(ESel 5 (EBinary 32 BOr (EVar 32 9) (EVar 32 10)) (EConst 5 15))')
        self.assertFalse(rows)
        self.assertTrue(residuals)

    def test_case_support_is_selected_by_dependency_not_process_name(self):
        body=a.rtl.Parser('SCase (EVar 2 8) [((Some (EConst 2 0)),(SAssign false (ESel 5 (EVar 32 9) (EConst 5 15)) (LVar 5 3)))]').complete()
        ast=dict(processes=[dict(name='unrelated_name',kind='Combinational',writers=[3],line=7,body=body)])
        with patch.object(a.readers,'analyze',return_value=dict(ports=[dict(rhs=a.rtl.Parser('EVar 5 3').complete())])):
            result=a.support_frontier(ast)
        self.assertEqual([r['process'] for r in result['cases']],['unrelated_name'])
        self.assertEqual(result['cases'][0]['root'],3)
        self.assertFalse(result['semantic_roles_proved'])

    def test_conflicting_writer_cannot_be_selected(self):
        body=a.rtl.Parser('SAssign false (EVar 5 7) (LVar 5 3)').complete()
        ast=dict(processes=[dict(name=name,kind='Combinational',writers=[3],line=7,body=body) for name in ['a','b']])
        with patch.object(a.readers,'analyze',return_value=dict(ports=[dict(rhs=a.rtl.Parser('EVar 5 3').complete())])):
            result=a.support_frontier(ast)
        self.assertFalse(result['cases'])
        self.assertEqual(result['residuals'][0]['reason'],'non-unique writer')

    def test_only_checked_tagged_addresses_count_as_covered(self):
        for accepted in [False, True]:
            with self.subTest(accepted=accepted), tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
                report=dict(origins=[],residuals=[dict(root=r,reason='branch') for r in [1,2,3]])
                stack.enter_context(patch.object(a,'render',return_value=(report,None,[],0)))
                stack.enter_context(patch.object(a.origin,'raw_binding',return_value=({}, {}, [])))
                stack.enter_context(patch.object(a,'support_frontier',return_value=dict(cases=[])))
                stack.enter_context(patch.object(a.readers,'analyze',return_value=dict(ports=[
                    dict(rhs=a.rtl.Parser('EVar 6 '+str(r)).complete()) for r in [1,2,3]])))
                origins=[dict(root=1),dict(root=2)]
                stack.enter_context(patch.object(a.tagged_origins,'render',
                    return_value=(dict(origins=origins),'source',[],2)))
                check=stack.enter_context(patch.object(a.tagged_origins,'check',
                    return_value=dict(accepted=accepted,origins=origins)))
                result=a.check('raw.v','Raw.AST',Path(directory)/'check')
                check.assert_called_once()
                self.assertEqual(result['unresolved_roots'],[3] if accepted else [1,2,3])
                self.assertFalse(result['all_discovered_addresses_covered'])


if __name__ == '__main__':
    unittest.main()
