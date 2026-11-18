import unittest
import re
from pathlib import Path
from unittest.mock import patch
import cpu_operand_tagged_origins as t


class TaggedAddressTests(unittest.TestCase):
    def test_raw_cv_generation_preserves_tag_and_unresolved_port(self):
        ast=t.origin.ROOT/'src/Ex/Generated/CV32E40PExtendedAST.v'
        original=Path.read_text
        def restricted(path,*args,**kwargs):
            if path.resolve()!=ast.resolve():
                raise AssertionError('unexpected old-proof lookup: '+str(path))
            return original(path,*args,**kwargs)
        with patch.object(Path,'read_text',restricted):
            report,source,_,count=t.render(ast,'Ex.Generated.CV32E40PExtendedAST')
        self.assertEqual([r['root']for r in report['origins']],[887,889])
        self.assertEqual(report['unresolved_roots'],[891])
        self.assertFalse(report['tag_truncated'])
        self.assertIn('root_937_tag_zero',source)
        self.assertIn('root_938_tag_zero',source)
        self.assertIn('Local Opaque CV32E40PExtendedAST.cv32e40p_program.',source)
        self.assertEqual(source.count('Local Opaque CV32E40PExtendedAST.cv32e40p_program.'),
                         source.count('Local Transparent CV32E40PExtendedAST.cv32e40p_program.'))
        self.assertEqual(source.count('Print Assumptions '),count)
        self.assertNotIn('Admitted',source)

    def test_connection_optimization_preserves_entire_proof_source(self):
        ast=t.origin.ROOT/'src/Ex/Generated/CV32E40PExtendedAST.v'
        before=t.tagged.proposal
        def original(profile, **_):
            return before(profile, opaque_program_connection=False)
        with patch.object(t.tagged, 'proposal', original):
            old_report,old_source,old_paths,old_count=t.render(ast,'Ex.Generated.CV32E40PExtendedAST')
        report,source,paths,count=t.render(ast,'Ex.Generated.CV32E40PExtendedAST')
        restored=re.sub(r'^Local (?:Opaque|Transparent) CV32E40PExtendedAST\.cv32e40p_program\.\n',
                        '',source,flags=re.M)
        self.assertEqual(restored,old_source)
        self.assertEqual((report,paths,count),(old_report,old_paths,old_count))


if __name__=='__main__':unittest.main()
