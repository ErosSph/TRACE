import unittest
from unittest.mock import patch
import cpu_direct_write_destination as d


class DirectWriteTests(unittest.TestCase):
    def fixture(self,plan=None,kind='Combinational',root=9):
        plan=plan or d.rtl.Term('BPWord',(
            d.rtl.Parser('(EBinary 12 BMul (EVar 5 9) (EConst 12 32))').complete(),
            d.rtl.Parser('(EVar 32 8)').complete()))
        bank=dict(root=100,total=1024,plans=[(dict(name='write'),None,plan)])
        fields=[dict(root=root,field='Rd',kind=kind,width=5)]
        return bank,fields

    def discover(self,bank,fields):
        with patch.object(d.ownership.bank,'analyze',return_value=dict(banks=[bank])):
            return d.discover({},fields)

    def test_same_sample_field_is_matched(self):
        rows,res=self.discover(*self.fixture())
        self.assertEqual(len(rows),1);self.assertEqual(res,[])

    def test_different_stage_field_is_not_same_sample(self):
        rows,res=self.discover(*self.fixture(kind='Sequential'))
        self.assertEqual(rows,[]);self.assertTrue(res)

    def test_different_index_root_is_not_guessed(self):
        rows,res=self.discover(*self.fixture(root=10))
        self.assertEqual(rows,[]);self.assertTrue(res)

    def test_guarded_write_requires_selection_rule(self):
        bank,_=self.fixture()
        plan=d.rtl.Term('BPIf',(d.rtl.Parser('(EVar 1 4)').complete(),
            bank['plans'][0][2],d.rtl.Term('BPEmpty')))
        rows,res=self.discover(*self.fixture(plan))
        self.assertEqual(rows,[]);self.assertTrue(res)

    def test_ambiguous_field_paths_are_not_silently_chosen(self):
        bank,fields=self.fixture();fields.append(dict(fields[0]))
        rows,res=self.discover(bank,fields)
        self.assertEqual(rows,[]);self.assertTrue(res)


if __name__=='__main__':unittest.main()
