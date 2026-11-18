import unittest
from unittest.mock import patch
import cpu_write_address_history as h
T=h.rf.rtl.Term

class WriteAddressHistoryTests(unittest.TestCase):
    def run_discovery(self,body,rows=None):
        proc=dict(name='wire',kind='Combinational',writers=[2],body=h.rf.rtl.Parser(body).complete())
        bank=dict(root=99,plans=[({},None,T('BPWord',(h.rf.rtl.Parser('EVar 5 2').complete(),T('EConst',(T('32'),T('0'))))))])
        with patch.object(h.projections,'discover_narrow_fields',return_value=dict(projections=rows if rows is not None else [dict(root=3)])),patch.object(h.rf.banks,'analyze',return_value=dict(banks=[bank])):
            return h.discover(dict(processes=[proc]))
    def test_alias_reaches_actual_history_leaf(self):
        matches,residuals=self.run_discovery('SAssign false (EVar 5 3) (LVar 5 2)')
        self.assertEqual(matches,[dict(bank=99,address=2,leaf=3,path=[2])]);self.assertFalse(residuals)
    def test_non_alias_is_not_invented(self):
        matches,residuals=self.run_discovery('SAssign false (EConst 5 3) (LVar 5 2)')
        self.assertFalse(matches);self.assertTrue(residuals)
    def test_cycle_terminates_unproved(self):
        matches,residuals=self.run_discovery('SAssign false (EVar 5 2) (LVar 5 2)')
        self.assertFalse(matches);self.assertTrue(residuals)
    def test_ambiguous_history_is_not_arbitrarily_selected(self):
        matches,_=self.run_discovery('SAssign false (EVar 5 3) (LVar 5 2)',[dict(root=3,source=7),dict(root=3,source=8)])
        self.assertFalse(matches)

if __name__=='__main__':unittest.main()
