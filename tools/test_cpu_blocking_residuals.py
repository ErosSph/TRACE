import unittest
from unittest.mock import patch
import cpu_blocking_residuals as c

class ResidualTests(unittest.TestCase):
    def discover(self,body):
        ast={'processes':[{'name':'renamed','kind':'Combinational',
          'body':c.observation.rtl.Parser(body).complete()}]}
        with patch.object(c.fields,'discover',return_value={'residuals':[{'process':'renamed','root':9,'reason':'raw dependency'}]}):
            return c.discover(ast)
    def test_no_manual_process_or_root_table(self):
        p=self.discover('(SSeq [(SAssign false (EVar 5 3) (LVar 5 7)); (SAssign false (EVar 5 7) (LVar 5 9))])')
        self.assertEqual(p['candidates'][0]['dependencies'],[(5,3)])
        self.assertFalse(p['candidates'][0]['proof_checked'])
        self.assertFalse(p['complete_R_generated'])
    def test_unsupported_not_dropped(self):
        p=self.discover('(SAssign true (EVar 5 3) (LVar 5 9))')
        self.assertEqual(p['candidates'],[]);self.assertEqual(len(p['unsupported']),1)
    def test_empty_is_not_proof(self):
        with patch.object(c.fields,'discover',return_value={'residuals':[]}):p=c.discover({'processes':[]})
        self.assertEqual(p['candidates'],[]);self.assertFalse(p['complete_R_generated'])

if __name__=='__main__':unittest.main()
