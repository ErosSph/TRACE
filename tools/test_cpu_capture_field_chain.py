import unittest
from unittest.mock import patch
import cpu_capture_field_chain as c

class CaptureChainTests(unittest.TestCase):
    def test_selected_component_does_not_merge_unrelated_field_chains(self):
        ast={'processes':[]}
        with patch.object(c.chain,'discover',return_value={'head':None})as discover,patch.object(c.birth,'discover',return_value={'captures':[]}):
            self.assertIsNone(c.discover(ast,{10,20})['connection'])
            discover.assert_called_once_with(ast,{10,20})
    def test_missing_capture_is_not_guessed(self):
        with patch.object(c.chain,'discover',return_value={'head':{'source':28}}),patch.object(c.birth,'discover',return_value={'captures':[]}):
            self.assertIsNone(c.discover({'processes':[]})['connection'])

    def test_ambiguous_capture_rejected(self):
        rows=[{'carrier':28,'valid_root':i}for i in [1,2]]
        with patch.object(c.chain,'discover',return_value={'head':{'source':28}}),patch.object(c.birth,'discover',return_value={'captures':rows}):
            self.assertIsNone(c.discover({'processes':[]})['connection'])

    def test_actual_alias_connects_capture(self):
        parse=c.birth.rtl.Parser
        ast={'processes':[dict(name='wire',kind='Combinational',writers=[28],body=parse('SAssign false (EVar 32 140) (LVar 32 28)').complete())]}
        capture=dict(carrier=140,valid_root=141)
        with patch.object(c.chain,'discover',return_value={'head':{'source':28}}),patch.object(c.birth,'discover',return_value={'captures':[capture]}):
            result=c.discover(ast)['connection']
        self.assertEqual(result['route']['terminal'],140)
        self.assertEqual(result['route']['edges'][0]['root'],28)
        self.assertEqual(result['capture'],capture)

    def test_noncopy_does_not_get_capture_identity(self):
        parse=c.birth.rtl.Parser
        ast={'processes':[dict(name='compute',kind='Combinational',writers=[28],body=parse('SAssign false (EConst 32 140) (LVar 32 28)').complete())]}
        with patch.object(c.chain,'discover',return_value={'head':{'source':28}}),patch.object(c.birth,'discover',return_value={'captures':[dict(carrier=140)]}):
            self.assertIsNone(c.discover(ast)['connection'])

if __name__=='__main__':unittest.main()
