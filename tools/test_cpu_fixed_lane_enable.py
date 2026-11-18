import unittest
from unittest.mock import patch
import cpu_fixed_lane_enable as f

class FixedLaneTests(unittest.TestCase):
    def fixture(self,taken=True,lane=1):
        st=f.rtl.Parser('SAssign false (EBinary 1 BAnd (EBinary 1 BEq (EConst 6 1) (EVar 6 4)) (EVar 1 5)) (LSel 1 (LVar 32 7) (EConst 5 1))').complete()
        ast=dict(processes=[dict(name='decode',kind='Combinational',body=st)])
        site=dict(destination=dict(kind='fixed_lane',lane=lane),process='rf',path=[0],
                  guards=[dict(expression='ESel 1 (EVar 32 7) (EConst 5 1)',taken=taken)])
        return ast,site

    def discover(self,ast,site):
        with patch.object(f.ownership,'analyze',return_value=dict(writes=[site])):
            return f.discover(ast)

    def test_full_six_bit_address_is_preserved(self):
        ast,site=self.fixture();r=self.discover(ast,site)
        self.assertEqual(len(r['rows']),1)
        self.assertEqual(r['rows'][0]['address'],'(EVar 6 4)')
        self.assertFalse(r['isa_destination_proved'])
        self.assertFalse(r['full_lfp_bit_connection_proved'])

    def test_negative_guard_does_not_imply_address(self):
        ast,site=self.fixture(taken=False);self.assertEqual(self.discover(ast,site)['rows'],[])

    def test_wrong_lane_does_not_match(self):
        ast,site=self.fixture(lane=2);self.assertEqual(self.discover(ast,site)['rows'],[])

    def test_duplicate_bit_producers_rejected(self):
        ast,site=self.fixture();ast['processes'].append(dict(ast['processes'][0],name='other'))
        self.assertEqual(self.discover(ast,site)['rows'],[])

if __name__=='__main__':unittest.main()
