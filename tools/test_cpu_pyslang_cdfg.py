import copy
import unittest
from cpu_cdfg_result_consumer import validate_replay
from cpu_pyslang_cdfg import dependencies


class GraphChecks(unittest.TestCase):
    def setUp(self):
        self.graph=dict(symbols=[dict(path='top.q',width=32)],processes=[dict(
            timing=dict(edge='Posedge'))],edges=[dict(target='top.q',data=['top.d'],
            address=['top.idx'],guards=[dict(condition=dict(reads=['top.en']),taken=True)])])

    def reject(self, change):
        modified=copy.deepcopy(self.graph);change(modified)
        with self.assertRaises(ValueError):validate_replay(modified,self.graph)

    def test_exact(self):validate_replay(self.graph,copy.deepcopy(self.graph))
    def test_missing_data(self):self.reject(lambda g:g['edges'][0]['data'].clear())
    def test_wrong_guard(self):self.reject(lambda g:g['edges'][0]['guards'][0].update(taken=False))
    def test_width(self):self.reject(lambda g:g['symbols'][0].update(width=31))
    def test_phase(self):self.reject(lambda g:g['processes'][0]['timing'].update(edge='Negedge'))
    def test_identity(self):self.reject(lambda g:g['edges'][0].update(target='top.other.q'))
    def test_control_and_address_dependencies(self):
        self.assertEqual(dependencies(self.graph['edges'][0]),{'top.d','top.en','top.idx'})


if __name__=='__main__':unittest.main()
