import copy
import unittest
from unittest.mock import patch
import cpu_add_ready_controls as controls


class Tests(unittest.TestCase):
    def setUp(self):
        recipe='(Select (EVar 1 99) Capture Unknown)'
        self.writes=dict(rows=[dict(root=100,process='p0',recipe=recipe,valid=10),
                               dict(root=200,process='p1',recipe=recipe,valid=20)])
        self.selection=dict(rows=[dict(root=101,process='p0',recipe=recipe),
                                  dict(root=201,process='p1',recipe=recipe)])
        first=dict(write=1,load=2,rd=3);second=dict(write=11,load=12,rd=13)
        self.physical=dict(rows=[dict(row=dict(binding=dict(first=first,second=second)))])
        self.routes={root:dict(kind='sequential',input=root,terminal=100+offset+(100 if root>10 else 0),
                              process='p1'if root>10 else'p0',edges=[])
                     for root,offset in [(1,0),(2,1),(3,2),(11,0),(12,1),(13,2)]}

    def discover(self):
        with patch.object(controls.history.admission.ready,'discover',return_value=(self.physical,None)), \
             patch.object(controls.history.admission.wires,'trace',side_effect=lambda raw,width,root:self.routes[root]):
            return controls.discover(dict(source_sha256='same'),self.writes,self.selection)

    def test_actual_mem2reg_not_different_alu_selector(self):
        self.assertEqual([r['routes']['load']['terminal']for r in self.discover()['rows']],[101,201])

    def test_wrong_control_role_rejected(self):
        self.selection['rows'][0]['root']=109
        with self.assertRaisesRegex(ValueError,'memory-selection'):
            self.discover()

    def test_wrong_write_predecessor_rejected(self):
        self.writes['rows'][1]['root']=100
        with self.assertRaisesRegex(ValueError,'write/memory'):
            self.discover()

    def test_wrong_destination_phase_rejected(self):
        self.routes[3]['process']='p1'
        with self.assertRaisesRegex(ValueError,'capture identity'):
            self.discover()

    def test_computed_boundary_is_not_claimed_sequential(self):
        self.routes[2]['kind']='computed'
        with self.assertRaisesRegex(ValueError,'not sequential'):
            self.discover()

    def test_ambiguous_ports_rejected(self):
        row=copy.deepcopy(self.physical['rows'][0]);row['row']['binding']['first']['load']=77
        self.physical['rows'].append(row)
        with self.assertRaisesRegex(ValueError,'ambiguous'):
            self.discover()

    def test_wrong_recipe_guard_rejected(self):
        self.selection['rows'][0]['recipe']='other'
        with self.assertRaisesRegex(ValueError,'capture identity'):
            self.discover()


if __name__=='__main__':unittest.main()
