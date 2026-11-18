import unittest
from unittest.mock import patch
import cpu_operand_routes as r


class OperandRouteTests(unittest.TestCase):
    def ast(self, bodies):
        return dict(source_sha256='fixture',processes=[dict(name='p'+str(i),kind=kind,
            events=['posedge'],line=i,body=r.rtl.Parser(body).complete())
            for i,(kind,body) in enumerate(bodies)])

    def discover(self, bodies):
        with patch.object(r.ports,'analyze',return_value=dict(ports=[dict(output_root=1,width=32)],residuals=[])):
            return r.discover(self.ast(bodies))

    def test_control_read_is_not_payload(self):
        p=self.discover([('Combinational','SAssign false (ECond 32 (EVar 32 1) (EConst 32 0) (EConst 32 1)) (LVar 32 2)')])
        self.assertEqual(p['reached_roots'],[1]);self.assertFalse(p['routes'])
        self.assertEqual(len(p['terminal_consumers']),1)

    def test_sequential_route_keeps_other_mux_choices(self):
        p=self.discover([('Sequential','SAssign true (ECond 32 (EVar 1 4) (EVar 32 1) (EVar 32 3)) (LVar 32 2)')])
        self.assertEqual(p['reached_roots'],[1,2])
        row=p['routes'][0]
        self.assertTrue(row['crossed_sampling_boundary'])
        self.assertEqual([x['source'] for x in row['alternatives']],[1,3])
        self.assertEqual(row['incoming'][0]['conditions'],[('(EVar 1 4)',True)])

    def test_arithmetic_stops_identity_transport(self):
        p=self.discover([('Combinational','SAssign false (EBinary 32 BAdd (EVar 32 1) (EConst 32 4)) (LVar 32 2)')])
        self.assertEqual(p['reached_roots'],[1]);self.assertFalse(p['routes'])

    def test_copy_cycles_terminate_and_do_not_invent_origins(self):
        p=self.discover([('Combinational','SAssign false (EVar 32 1) (LVar 32 2)'),
                         ('Combinational','SAssign false (EVar 32 2) (LVar 32 1)'),
                         ('Combinational','SAssign false (EVar 32 7) (LVar 32 8)')])
        self.assertEqual(p['reached_roots'],[1,2]);self.assertEqual(len(p['routes']),2)

    def test_ports_remain_distinct_until_an_actual_join(self):
        bodies=[('Combinational','SAssign false (EVar 32 1) (LVar 32 10)'),
                ('Combinational','SAssign false (EVar 32 2) (LVar 32 20)'),
                ('Sequential','SAssign true (ECond 32 (EVar 1 4) (EVar 32 10) (EVar 32 20)) (LVar 32 30)')]
        with patch.object(r.ports,'analyze',return_value=dict(
                ports=[dict(output_root=x,width=32)for x in [1,2]],residuals=[])):
            p=r.discover(self.ast(bodies))
        self.assertEqual(p['port_provenance']['10'],[1])
        self.assertEqual(p['port_provenance']['20'],[2])
        self.assertEqual(p['port_provenance']['30'],[1,2])
        join=next(x for x in p['routes']if x['root']==30)
        self.assertEqual([x['origin_ports']for x in join['alternatives']],[[1],[2]])
        self.assertTrue(join['crossed_sampling_boundary'])

    def test_transformed_value_retains_source_obligation_not_identity(self):
        p=self.discover([('Combinational','SAssign false (EBinary 32 BAdd (EVar 32 1) (EConst 32 4)) (LVar 32 2)')])
        self.assertNotIn('2',p['port_provenance'])
        self.assertEqual(p['terminal_consumers'][0]['origin_ports'],[1])


if __name__=='__main__':unittest.main()
