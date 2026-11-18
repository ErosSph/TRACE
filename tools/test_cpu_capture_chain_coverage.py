import unittest
import cpu_capture_chain_coverage as c

class ChainCoverageTests(unittest.TestCase):
    def test_no_connection_does_not_create_coverage(self):
        self.assertIsNone(c.relations({'connection':None}))

    def test_sources_are_actual_predecessors_not_alias_inputs(self):
        data={'connection':{'capture':{'carrier':140}},'chain':{
            'rows':[{'root':244,'source':225},{'root':283,'source':272},{'root':305,'source':298}],
            'edges':[{'target':1,'source':0},{'target':2,'source':1}]}}
        rows=c.relations(data)['direct_origins']
        self.assertEqual([r['source']for r in rows],[140,244,283])
        self.assertEqual(data['chain']['rows'][0]['source'],225)

if __name__=='__main__':unittest.main()
