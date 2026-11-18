import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch
import cpu_tagged_capture_addresses as t


class TaggedCapture(unittest.TestCase):
    def test_match_requires_unique_real_carrier(self):
        row=dict(root=10,word_root=30,field='Rs1')
        self.assertEqual(len(t.select([row],[dict(carrier=30,valid_root=31)])[0]),1)
        for captures in [[],[dict(carrier=29)],[dict(carrier=30),dict(carrier=30)]]:
            self.assertEqual(t.select([row],captures)[0],[])

    def test_destination_field_not_promoted_to_source(self):
        self.assertEqual(t.select([dict(root=10,word_root=30,field='Rd')],[dict(carrier=30)])[0],[])

    def test_actual_cv_read_ports_retain_unresolved_third_port(self):
        ar,_,_,_=t.tagged.render('src/Ex/Generated/CV32E40PExtendedAST.v','Ex.Generated.CV32E40PExtendedAST')
        ast,_,_=t.o.raw_binding('src/Ex/Generated/CV32E40PExtendedAST.v','Ex.Generated.CV32E40PExtendedAST')
        joins,missing=t.select(ar['origins'],t.c.births.discover(ast)['captures'])
        self.assertEqual({r['root']for r,_,_ in joins},{887,889})
        self.assertEqual(ar['unresolved_roots'],[891]);self.assertEqual(missing,[])
        self.assertFalse(ar['tag_truncated'])

    def test_failed_fresh_provider_stops_before_connection(self):
        address=dict(origins=[dict(root=10,word_root=30,field='Rs1')],unresolved_roots=[])
        births=dict(captures=[dict(carrier=30,valid_root=31)])
        with tempfile.TemporaryDirectory()as tmp,\
             patch.object(t.o,'raw_binding',return_value=({}, {}, [])),\
             patch.object(t.tagged,'render',return_value=(address,'source',[],0)),\
             patch.object(t.c.births,'discover',return_value=births),\
             patch.object(t.c.births,'render',return_value=(births,'birth')),\
             patch.object(t.tagged,'check',return_value={'accepted':False}),\
             patch.object(t.c,'verify')as verify,patch.object(t.c.births,'check')as build_birth:
            r=t.check('raw','Raw',Path(tmp)/'out')
            self.assertFalse(r['accepted']);verify.assert_not_called();build_birth.assert_not_called()


if __name__=='__main__':unittest.main()
