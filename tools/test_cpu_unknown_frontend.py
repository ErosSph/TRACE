#!/usr/bin/env python3
import unittest
import xml.etree.ElementTree as ET
from cpu_unknown_frontend import unknown_literal,UnknownInputTranslator

class UnknownFrontendTests(unittest.TestCase):
    def test_full_x_never_chooses_zero(self):
        parsed=unknown_literal("32'bx")
        self.assertEqual(parsed['known_mask'],0)
        self.assertEqual(parsed['unknown_mask'],2**32-1)

    def test_mixed_binary_keeps_known_bits(self):
        p=unknown_literal("4'b1x01")
        outputs={p['known_value']|(choice&p['unknown_mask']) for choice in range(16)}
        self.assertEqual(outputs,{9,13})
        self.assertTrue(all(value&p['known_mask']==p['known_value'] for value in outputs))

    def test_mixed_hex_keeps_known_high_nibble(self):
        p=unknown_literal("8'hax")
        outputs={p['known_value']|(choice&p['unknown_mask']) for choice in range(256)}
        self.assertEqual(outputs,set(range(160,176)))

    def test_leading_z_is_extended(self):
        self.assertEqual(unknown_literal("8'hz")['unknown_mask'],255)

    def test_signed_marker_recorded(self):
        self.assertTrue(unknown_literal("8'shx")['signed'])

    def test_known_literals_not_touched(self):
        self.assertIsNone(unknown_literal("32'h12345678"))

    def test_nonpositive_width_rejected(self):
        with self.assertRaises(ValueError):unknown_literal("0'bx")

    def translator(self):
        root=ET.fromstring('''<verilator_xml><netlist><module name="top">
          <var name="out" dtype_id="1" loc="f,1,1,1,2"/>
          <always loc="f,2,1,2,2"><assign>
          <const name="4'b1x01" dtype_id="1" loc="f,2,1,2,2"/>
          <varref name="out" dtype_id="1"/></assign></always></module>
          <typetable><basicdtype id="1" name="logic" left="3" right="0"/>
          <basicdtype id="2" name="logic" left="7" right="0"/></typetable>
          </netlist></verilator_xml>''')
        return UnknownInputTranslator(root,'top')

    def test_actual_unknown_emits_readonly_input(self):
        tr=self.translator();tr.translate()
        self.assertEqual(len(tr.unknown_sites),1)
        self.assertEqual(tr.signals[1].direction,'arbitrary_input')
        self.assertIn('EVar 4 1',tr.processes[0])
        self.assertIn('EConst 4 9',tr.processes[0])
        self.assertIn('EConst 4 4',tr.processes[0])
        self.assertNotIn(1,tr.process_meta[0]['writers'])

    def test_source_site_is_cached_not_reallocated(self):
        tr=self.translator();node=tr.modules['top'].find('.//const')
        a=tr.expr(node,{});b=tr.expr(node,{})
        self.assertEqual(a,b);self.assertEqual(len(tr.unknown_sites),1)

    def test_extension_mismatch_refused(self):
        tr=self.translator();node=tr.modules['top'].find('.//const');node.set('dtype_id','2')
        with self.assertRaisesRegex(ValueError,'width mismatch'):tr.expr(node,{})

    def test_nonempty_task_not_silently_skipped(self):
        tr=self.translator()
        with self.assertRaisesRegex(ValueError,'task needs'):
            tr.stmt(ET.fromstring('<taskref name="not_empty"/>'),{})

if __name__=='__main__':unittest.main()
