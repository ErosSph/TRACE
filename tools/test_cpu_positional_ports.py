"""Real Verilator elaboration regression for named/positional port equivalence."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import source_port_order

V = Path('/opt/miniforge3/envs/verilator4/opt/verilator-4.028')

class PositionalPorts(unittest.TestCase):
    @unittest.skipUnless((V/'bin/verilator').exists(), 'requires pinned Verilator 4')
    def test_named_and_positional_match_for_ansi_and_reordered_nonansi(self):
        for child in [
            'module child #(parameter W=8)(input [W-1:0] b,a, output [W-1:0] y); assign y=a-b; endmodule',
            'module child(b,a,y); input [7:0] a; output [7:0] y; input [7:0] b; assign y=a-b; endmodule',
        ]:
            variants = []
            with tempfile.TemporaryDirectory(prefix='port-binding-regression-') as tmp:
                d=Path(tmp)
                for binding in ['b,a,y', '.b(b),.a(a),.y(y)']:
                    source=d/'test.v';xml=d/'test.xml'
                    source.write_text(child+'\nmodule top(input [7:0] a,b, output [7:0] y); child u('+binding+'); endmodule\n')
                    subprocess.run([str(V/'bin/verilator'),'--xml-only','--xml-output',str(xml),'--top-module','top','-Wno-fatal',str(source)],cwd=d,env=dict(os.environ,VERILATOR_ROOT=str(V)),capture_output=True,check=True)
                    tr=ArrayTranslator(ET.parse(xml).getroot(),'top');tr.translate()
                    variants.append([re.sub(r'process_source_line := \d+', 'process_source_line := 0', p) for p in tr.processes])
                self.assertEqual(variants[0],variants[1])

    def test_ambiguous_headers_are_rejected(self):
        for source in ['module m(a); input a; endmodule module m(b); input b; endmodule',
                       'module m(input a, `ifdef EXTRA input b, `endif output y); endmodule']:
            with self.assertRaises(ValueError):source_port_order(source,'m')

if __name__=='__main__':unittest.main()
