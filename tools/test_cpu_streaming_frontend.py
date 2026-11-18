"""Real-elaboration regression for exact one-bit streaming reversal."""
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import SignalInfo

V = Path('/opt/miniforge3/envs/verilator4/opt/verilator-4.028')

def evaluate(term, value):
    tokens = iter(re.findall(r'[A-Za-z]+|\d+', term))
    def expr():
        tag, width = next(tokens), int(next(tokens))
        if tag == 'EVar':
            next(tokens)
            result = value
        elif tag == 'EConst':
            result = int(next(tokens))
        elif tag == 'ESel':
            base, _ = expr()
            offset, _ = expr()
            result = base >> offset
        elif tag == 'EConcat':
            left, _ = expr()
            right, rw = expr()
            result = (left << rw) | right
        else:
            raise AssertionError(tag)
        return result & ((1 << width) - 1), width
    answer = expr()[0]
    assert next(tokens, None) is None
    return answer

class StreamingTests(unittest.TestCase):
    @unittest.skipUnless((V/'bin/verilator').exists(), 'requires pinned Verilator 4')
    def test_real_elaboration_bit_order(self):
        for width in (1, 8, 32):
            with tempfile.TemporaryDirectory(prefix='streaming-regression-') as tmp:
                d=Path(tmp); source=d/'test.sv'; xml=d/'test.xml'
                source.write_text(f'module top(input [{width-1}:0] a, output [{width-1}:0] y); assign y = {{<<{{a}}}}; endmodule\n')
                subprocess.run([str(V/'bin/verilator'),'--xml-only','--xml-output',str(xml),'--top-module','top','-Wno-fatal',str(source)],cwd=d,env=dict(os.environ,VERILATOR_ROOT=str(V)),capture_output=True,check=True)
                root=ET.parse(xml).getroot();tr=ArrayTranslator(root,'top')
                node=root.find('.//streaml')
                self.assertIsNotNone(node)
                term=tr.expr(node,{'a':SignalInfo(0,width,'top.a',0,'')})
                values=range(1<<width) if width<=8 else [0,0xffffffff,0x12345678]+[1<<i for i in range(width)]
                for value in values:
                    expected=int(f'{value:0{width}b}'[::-1],2)
                    self.assertEqual(evaluate(term,value),expected,(width,value))
                node[1].set('name',"32'h2")
                with self.assertRaisesRegex(ValueError,'one-bit'):
                    tr.expr(node,{'a':SignalInfo(0,width,'top.a',0,'')})

if __name__=='__main__':unittest.main()
