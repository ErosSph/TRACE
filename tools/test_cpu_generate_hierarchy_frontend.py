"""Real elaboration regressions for generate-scope child instantiation."""
import os,re,tempfile,subprocess,unittest
from pathlib import Path
import xml.etree.ElementTree as ET
from cpu_array_frontend import ArrayTranslator
V=Path('/opt/miniforge3/envs/verilator4/opt/verilator-4.028')
class GenerateHierarchyTests(unittest.TestCase):
    def translate(self,body):
        with tempfile.TemporaryDirectory(prefix='generate-hierarchy-') as tmp:
            d=Path(tmp);p=d/'test.sv';x=d/'test.xml'
            p.write_text('module child(input [7:0] a, output [7:0] y); assign y=~a; endmodule\nmodule top(input [7:0] a, output [7:0] y); wire [7:0] x; '+body+' endmodule\n')
            subprocess.run([str(V/'bin/verilator'),'--xml-only','--xml-output',str(x),'--top-module','top','-Wno-fatal',str(p)],cwd=d,env=dict(os.environ,VERILATOR_ROOT=str(V)),capture_output=True,check=True)
            tr=ArrayTranslator(ET.parse(x).getroot(),'top');tr.translate();return tr
    @unittest.skipUnless((V/'bin/verilator').exists(),'requires pinned Verilator 4')
    def test_nested_generate_matches_flat_complete_ast(self):
        flat=self.translate('child u0(a,x); child u1(x,y);')
        nested=self.translate('if(1) begin:g if(1) begin:h child u(a,x); end end if(1) begin:j child u(x,y); end')
        normalize=lambda tr:[re.sub(r'process_source_line := \d+','process_source_line := 0',p) for p in tr.processes]
        self.assertEqual(len(nested.instances),2)
        self.assertEqual({i['path'] for i in nested.instances},{'top.g.h.u','top.j.u'})
        self.assertEqual(len(nested.processes),6)
        self.assertEqual(normalize(flat),normalize(nested))
    @unittest.skipUnless((V/'bin/verilator').exists(),'requires pinned Verilator 4')
    def test_ambiguous_scoped_variables_fail_closed(self):
        with self.assertRaisesRegex(ValueError,'ambiguous scoped variable'):
            self.translate('if(1) begin:g wire [7:0] tmp; child u(a,tmp); assign x=tmp; end if(1) begin:h wire [7:0] tmp; child u(x,tmp); assign y=tmp; end')
    def test_unknown_instance_container_is_rejected(self):
        r=ET.fromstring('<verilator_xml><netlist><module name="top"><unsupported><instance name="u" defName="child"/></unsupported></module><module name="child"/><typetable/></netlist></verilator_xml>')
        with self.assertRaisesRegex(ValueError,'unsupported scope'):
            ArrayTranslator(r,'top').translate()
    def test_function_locals_are_not_hardware_registers(self):
        r=ET.fromstring('<verilator_xml><netlist><module name="top"><func name="f"><var name="x" dtype_id="1"/></func><func name="g"><var name="x" dtype_id="1"/></func></module><typetable><basicdtype id="1" name="logic"/></typetable></netlist></verilator_xml>')
        tr=ArrayTranslator(r,'top');tr.instantiate('top','top')
        self.assertEqual(tr.signals,[])
        self.assertTrue(tr.unsupported) # Plain frontend still rejects unlowered functions.
if __name__=='__main__':unittest.main()
