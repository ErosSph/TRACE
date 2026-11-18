import unittest
import xml.etree.ElementTree as ET
from cpu_array_frontend import ArrayTranslator
from cv32e40p_extended_frontend import SignalInfo

class ArrayTests(unittest.TestCase):
    def tr(self,cells=32,iw=5,signed="false"):
        root=ET.fromstring(f'''<verilator_xml><netlist><module name="test"/>
          <typetable><basicdtype id="word" left="31" right="0"/>
          <basicdtype id="idx" left="{iw-1}" right="0" signed="{signed}"/>
          <unpackarraydtype id="bank" sub_dtype_id="word"><range>
          <const name="32'h0"/><const name="32'h{cells-1:x}"/>
          </range></unpackarraydtype></typetable></netlist></verilator_xml>''')
        return ArrayTranslator(root,"test")
    def select(self):
        return ET.fromstring('<arraysel dtype_id="word"><varref name="storage" dtype_id="bank"/><varref name="address" dtype_id="idx"/></arraysel>')
    def env(self):
        # Match the existing frontend dataclass, without CPU-specific names.
        return {"storage":SignalInfo(0,1024,"test.storage",0,""),
                "address":SignalInfo(1,5,"test.address",0,"")}
    def test_zero_based_bank_width(self):
        self.assertEqual(self.tr().dtype_width("bank"),1024)
    def test_index_arithmetic_cannot_overflow_5bits(self):
        s=self.tr().expr(self.select(),self.env())
        self.assertIn("EBinary 12 BMul",s)
        self.assertIn("EConst 12 32",s)
    def test_array_lvalue_is_slice_not_whole_bank(self):
        self.assertTrue(self.tr().lvalue(self.select(),self.env()).startswith("LSel 32"))
    def test_possible_oob_is_rejected(self):
        with self.assertRaisesRegex(ValueError,"exceeds"):
            self.tr(cells=16).expr(self.select(),self.env())
    def test_signed_index_is_rejected(self):
        with self.assertRaisesRegex(ValueError,"signed"):
            self.tr(signed="true").expr(self.select(),self.env())
    def test_x_is_not_changed_to_zero(self):
        with self.assertRaisesRegex(ValueError,"unsupported Verilator constant"):
            self.tr().expr(ET.fromstring('<const dtype_id="word" name="32\'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"/>'),{})
if __name__ == "__main__":
    unittest.main()
