import unittest
import tempfile
from pathlib import Path
import cpu_isa_destination_certificate as d


class DestinationTests(unittest.TestCase):
    def setUp(self):
        self.original=(d.synthesis.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text()

    def test_register_destination_is_actual_primitive_argument(self):
        text=d.render(self.original)
        self.assertIn('| Decode.Add rd rs1 rs2 => [rd]',text)
        self.assertIn('| Decode.Sw rs1 rs2 simm12 => []',text)
        self.assertIn('token_execute',text)
        self.assertIn('original_decode_destination_fields',text)
        self.assertIn('original_destination_address',text)
        self.assertIn('Utility.bitSlice code 7 12',text)
        self.assertNotIn('Admitted',text)

    def test_unknown_register_argument_is_rejected(self):
        with self.assertRaises(ValueError):
            d.render(self.original.replace('Spec.Machine.setRegister rd',
                                            'Spec.Machine.setRegister (rd + 1)',1))

    def test_coq_rejects_wrong_add_destination(self):
        source=d.render(self.original)
        old='| Decode.Add rd rs1 rs2 => [rd]'
        self.assertEqual(source.count(old),1)
        with tempfile.TemporaryDirectory()as directory:
            path=Path(directory)/'Destination.v'
            flags=list(d.synthesis.origin.pending.rtl.framework.FLAGS)
            flags+=['-R',directory,'DestinationTest']
            for mutated in (False,True):
                path.write_text(source.replace(old,'| Decode.Add rd rs1 rs2 => [rs1]')if mutated else source)
                result,timed=d.run_stage([str(d.synthesis.ROOT/'_opam/bin/coqc'),*flags,str(path)],
                    Path(directory)/('wrong.log'if mutated else 'correct.log'),1200)
                self.assertFalse(timed)
                if not mutated:self.assertEqual(result.returncode,0,result.stdout+result.stderr)
                else:
                    self.assertNotEqual(result.returncode,0)
                    self.assertNotIn('Cannot find a physical path',result.stdout+result.stderr)


if __name__=='__main__':unittest.main()
