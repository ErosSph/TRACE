import unittest
import cpu_captured_rom as c
class Tests(unittest.TestCase):
    def test_abstraction_preserves_original_bit_operations(self):
        e=c.rtl.Parser('(ESel 32 (EVar 1024 9) (EBinary 32 BShiftL (EVar 32 8) (EConst 32 5)))').complete()
        self.assertEqual(c.abstract_read(e,9,8),'(ESel 32 (EConst 1024 image) (EBinary 32 BShiftL (EConst 32 address) (EConst 32 5)))')
    def test_unknown_dependency_rejected(self):
        with self.assertRaisesRegex(ValueError,'dependency'):
            c.abstract_read(c.rtl.Parser('(EVar 32 7)').complete(),9,8)
    def test_address_width_not_guessed(self):
        with self.assertRaisesRegex(ValueError,'dependency'):
            c.abstract_read(c.rtl.Parser('(EVar 16 8)').complete(),9,8)
    def test_unmatched_source_rejected(self):
        with self.assertRaisesRegex(ValueError,'capture source'):
            c.content_proof(c.rtl.Parser('(EVar 32 9)').complete(),c.rtl.Parser('(EConst 1 1)').complete(),7,8)
    def test_condition_mismatch_rejected(self):
        with self.assertRaisesRegex(ValueError,'unsupported'):
            c.content_proof(c.rtl.Parser('(ECond 32 (EVar 1 2) (EVar 32 8) (EVar 32 7))').complete(),
                            c.rtl.Parser('(ECond 1 (EVar 1 3) (EConst 1 1) (EConst 1 0))').complete(),7,8)
    def test_single_stage_uses_final_conjunction_component(self):
        source=c.render_pipeline(dict(rows=[dict(root=9)]))
        self.assertIn('((proj2 HR) token HT)',source)
        self.assertNotIn('(proj1 (proj2 HR))',source)
    def test_multiple_stages_connect_same_tag_to_history(self):
        source=c.render_pipeline(dict(rows=[dict(root=9),dict(root=12)]))
        self.assertIn('((proj1 (proj2 HR)) token HT)',source)
        self.assertIn('((proj2 (proj2 HR)) token HT)',source)
        self.assertIn('chain_tag1(snd(H.boot_history image events))=Some token',source)
    def test_empty_pipeline_rejected(self):
        with self.assertRaisesRegex(ValueError,'empty'):
            c.render_pipeline(dict(rows=[]))
if __name__=='__main__':unittest.main()
