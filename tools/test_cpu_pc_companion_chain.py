import unittest
from unittest.mock import patch
import cpu_pc_companion_chain as c

class CompanionTests(unittest.TestCase):
    def match(self,e,r):return c.match_recipe(c.rtl.Parser(e).complete(),c.RecipeParser(r).complete(),7)
    def test_capture_is_exact_scalar_copy(self):
        self.assertEqual(self.match('(EVar 32 8)','Capture')[0],{8})
        self.assertIsNone(self.match('(EVar 5 8)','Capture'))
    def test_hold_cannot_change_companion(self):
        self.assertIsNotNone(self.match('(EVar 32 7)','Hold'))
        self.assertIsNone(self.match('(EVar 32 8)','Hold'))
    def test_unknown_does_not_imply_zero_or_valid(self):
        self.assertEqual(self.match('(EConst 32 99)','Unknown')[0],set())
    def test_guard_mismatch_rejected(self):
        self.assertIsNone(self.match('(ECond 32 (EVar 1 1) (EVar 32 8) (EConst 32 0))','(Select (EVar 1 2) Capture Unknown)'))
    def test_shared_recipe_tracks_both_paths(self):
        result=self.match('(ECond 32 (EVar 1 1) (EVar 32 8) (EVar 32 9))','(Select (EVar 1 1) Capture Capture)')
        self.assertEqual(result[0],{8,9})
    def test_ambiguous_companion_is_not_guessed(self):
        chain=dict(rows=[dict(process='p',recipe='Capture')],edges=[])
        scalars=[dict(root=r,width=32,process='p',next_expression='(EVar 32 9)')for r in [20,21]]
        with patch.object(c.pc.fetch.origin.pending,'analyze',return_value=dict(scalar_transitions=scalars)),patch.object(c.pc.fetch.rom.aliases,'trace',return_value=dict(terminal=7,edges=[])):
            with self.assertRaisesRegex(ValueError,'got 2'):c.discover({},chain,7)
    def test_cyclic_chain_does_not_loop(self):
        chain=dict(rows=[dict(process='p',recipe='Capture')],edges=[dict(target=0,source=0)])
        with patch.object(c.pc.fetch.origin.pending,'analyze',return_value=dict(scalar_transitions=[])):
            with self.assertRaisesRegex(ValueError,'cyclic'):c.discover({},chain,7)
    def test_write_connection_selects_endpoint_not_last_stage(self):
        source=c.render_write_identity('AST.program',[dict(root=40),dict(root=50)],
            dict(rows=[dict(root=4),dict(root=5)]),dict(endpoint=4),
            dict(process='process_2',guards=[('(EVar 1 7)',True)],total=1024,bank=9,data='(EVar 32 8)'))
        self.assertIn('chain_tag0(snd packed)',source)
        self.assertIn('read_signal pre 40',source)
        self.assertIn('(proj1 HF) token HT',source)
        self.assertNotIn('chain_tag1(snd packed)',source)
        self.assertIn('actual_write_destination_from_boot',source)
    def test_unknown_write_endpoint_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'one token stage'):
            c.render_write_identity('AST.program',[dict(root=40)],dict(rows=[dict(root=4)]),dict(endpoint=99),{})
    def test_rom_connection_uses_the_same_write_token(self):
        source=c.render_write_identity('AST.program',[dict(root=40)],dict(rows=[dict(root=4)]),
            dict(endpoint=4),dict(process='p',guards=[],total=1024,bank=9,data='(EVar 32 8)'),True)
        self.assertIn('actual_write_pc_rom_identity',source)
        self.assertIn('RR.pipeline_field_0_content image events token HE HT',source)
        self.assertIn('RR.content_at_pc image token _ HC HPC',source)
        self.assertIn('token_word token=RR.lookup image(norm 32(read_signal pre 40))',source)

if __name__=='__main__':unittest.main()
