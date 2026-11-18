import unittest
import cpu_add_family_ram_phase as phase


class FamilyRAMPhase(unittest.TestCase):
    def test_class_to_real_nonstore_and_prequiet(self):
        source,exports=phase.render(dict(ast_module='Configured'),dict(ast=dict(program='Program')),
            dict(pair=dict(valid_root=141),store_controller=dict(opcode=143,root=163),byte_bank=dict(root=327,width=1024)))
        self.assertIn('actual_opcode_19_nonstore',source)
        self.assertIn('actual_opcode_51_nonstore',source)
        self.assertIn('actual_quiet_RAM_phase ev pre seed HEv HL HQ',source)
        statement=source.split('Theorem actual_family_quiet_RAM_phase',1)[1].split('Proof.',1)[0]
        self.assertIn('StoreQuiet pre ->',statement)
        self.assertNotIn('StoreQuiet (PhaseSemantics Program ev pre) ->',statement)
        self.assertIn('ClassifiedFamily',statement)
        self.assertEqual(len(exports),4)


if __name__=='__main__':unittest.main()
