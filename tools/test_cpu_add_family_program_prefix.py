import unittest
import cpu_add_family_program_prefix as program


class StaticFamilyCertificate(unittest.TestCase):
    def test_original_decoder_and_domain(self):
        source,exports=program.render_static(dict(ast_module='Configured'),dict(ast=dict(program='Program')),
                                              dict(capacity=101,offset_width=12))
        certificate=source.split('Definition FamilyProgram',1)[1].split('Definition family_programb',1)[0]
        self.assertIn('Forall(Word 32)words',certificate)
        self.assertIn('Forall FamilyWord words',certificate)
        self.assertIn('(length words<=101)%nat',certificate)
        self.assertNotIn('Current',certificate)
        self.assertNotIn('MemoryJoint',certificate)
        self.assertIn('Decode.decode Decode.RV32I code',source)
        self.assertIn('lookup_packed 101%nat 12%nat',source)
        self.assertIn('rejects_xori',exports)
        self.assertIn('rejects_over_capacity',exports)

    def test_unknown_alias_domain_rejected(self):
        with self.assertRaises(ValueError):program.validate_domain(dict(capacity=130,offset_width=12))

    def test_empty_physical_rom_rejected(self):
        with self.assertRaises(ValueError):program.validate_domain(dict(capacity=0,offset_width=12))

    def test_real_family_cycle_and_bounded_not_retirement_count(self):
        source,exports=program.render(dict(ast_module='Configured'),dict(ast=dict(program='Program')),
                                      dict(capacity=101,offset_width=12,enable_root=156))
        self.assertIn('GeneratedAddFamilyMemoryCycle.AddFamilyMemoryCycle.actual_family_memory_cycle',source)
        self.assertIn('GeneratedAddFamilyMemoryJoint.AddFamilyMemoryJoint.actual_boot_boundary_and_family_joint',source)
        self.assertIn('(cycles<=length words)%nat',source)
        self.assertIn('(i<=cycles)%nat',source)
        self.assertIn('EffectChain CPUOriginalISAReference.original_step',source)
        self.assertNotIn('GeneratedClassifiedJoint',source)
        self.assertNotIn('actual_normal_ADD_cycle',source)
        self.assertNotIn('QueueRegisterInv',source)


if __name__=='__main__':unittest.main()
