import unittest
import cpu_add_family_memory_joint as memory


class MemoryJointStructure(unittest.TestCase):
    def render(self,width=1024):
        return memory.render(dict(ast_module='Configured'),dict(ast=dict(program='Program')),
                             dict(byte_bank=dict(width=width,root=327)))

    def test_same_frontier_and_current(self):
        source,exports=self.render()
        relation=source.split('Definition FamilyMemoryJoint',1)[1].split('Theorem family_current',1)[0]
        self.assertIn('GeneratedAddFamilyJoint.AddFamilyJoint.Current',relation)
        self.assertNotIn('GeneratedDerivedSources',relation)
        self.assertNotIn('QueueRegisterInv',source)
        self.assertEqual(relation.count('exists frontier,'),1)
        self.assertIn('FrontierAt pre frontier i words',relation)
        self.assertIn('NextPCAligned frontier',relation)
        self.assertIn('CPUByteBankRelation.Related 1024 327%nat 128%nat',relation)
        self.assertEqual(len(exports),9)

    def test_no_old_complete_initialization(self):
        source,_=self.render()
        self.assertNotIn('GeneratedJointInitial',source)
        self.assertNotIn('GeneratedMemoryJoint.MemoryJoint',source)
        self.assertIn('GeneratedAddFamilyInitial.AddFamilyInitial.actual_boot_current',source)
        self.assertIn('GeneratedRAMInitial.RAMInitial.actual_boot_original_memory',source)
        self.assertIn('ExtendedSVCaptureContent.empty_related',source)

    def test_unaligned_bank_rejected(self):
        with self.assertRaises(ValueError):self.render(1023)


if __name__=='__main__':unittest.main()
