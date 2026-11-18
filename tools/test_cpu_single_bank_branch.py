import unittest
from unittest.mock import patch
import cpu_single_bank_branch as r


class SingleBranchTests(unittest.TestCase):
    def parse(self,text):
        with patch.dict(r.rtl.ARITIES,dict(BPSeq=1,BPIf=3,BPReset=1,BPWord=2,BPEmpty=0)):
            return r.rtl.Parser(text).complete()

    def discover(self,plan,multiple=False):
        proc=dict(name='p')
        plans=[(proc,None,self.parse(plan))]
        if multiple:plans*=2
        with patch.object(r.indices.ownership.bank,'analyze',return_value=dict(
                banks=[dict(root=100,total=1024,plans=plans)])):
            return r.discover({},7)

    write='(BPWord (EBinary 12 BMul (EVar 5 7) (EConst 12 32)) (EVar 32 8))'

    def test_guarded_single_write(self):
        matches=self.discover(f'(BPIf (EVar 1 3) {self.write} BPEmpty)')
        self.assertEqual(len(matches),1)
        self.assertEqual(matches[0]['guards'],[('(EVar 1 3)',True)])

    def test_reset_branch_retained_as_guard(self):
        matches=self.discover(f'(BPIf (EVar 1 3) {self.write} (BPReset (EConst 1024 0)))')
        self.assertEqual(len(matches),1)
        self.assertEqual(matches[0]['guards'],[('(EVar 1 3)',True)])

    def test_second_simultaneous_write_rejected(self):
        self.assertEqual(self.discover(f'(BPSeq [{self.write};{self.write}])'),[])

    def test_unresolved_sibling_branch_rejected(self):
        self.assertEqual(self.discover(f'(BPSeq [{self.write};(BPIf (EVar 1 3) BPEmpty (BPReset (EConst 1024 0)))])'),[])

    def test_multiple_writers_not_silently_ignored(self):
        self.assertEqual(self.discover(self.write,multiple=True),[])

    def test_contradictory_guard_path_rejected(self):
        self.assertEqual(self.discover(f'(BPIf (EVar 1 3) (BPIf (EVar 1 3) BPEmpty {self.write}) BPEmpty)'),[])

    def test_same_guard_can_discharge_empty_sibling(self):
        matches=self.discover(f'(BPSeq [(BPIf (EVar 1 3) {self.write} BPEmpty);(BPIf (EVar 1 3) BPEmpty (BPReset (EConst 1024 0)))])')
        self.assertEqual(len(matches),1)


if __name__=='__main__':unittest.main()
