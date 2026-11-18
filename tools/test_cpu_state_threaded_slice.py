import unittest
import cpu_state_threaded_slice as s


class StateSliceTests(unittest.TestCase):
    def proc(self,body):return dict(kind='Combinational',body=s.rtl.Parser(body).complete())

    def test_transitive_temporary_reads_retained(self):
        p=self.proc('SSeq [(SAssign false (EVar 1 9) (LVar 1 2));(SAssign false (EVar 1 2) (LVar 1 3));(SIf (EVar 1 3) (SAssign false (EConst 1 1) (LVar 1 4)) (SAssign false (EConst 1 0) (LVar 1 4)))]')
        plan,body=s.closure(p,4)
        self.assertEqual(plan['targets'],[2,3,4])
        self.assertEqual(body,p['body'])
        self.assertEqual(plan['external_inputs'],[9])

    def test_late_overwrite_not_deleted(self):
        p=self.proc('SSeq [(SAssign false (EConst 1 1) (LVar 1 4));(SAssign false (EVar 1 9) (LVar 1 2));(SIf (EVar 1 2) (SAssign false (EConst 1 0) (LVar 1 4)) SSkip);(SAssign false (EConst 1 1) (LVar 1 8))]')
        plan,body=s.closure(p,4)
        self.assertEqual(plan['targets'],[2,4])
        self.assertEqual(body.args[0].args[-1].name,'SSkip')
        self.assertEqual(body.args[0].args[-2],p['body'].args[0].args[-2])

    def test_self_read_terminates_closure_without_changing_read(self):
        p=self.proc('SAssign false (EUnary 1 UNot (EVar 1 4)) (LVar 1 4)')
        plan,body=s.closure(p,4)
        self.assertEqual(plan['targets'],[4]);self.assertEqual(body,p['body'])

    def test_case_key_dependency_is_retained(self):
        p=self.proc('SSeq [(SAssign false (EVar 1 9) (LVar 1 2));(SCase (EVar 1 8) [((Some (EVar 1 2)),(SAssign false (EConst 1 1) (LVar 1 4)))])]')
        plan,_=s.closure(p,4);self.assertEqual(plan['targets'],[2,4])


if __name__=='__main__':unittest.main()
