import unittest
from pathlib import Path
from unittest.mock import patch
import cpu_bank_requirements as r


class BankRequirementsTests(unittest.TestCase):
    def compile(self,text):
        # BankPlan is generated internally, not accepted by the RTL parser.
        with patch.dict(r.rtl.ARITIES,dict(BPSeq=1,BPIf=3,BPReset=1,BPWord=2,BPEmpty=0)):
            term=r.rtl.Parser(text).complete()
        c=r.Compiler();c.compile(term);return '\n'.join(c.lines)

    def test_reset_and_hold_not_dropped(self):
        source=self.compile('(BPIf (EVar 1 7) BPEmpty (BPReset (EConst 1024 0)))')
        self.assertIn('reset_correct',source)
        self.assertIn('empty_correct',source)
        self.assertIn('branch_correct',source)

    def test_ordered_overlapping_writes_preserved(self):
        source=self.compile('(BPSeq [(BPWord (EConst 10 32) (EVar 32 4)); (BPWord (EConst 10 32) (EVar 32 5))])')
        self.assertIn('sequence [bank_wp_0;bank_wp_1]',source)
        self.assertIn('(EVar 32 4)',source)
        self.assertIn('(EVar 32 5)',source)

    def test_unknown_structure_rejected(self):
        with self.assertRaises(ValueError):self.compile('BPUnknown')

    def test_identical_subtrees_share_proof_not_write_occurrence(self):
        source=self.compile('(BPSeq [BPEmpty;BPEmpty])')
        self.assertIn('sequence [bank_wp_0;bank_wp_0]',source)
        self.assertEqual(source.count('Lemma bank_wp_0_correct'),1)

    def test_no_existing_inv_or_file_lookup(self):
        with patch.object(Path,'read_text',side_effect=AssertionError('old proof read')):
            source=self.compile('(BPWord (EConst 10 64) (EVar 32 99))')
        self.assertNotIn('Admitted',source)
        self.assertNotIn('Axiom ',source)

    def test_audit_ignores_timing_echo_but_rejects_axiom(self):
        log='BANK_REQUIREMENT_AUDIT\nChars [idtac "BANK_REQUIREMENT_AUDIT".]\n'+(
            'Closed under the global context\n'*2)
        with patch.object(r.bank,'audit_bank_output',return_value=(True,[])):
            self.assertTrue(r.audit(log,1))
            self.assertFalse(r.audit(log+'Axioms: new_axiom\n',1))
            self.assertFalse(r.audit(log,2))

    def test_budget_checked_before_any_work(self):
        for budget in (0,-1,1201):
            with self.assertRaises(ValueError):r.check(None,None,None,budget)


if __name__=='__main__':unittest.main()
