"""Lightweight discovery/render contracts; deliberately no native CPU build."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import cpu_add_family_joint as family


class FamilyJointTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        for folder in ['derived', 'queue', 'operand', 'ready', 'controls']:
            (root / folder).mkdir()
        providers = [dict(namespace='GeneratedPhasePendingCommit', directory=str(root / 'queue')),
                     dict(namespace='GeneratedOperandResultJoint', directory=str(root / 'operand'))]
        (root / 'derived/providers.json').write_text(json.dumps(providers))
        (root / 'queue/plan.json').write_text('{}')
        (root / 'ready/plan.json').write_text('{}')
        (root / 'controls/plan.json').write_text(json.dumps(dict(rows=[dict(root=91, width=1), dict(root=92, width=1)])))
        self.config = dict(derived_sources=str(root / 'derived'), ready_controls=str(root / 'ready'),
                           controls=str(root / 'controls'), ast_module='MockAST')
        self.physical = dict(ports=[dict(field='Rs2', operand=222), dict(field='Rs1', operand=111)],
                             head=dict(valid=333), bank=444)

    def discover(self, plan=None):
        with patch.object(family.derived, 'discover', return_value=copy.deepcopy(plan or self.physical)):
            return family.discover(self.config, {})

    def render(self):
        return family.render(self.config, {}, dict(ast=dict(program='mock_program')), self.discover())

    def test_roles_not_port_position(self):
        actual = self.discover()
        self.assertEqual((actual['left'], actual['right']), (111, 222))
        shuffled = copy.deepcopy(self.physical)
        shuffled['ports'].reverse()
        again = self.discover(shuffled)
        self.assertEqual((again['left'], again['right']), (111, 222))

    def test_missing_role_rejected(self):
        candidate = copy.deepcopy(self.physical)
        candidate['ports'] = candidate['ports'][:1]
        with self.assertRaisesRegex(ValueError, 'ISA source roles'):
            self.discover(candidate)

    def test_wrong_role_rejected(self):
        candidate = copy.deepcopy(self.physical)
        candidate['ports'][0]['field'] = 'Rd'
        with self.assertRaisesRegex(ValueError, 'ISA source roles'):
            self.discover(candidate)

    def test_current_has_no_queue_register_invariant(self):
        source, _ = self.render()
        current = source.split('Record Current', 1)[1].split('Theorem head_from_operand_clause', 1)[0]
        self.assertNotIn('QueueRegisterInv', source)
        self.assertIn('current_RF:RegisterRelated', current)
        self.assertIn('current_retired:EffectChain(instruction_effect', current)
        self.assertIn('current_pending:exists frontier,EffectChain(instruction_effect', current)
        self.assertIn('current_operands:OperandClause', current)

    def test_both_branches_use_real_original_isa_effects(self):
        source, exports = self.render()
        proof = source.split('Theorem head_from_operand_clause', 1)[1].split('Theorem actual_result_phase', 1)[0]
        self.assertEqual(proof.count('destruct(token_execute reference_pc token_word token before after _ HStep HD)'), 2)
        self.assertIn('original_add_effect before middle rd rs1 rs2 HEX', proof)
        self.assertIn('original_addi_effect before middle rd rs imm HEX', proof)
        self.assertIn('HSource x y HX HY', proof)
        self.assertIn('HSource x HX', proof)
        self.assertIn('read_signal (phase_driven_state mock_program ev pre) 111', proof)
        self.assertIn('read_signal (phase_driven_state mock_program ev pre) 222', proof)
        self.assertEqual(exports, ['sampled_add_controls', 'head_from_operand_clause', 'actual_result_phase'])

    def test_same_family_values_and_cut_rules(self):
        source, _ = self.render()
        self.assertIn('Module F:=CPUISAAddFamilyReferenceValues.', source)
        self.assertEqual(source.count('F.values reference_pc token_word token_id initial ledger'), 2)
        self.assertIn('V.Joint(F.values reference_pc token_word token_id initial ledger)', source)
        self.assertIn('V.Head(F.values reference_pc token_word token_id initial ledger)', source)
        self.assertIn('F.at_cut reference_pc token_word token_id initial ledger', source)
        self.assertIn('F.computed_add token_word token before rd rs1 rs2 x y HD HX HY', source)
        self.assertIn('F.addi_at_cut reference_pc token_word token_id initial ledger', source)
        self.assertNotIn('CPUISAAddReferenceValues', source)


if __name__ == '__main__':
    unittest.main(verbosity=2)
