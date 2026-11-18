import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import cpu_add_admission_queue as queue


class Tests(unittest.TestCase):
    def source(self):
        plan=dict(birth=dict(event=dict(reset=132)),head=dict(process='capture',valid=250))
        return queue.render(dict(ast_module='Input.AST'),dict(module='DUT'),dict(ast=dict(program='DUT.program')),plan)

    def test_queue_equality_is_conclusion_not_input(self):
        header=self.source().split('Theorem actual_admission_pending_transfer',1)[1].split('Proof.',1)[0]
        self.assertEqual(header.count('actual_pending'),2)
        self.assertNotIn('actual_pending pre',header.split('->')[-2])
        self.assertIn('++admitted ev pre',header.split('->')[-1])

    def test_result_uses_actual_post_queue_and_post_history(self):
        header=self.source().split('Theorem actual_admission_restores_operand_clause',1)[1].split('Proof.',1)[0]
        self.assertIn('retired++GeneratedPhasePendingCommit.PhasePendingCommit.actual_pending (PhaseSemantics DUT.program ev pre)',header)
        self.assertIn('D.Captured.advance_capture_fields ev pre',header)
        self.assertNotIn('CertifiedBatches',header)
        self.assertNotIn('SlotRelated',header)

    def test_ghost_step_and_view_connections_are_proved(self):
        source=self.source()
        self.assertIn('Lemma repack_step',source)
        self.assertIn('Lemma view_agreement',source)
        self.assertIn('rising_waiting_conserved',source)
        self.assertIn('actual_admission_pending_transfer image events ev HE HEv HM HV',source)

    def test_native_provider_receipt_rejects_scope_or_axiom_changes(self):
        with tempfile.TemporaryDirectory()as d:
            folder=Path(d);text='unit fixture, not a native proof'
            (folder/'DerivedSources.v').write_text(text);(folder/'DerivedSources.vo').write_text('unit placeholder')
            (folder/'plan.json').write_text(json.dumps(dict(ast_sha256='same')))
            report=dict(accepted=True,coqc_exit=0,coqchk_exit=0,assumptions_audit_passed=True,old_inv_read=False,
                ast_sha256='same',isa_assumptions=[],baseline_assumptions=[],source_sha256=hashlib.sha256(text.encode()).hexdigest())
            def save():
                (folder/'report.json').write_text(json.dumps(report))
            save();self.assertEqual(queue.checked_sources(d,'same')['ast_sha256'],'same')
            report['isa_assumptions']=['CPU_always_correct'];save()
            with self.assertRaisesRegex(ValueError,'native-checked'):
                queue.checked_sources(d,'same')
            report['isa_assumptions']=[];report['old_inv_read']=True;save()
            with self.assertRaisesRegex(ValueError,'native-checked'):
                queue.checked_sources(d,'same')

    def test_source_provider_mutation_is_rejected(self):
        with tempfile.TemporaryDirectory()as d:
            folder=Path(d)
            (folder/'DerivedSources.v').write_text('different');(folder/'DerivedSources.vo').write_text('unit placeholder')
            (folder/'plan.json').write_text(json.dumps(dict(ast_sha256='same')))
            (folder/'report.json').write_text(json.dumps(dict(accepted=True,coqc_exit=0,coqchk_exit=0,
                assumptions_audit_passed=True,old_inv_read=False,ast_sha256='same',isa_assumptions=[],
                baseline_assumptions=[],source_sha256=hashlib.sha256(b'original').hexdigest())))
            with self.assertRaisesRegex(ValueError,'native-checked'):
                queue.checked_sources(d,'same')

    def test_changed_control_path_is_not_reused(self):
        with tempfile.TemporaryDirectory()as d:
            normal=Path(d)/'normal-phase';normal.mkdir()
            (normal/'plan.json').write_text(json.dumps(dict(rising_paths=[dict(guard='old')])) )
            with patch.object(queue.normal,'discover',return_value=dict(rising_paths=[dict(guard='changed')])):
                with self.assertRaisesRegex(ValueError,'physical path/control/phase'):
                    queue.checked_physical(d,dict(source_sha256='same'))

    def test_changed_native_object_is_not_reused(self):
        with tempfile.TemporaryDirectory()as d:
            folder=Path(d);normal=folder/'normal-phase';normal.mkdir()
            (normal/'plan.json').write_text(json.dumps(dict(rising_paths=['same'])))
            first=folder/'capture-birth';first.mkdir();text='unit fixture'
            (first/'CaptureBirth.v').write_text(text);(first/'CaptureBirth.vo').write_text('changed')
            (first/'plan.json').write_text(json.dumps(dict(ast_sha256='same')))
            (first/'report.json').write_text(json.dumps(dict(accepted=True,coqc_exit=0,coqchk_exit=0,
                assumptions_closed=True,old_inv_read=False,old_pending_read=False,ast_sha256='same',
                source_sha256=hashlib.sha256(text.encode()).hexdigest(),object_sha256=hashlib.sha256(b'original').hexdigest())))
            with patch.object(queue.normal,'discover',return_value=dict(rising_paths=['same'])):
                with self.assertRaisesRegex(ValueError,'physical provider'):
                    queue.checked_physical(d,dict(source_sha256='same'))


if __name__=='__main__':unittest.main()
