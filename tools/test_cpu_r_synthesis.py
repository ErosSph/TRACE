import unittest
import tempfile
from contextlib import ExitStack
from unittest.mock import patch
from pathlib import Path
import cpu_r_synthesis as r


class RelationSynthesisTests(unittest.TestCase):
    def test_partial_components_never_mean_end_to_end_success(self):
        flags=dict(complete_R_generated=True,initialization_proved=True,preservation_proved=True)
        self.assertEqual(r.exit_status(flags,True),0)
        self.assertEqual(r.exit_status(flags,False),1)
        self.assertEqual(r.exit_status({},True),1)
        for name in flags:
            for value in (False,None,'true',1):
                partial=dict(flags);partial[name]=value
                self.assertEqual(r.exit_status(partial,True),1)
        self.assertEqual(r.exit_status({},False,analysis_only=True),0)

    def setUp(self):
        self.source = (r.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text()

    def test_actual_38_branches_and_dependencies(self):
        plan = r.isa_demands(self.source)
        rows = {row['instruction']: row for row in plan['instructions']}
        self.assertEqual(len(rows), 38)
        self.assertEqual(rows['Add']['calls'], ['getRegister', 'setRegister'])
        self.assertIn('memory_write', rows['Sw']['obligations'])
        self.assertIn('memory_read', rows['Lbu']['obligations'])
        self.assertIn('redirect_target', rows['Jalr']['obligations'])
        self.assertIn('exception_or_domain_certificate', rows['Jalr']['obligations'])
        self.assertEqual(rows['Fence_i']['calls'], [])
        self.assertIn('memory_frame', rows['Fence_i']['obligations'])
        self.assertFalse(plan['semantic_footprint_soundness_proved'])

    def test_unknown_isa_effect_is_not_silently_dropped(self):
        with self.assertRaises(ValueError):
            r.isa_demands(self.source.replace('Spec.Machine.setRegister', 'Spec.Machine.unknownEffect', 1))

    def test_reference_inputs_come_from_actual_uses(self):
        rows={x['instruction']:x['reference_uses']for x in r.isa_demands(self.source)['instructions']}
        self.assertEqual([(x['kind'],x.get('field'))for x in rows['Add']['inputs']],
                         [('register_value','rs1'),('register_value','rs2')])
        self.assertEqual([(x['kind'],x.get('field'))for x in rows['Addi']['inputs']],
                         [('register_value','rs1'),('instruction_parameter','imm12')])
        self.assertEqual([x['kind']for x in rows['Auipc']['inputs']],
                         ['instruction_pc','instruction_parameter'])
        self.assertEqual(rows['Fence_i']['inputs'],[])
        self.assertFalse(rows['Add']['semantic_input_correspondence_proved'])

    def test_field_rename_does_not_guess_role(self):
        body='Bind (Spec.Machine.getRegister arbitrary) (fun x => Spec.Machine.setRegister output x)'
        uses=r.isa_input_uses(body,['output','arbitrary'])
        self.assertEqual(uses['inputs'][0]['field'],'arbitrary')
        self.assertEqual(uses['destinations'][0]['field'],'output')

    def test_computed_register_argument_fails_closed(self):
        with self.assertRaises(ValueError):
            r.isa_input_uses('Spec.Machine.getRegister (rs + 1)',['rs'])

    def test_missing_instruction_is_rejected(self):
        with self.assertRaises(ValueError):
            r.isa_demands(self.source.replace('| Spec.Decode.Add rd rs1 rs2 =>', '| unknown =>'))

    def test_comments_cannot_introduce_demands(self):
        self.assertEqual(r.isa_demands(self.source)['instructions'],
                         r.isa_demands(self.source+'\n(* Spec.Machine.unknownEffect *)')['instructions'])
        with self.assertRaises(ValueError): r.remove_comments('(* unterminated')

    def test_relation_generation_does_not_read_old_proofs(self):
        with patch.object(Path, 'read_text', side_effect=AssertionError('unexpected proof lookup')):
            source = r.relation_source(91, 'Raw.program')
        self.assertIn('read_signal s 91', source)
        self.assertIn('ISAProjectedRegisterEffects', source)
        self.assertNotIn('Admitted', source)
        self.assertNotIn('Axiom ', source)
        self.assertNotIn('joint_cycle', source)

    def test_backward_search_keeps_guards_and_stops_at_registers(self):
        parse = r.origin.pending.rtl.Parser
        def proc(name, kind, root, body):
            return dict(name=name, kind=kind, writers=[root], events=[], line=1,
                        body=parse(body).complete())
        ast = dict(processes=[
            proc('write', 'Sequential', 9,
                 'SIf (EVar 1 5) (SAssign true (EVar 32 2) (LVar 32 9)) SSkip'),
            proc('mux', 'Combinational', 2,
                 'SAssign false (EVar 32 3) (LVar 32 2)'),
            proc('stage', 'Sequential', 3,
                 'SAssign true (EVar 32 7) (LVar 32 3)')])
        result = r.backward_frontier(ast, 9)
        self.assertEqual(result['external_inputs'], [5])
        self.assertEqual(result['sequential_boundary'], [3])
        self.assertNotIn(7, result['external_inputs'])
        self.assertFalse(result['semantic_slice_proved'])

    def test_native_pipeline_checks_capture_and_branch_components(self):
        # Check orchestration, not hardware semantics: a failed capture must
        # remain visible and cannot be promoted to successful complete R.
        with tempfile.TemporaryDirectory() as directory, ExitStack() as stack:
            ast = dict(source_sha256='test', processes=[])
            stack.enter_context(patch.object(r.origin, 'raw_binding',
                return_value=(ast, dict(ast=dict(program='Raw.p')), [])))
            stack.enter_context(patch.object(r.operand_routes, 'discover',
                return_value=dict(routes=[])))
            stack.enter_context(patch.object(r.roles, 'derive_candidates',
                return_value=dict(register_file=[], pc=[])))
            calls = {}
            bank_indices=stack.enter_context(patch('cpu_bank_index_certificate.check',
                return_value=dict(accepted=True,actual_selected_write_proved=False)))
            stack.enter_context(patch('cpu_fixed_lane_enable.check',
                return_value=dict(accepted=True)))
            fixed_lfp=stack.enter_context(patch('cpu_fixed_lane_lfp.check',
                return_value=dict(accepted=False,full_lfp_bit_connection_proved=False)))
            reference_inputs=stack.enter_context(patch.object(r.reference_requirements,'check',
                return_value=dict(accepted=False,complete_R_generated=False)))
            isa_inputs=stack.enter_context(patch.object(r,'check_isa_input_certificate',
                return_value=dict(accepted=True)))
            stack.enter_context(patch('cpu_isa_destination_certificate.run',
                return_value=dict(accepted=True)))
            decoded_inputs=stack.enter_context(patch.object(r.decoded_addresses,'run',
                return_value=dict(accepted=False,provider='checked-fields')))
            destination_fields=stack.enter_context(patch('cpu_destination_field_connection.check',
                return_value=dict(accepted=False,current_token_identity_proved=False,
                                  status='no_supported_rd_field')))
            captured_inputs=stack.enter_context(patch.object(r.capture_addresses,'automatic',
                return_value=dict(accepted=False,status='no_supported_capture_address_join')))
            history_inputs=stack.enter_context(patch.object(r.history_addresses,'check',
                return_value=dict(accepted=False,status='no_direct_word_address_cone')))
            registered_inputs=stack.enter_context(patch.object(r.registered_addresses,'check',
                return_value=dict(accepted=False,connections=0)))
            tagged_inputs=stack.enter_context(patch.object(r.tagged_capture_addresses,'check',
                return_value=dict(accepted=False,connections=0)))
            calls['blocking_residuals'] = stack.enter_context(patch.object(r.blocking_residuals, 'run',
                return_value=dict(accepted=False,status='unclosed_residuals')))
            for name in ['operands', 'route_proofs', 'ready_selection', 'branch_proofs', 'capture_proofs', 'address_origins','selector_sources','control_captures','nonzero_capture','nonzero_projection','synchronized_values','zero_instruction_rf']:
                calls[name] = stack.enter_context(patch.object(getattr(r, name), 'check',
                    return_value=dict(accepted=name!='capture_proofs',
                        **({'tagged_origins':dict(accepted=True)}if name=='address_origins'else{}))))
            calls['selector_proofs'] = stack.enter_context(patch.object(r.selector_proofs, 'check_discovered',
                return_value=dict(accepted=False)))
            calls['control_histories'] = stack.enter_context(patch.object(r.control_captures, 'check_histories',
                return_value=dict(accepted=False)))
            calls['control_transforms'] = stack.enter_context(patch.object(r.control_captures, 'check_transforms',
                return_value=dict(accepted=False)))
            calls['synchronized_fields'] = stack.enter_context(patch.object(r.projection_origins, 'check_synchronized',
                return_value=dict(accepted=False)))
            calls['narrow_fields'] = stack.enter_context(patch.object(r.projection_origins, 'check_narrow',
                return_value=dict(accepted=False)))
            calls['field_chains'] = stack.enter_context(patch.object(r.field_chain_history, 'check',
                return_value=dict(accepted=False)))
            calls['capture_field_chains'] = stack.enter_context(patch.object(r.capture_field_chain, 'check',
                return_value=dict(accepted=False)))
            calls['capture_chain_coverage'] = stack.enter_context(patch.object(r.capture_chain_coverage, 'check',
                return_value=dict(accepted=False)))
            calls['word_field_copies'] = stack.enter_context(patch.object(r.word_field_copy, 'check',
                return_value=dict(accepted=False)))
            calls['field_selector_origins'] = stack.enter_context(patch.object(r.field_selector_origin, 'check',
                return_value=dict(accepted=False)))
            calls['write_address_histories'] = stack.enter_context(patch.object(r.write_address_history, 'check',
                return_value=dict(accepted=False)))
            calls['selector_joint'] = stack.enter_context(patch.object(r.selector_joint, 'check_auto',
                return_value=dict(accepted=False)))
            calls['selector_metadata'] = stack.enter_context(patch.object(r.selector_metadata, 'check_auto',
                return_value=dict(accepted=False)))
            gap_rules = stack.enter_context(patch.object(r.validity_strategy, 'run',
                return_value=dict(accepted=False, local_proof_generated=False)))
            write_gaps = stack.enter_context(patch.object(r.write_strategy, 'run',
                return_value=dict(accepted=False, proof_generated=False)))
            field_gaps = stack.enter_context(patch.object(r.field_selector_gap, 'run',
                return_value=dict(accepted=False, proof_generated=False)))
            address_cases=stack.enter_context(patch.object(r.address_case_completion,'run',
                return_value=dict(checks={},complete_R_generated=False)))
            report = r.run('raw.v', 'Raw.AST', Path(directory)/'generated',use_llm=True,key='test')
            isa_inputs.assert_called_once()
            bank_indices.assert_called_once()
            self.assertFalse(report['bank_index_certificate']['actual_selected_write_proved'])
            fixed_lfp.assert_called_once()
            self.assertFalse(report['fixed_lane_lfp_certificate']['accepted'])
            self.assertFalse(report['fixed_lane_lfp_certificate']['full_lfp_bit_connection_proved'])
            reference_inputs.assert_called_once()
            self.assertFalse(report['operand_reference_requirements']['accepted'])
            address_cases.assert_called_once()
            decoded_inputs.assert_called_once()
            self.assertEqual(destination_fields.call_count,2)
            self.assertIn('tagged_provider',destination_fields.call_args_list[1].kwargs)
            self.assertFalse(report['tagged_destination_field_connections']['accepted'])
            self.assertFalse(report['destination_field_connections']['accepted'])
            captured_inputs.assert_called_once()
            history_inputs.assert_called_once()
            registered_inputs.assert_called_once()
            tagged_inputs.assert_called_once()
            self.assertFalse(report['registered_operand_addresses']['accepted'])
            self.assertFalse(report['history_operand_addresses']['accepted'])
            self.assertFalse(report['captured_operand_addresses']['accepted'])
            self.assertFalse(report['decoded_address_connections']['accepted'])
            self.assertTrue(report['isa_input_certificate']['accepted'])
            for name,call in calls.items():
                if name=='zero_instruction_rf':
                    self.assertEqual(call.call_count,4)
                    self.assertTrue(call.call_args_list[1].kwargs['derive_condition'])
                    self.assertTrue(call.call_args_list[2].kwargs['derive_reference'])
                    self.assertTrue(call.call_args_list[3].kwargs['derive_slices'])
                elif name=='field_selector_origins':
                    self.assertEqual(call.call_count,2)
                    self.assertTrue(call.call_args_list[1].kwargs['projected'])
                else:call.assert_called_once()
            self.assertFalse(report['operand_capture_equations']['accepted'])
            self.assertFalse(report['operand_selector_equations']['accepted'])
            self.assertFalse(report['accepted'])
            write_gaps.assert_called_once()
            field_gaps.assert_called_once()
            self.assertFalse(report['llm_register_write_gaps']['proof_generated'])
            self.assertEqual(gap_rules.call_count,2)
            self.assertTrue(all(call.kwargs['check_proposals']for call in gap_rules.call_args_list))
            self.assertTrue(gap_rules.call_args_list[1].kwargs['metadata'])


if __name__ == '__main__': unittest.main()
