import unittest
import cpu_pending_joint_history as h


def connection(root,valid,source,source_valid,kind='copy',width=5):
    return dict(coverage=dict(root=root,valid_root=valid,source=source,source_valid=source_valid,width=width),
        provider=dict(kind=kind,index=0))


class JointHistoryTests(unittest.TestCase):
    def test_network_is_built_from_birth_not_a_supplied_origin(self):
        slots=h.layout([dict(carrier=1,valid_root=2)],[connection(3,4,1,2,'connected'),connection(5,6,3,4)])
        self.assertEqual([s['root']for s in slots],[3,5])
        self.assertEqual(slots[0]['source_tag'],'current(joint_birth g)')
        self.assertEqual(slots[1]['source_tag'],'joint_tag_0 g')
        self.assertEqual(slots[0]['ref'],slots[1]['ref'])
        self.assertEqual(slots[0]['source_recorded'],'CaptureRecorded')
        self.assertEqual(slots[1]['source_recorded'],'RecordField0')

    def test_dependencies_not_input_order_determine_proof_order(self):
        slots=h.layout([dict(carrier=1,valid_root=2)],[connection(5,6,3,4),connection(3,4,1,2,'connected')])
        self.assertEqual([s['root']for s in slots],[3,5])
        self.assertEqual(slots[1]['source_recorded'],'RecordField1')

    def test_bad_validity_is_not_silently_accepted(self):
        with self.assertRaises(ValueError):h.layout([dict(carrier=1,valid_root=2)],[connection(3,4,1,99,'connected')])

    def test_disconnected_cycle_is_not_filled_from_old_pending(self):
        with self.assertRaises(ValueError):h.layout([dict(carrier=1,valid_root=2)],
            [connection(3,4,5,6),connection(5,6,3,4)])

    def test_missing_birth_or_metadata_is_not_a_vacuous_inv(self):
        for births,rows in[([],[]),([dict(carrier=1,valid_root=2)],[])]:
            with self.assertRaises(ValueError):h.layout(births,rows)


if __name__=='__main__':unittest.main()
