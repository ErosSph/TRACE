import unittest
from check_reference_value_rules import audit_all_exports


class Tests(unittest.TestCase):
    def test_closed_export_must_not_hide_axiom_of_another_export(self):
        output = ('Closed under the global context\nChars 0 [Print.] 0 secs\n'
                  'Axioms:\nUnexpected.cpu_correct : Prop\nChars 1 [Print.] 0 secs\n')
        self.assertEqual(audit_all_exports(output, 2), {'Unexpected.cpu_correct'})

    def test_missing_export_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'missing or extra'):
            audit_all_exports('Closed under the global context\n', 2)


if __name__ == '__main__':
    unittest.main()
