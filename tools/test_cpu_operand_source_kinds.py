import unittest
import cpu_operand_routes as routes

T = routes.rtl.Term
def var(root):
    return T('EVar',(T('32'),T(str(root))))


class SourceKinds(unittest.TestCase):
    def test_known_transport(self):
        self.assertEqual(routes.source_kind(2,var(2),{2}),'transported_rf_data')

    def test_other_mux_input_not_automatically_forward(self):
        self.assertEqual(routes.source_kind(3,var(3),{2}),'unclassified_external_data')

    def test_constant_not_automatically_invalid(self):
        expr=T('EConst',(T('32'),T('0')))
        self.assertEqual(routes.source_kind(None,expr,{2}),'constant_data')

    def test_transformation_is_not_transport(self):
        expr=T('EBinary',(T('32'),T('BAdd'),var(2),var(3)))
        self.assertEqual(routes.source_kind(None,expr,{2}),'transformed_rf_data')

    def test_unrelated_calculation_unclassified(self):
        expr=T('EBinary',(T('32'),T('BAdd'),var(3),var(4)))
        self.assertEqual(routes.source_kind(None,expr,{2}),'unclassified_expression')


if __name__ == '__main__':unittest.main()
