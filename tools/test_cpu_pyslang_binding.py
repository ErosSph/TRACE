import unittest
from cpu_pyslang_binding import bind


class BindingTests(unittest.TestCase):
    def setUp(self):
        self.table = [dict(id=7, path='top.stage.value', width=32, source_line=4)]
        self.symbol = dict(path='top.stage.value', width=32, line=4)

    def test_identity(self):
        self.assertEqual(bind(self.table, [self.symbol])[0]['coq_root'], 7)

    def test_wrong_width(self):
        with self.assertRaises(ValueError):
            bind(self.table, [dict(self.symbol, width=31)])

    def test_wrong_location(self):
        with self.assertRaises(ValueError):
            bind(self.table, [dict(self.symbol, line=8)])

    def test_wrong_instance(self):
        with self.assertRaises(ValueError):
            bind(self.table, [dict(self.symbol, path='top.other.value')])

    def test_ambiguous(self):
        with self.assertRaises(ValueError):
            bind(self.table, [self.symbol, self.symbol])

    def test_missing(self):
        with self.assertRaises(ValueError):
            bind(self.table, [])


if __name__ == '__main__':
    unittest.main()
