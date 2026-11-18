import unittest
from unittest.mock import patch
import cpu_word_field_copy as c

class WordFieldCopyTests(unittest.TestCase):
    def discover(self,producers,consumers):
        with patch.object(c.p,'discover',return_value={'projections':producers}),patch.object(c.p,'discover_narrow_fields',return_value={'projections':consumers}):
            return c.discover({})
    def test_direct_copy_keeps_actual_source(self):
        a={'root':184,'width':5,'source':129}
        b={'root':230,'source':184,'capture':'(EVar 5 184)'}
        self.assertEqual(self.discover([a],[b]),[{'producer':a,'consumer':b}])
    def test_ambiguous_source_rejected(self):
        a={'root':184,'width':5,'source':129}
        b={'root':230,'source':184,'capture':'(EVar 5 184)'}
        self.assertEqual(self.discover([a,a],[b]),[])
    def test_transformation_is_not_copy(self):
        self.assertEqual(self.discover([{'root':184,'width':5}],[{'root':230,'source':184,'capture':'(EConst 5 0)'}]),[])

if __name__=='__main__':unittest.main()
