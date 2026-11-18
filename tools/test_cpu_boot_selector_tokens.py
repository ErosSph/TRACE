import unittest
import cpu_boot_selector_tokens as c

class Tests(unittest.TestCase):
    def data(self):
        return dict(sources=[
          dict(selector=5,input=10,width=5,terminal=20,edges=[{}]),
          dict(selector=5,input=11,width=1,terminal=21,edges=[{}])]),[dict(rd=20,write=21,valid=22)]
    def test_matches_joint_stage_not_signal_name(self):
        p,s=self.data();r=c.discover(p,s)
        self.assertEqual([(x['rd'],x['write'],x['stage'])for x in r],[(10,11,0)])
    def test_other_stage_enable_not_accepted(self):
        p,s=self.data();p['sources'][1]['terminal']=30
        self.assertEqual(c.discover(p,s),[])
    def test_other_selector_enable_not_accepted(self):
        p,s=self.data();p['sources'][1]['selector']=6
        self.assertEqual(c.discover(p,s),[])
    def test_ambiguous_enable_not_accepted(self):
        p,s=self.data();p['sources'].append(dict(p['sources'][1],input=12))
        self.assertEqual(c.discover(p,s),[])
    def test_ambiguous_destination_not_accepted(self):
        p,s=self.data();s.append(dict(s[0]))
        self.assertEqual(c.discover(p,s),[])
    def test_duplicate_use_same_pair_is_shared(self):
        p,s=self.data();p['sources'] += [dict(r,selector=6)for r in p['sources']]
        self.assertEqual(len(c.discover(p,s)),1)

if __name__=='__main__':unittest.main()
