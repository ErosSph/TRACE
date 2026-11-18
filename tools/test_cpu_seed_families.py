import copy
import json
from pathlib import Path
import unittest
import cpu_seed_families as F

ROOT=Path(__file__).resolve().parents[1]/'framework/seed-families-20261106'

class FamilyTests(unittest.TestCase):
    def schema(self,name='nerv-outcome'):
        d=ROOT/name
        return json.loads((d/'schema.json').read_text()),d

    def test_complete_partitions_and_honest_provenance(self):
        total=seeds=0
        for d in ROOT.iterdir():
            if not d.is_dir():continue
            c,d=self.schema(d.name);text,ledger=F.render(c,d)
            self.assertEqual(len(ledger),8 if 'misalignment' in d.name else 29)
            self.assertEqual(len({r['theorem'] for r in ledger}),len(ledger))
            self.assertFalse(any(r['narrow_llm_written'] for r in ledger))
            self.assertNotRegex(text,r'@[A-Z_]+@')
            total+=len(ledger);seeds+=sum(r['origin']=='adapted_seed' for r in ledger)
        self.assertEqual((total,seeds),(124,34))

    def test_missing_and_duplicate_classes_fail(self):
        c,d=self.schema()
        for mutate in [lambda x:x['families'][0]['classes'].pop(),
                       lambda x:x['families'][0]['classes'].append(x['families'][0]['classes'][0])]:
            bad=copy.deepcopy(c);mutate(bad)
            with self.assertRaises(ValueError):F.render(bad,d)

    def test_roles_cannot_inject_proofs_or_change_isa_slots(self):
        c,d=self.schema()
        for roles in [{'ROLE_BAD':'exact I. Qed.'},{'BINOP':'BSub'},{'ROLE_BAD':True}]:
            bad=copy.deepcopy(c);bad['roles']['Add']=roles
            with self.assertRaises(ValueError):F.render(bad,d)

    def test_signed_and_unsigned_class_parameters(self):
        self.assertEqual(F.parameters('Srai')['FUNCT_SEVEN'],'32')
        self.assertEqual(F.parameters('Srli')['FUNCT_SEVEN'],'0')
        self.assertEqual(F.parameters('Sltiu')['COND_SHAPE'],'SLTU')
        self.assertEqual(F.parameters('Bge')['COND_SHAPE'],'GE')
        self.assertEqual(F.parameters('Bgeu')['COND_SHAPE'],'GEU')

    def test_fresh_narrow_authorship_is_only_the_seed(self):
        c,d=self.schema();c['families'][0]['origin']='llm_written'
        c['families'][0]['proof_author']='OpenAI Codex'
        _,ledger=F.render(c,d)
        self.assertEqual(sum(r['narrow_llm_written'] for r in ledger),1)
        c['families'][0]['origin']='unknown'
        with self.assertRaises(ValueError):F.render(c,d)

if __name__=='__main__':unittest.main()
