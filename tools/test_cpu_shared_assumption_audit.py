"""Small real-Coq dependency-union regression; never compiles CPU modules."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
import unittest

import cpu_shared_assumption_audit as audit


def footer(names):
    return ''.join('Print Assumptions '+name+'.\n' for name in names)


class AggregationTests(unittest.TestCase):
    def setUp(self):
        self.prefix='Definition first := I.\nDefinition last := I.\n'
        self.source=self.prefix+footer(['first','last'])

    def test_prefix_and_full_coverage(self):
        generated,meta=audit.aggregate(self.source,['first','last'])
        self.assertTrue(generated.startswith(self.prefix))
        self.assertEqual(meta['covered_exports'],['first','last'])
        self.assertIn('(@first, (@last, tt))',generated)
        self.assertFalse(meta['drops_type_checks'])
        self.assertFalse(meta['drops_kernel_checks'])

    def test_reject_bad_coverage(self):
        for exports in [[],['first'],['first','first'],['last','first'],['first','last','extra']]:
            with self.subTest(exports=exports),self.assertRaises(ValueError):
                audit.aggregate(self.source,exports)

    def test_reject_nonterminal_print(self):
        with self.assertRaises(ValueError):
            audit.aggregate(self.source+'Definition after := I.\n',['first','last'])

    def test_reject_symbol_injection(self):
        for symbol in ['first. Abort','@first','first;last','first\nAxiom evil : False','first..last']:
            with self.subTest(symbol=symbol),self.assertRaises(ValueError):
                audit.aggregate(self.source,[symbol,'last'])

    def test_reject_bundle_collision(self):
        _,meta=audit.aggregate(self.source,['first','last'])
        with self.assertRaises(ValueError):
            audit.aggregate('Definition '+meta['bundle']+' := I.\n'+self.source,['first','last'])


CASES={
    'Closed':('Definition first : True := I.\nDefinition last : True := I.\n',['first','last'],set()),
    'Generic':('Section Generic.\nContext {A : Type}.\nDefinition generic_identity (x : A) : A := x.\nDefinition generic_constant {B : Type} (x : A) (_ : B) : A := x.\nEnd Generic.\n',['generic_identity','generic_constant'],set()),
    'HiddenLast':('Definition first : True := I.\nAxiom HiddenLast : True.\nDefinition hidden_last : True := HiddenLast.\n',['first','hidden_last'],{'HiddenLast'}),
    'Union':('Axiom LeftDependency : True.\nAxiom RightDependency : True.\nDefinition first : True := LeftDependency.\nDefinition last : True := RightDependency.\n',['first','last'],{'LeftDependency','RightDependency'}),
    'TypeOnly':('Axiom HiddenType : Type.\nDefinition typed_identity (x : HiddenType) : HiddenType := x.\n',['typed_identity'],{'HiddenType'}),
    'Qualified':('Module Qualified.\nDefinition value : True := I.\nEnd Qualified.\n',['Qualified.value'],set()),
}


def dependencies(log):
    """Coq's declaration names, not words inside multiline axiom types."""
    return set(re.findall(r'(?m)^([A-Za-z_][A-Za-z0-9_.]*)[ \t]*:',log))-{'Axioms'}


def real_coq(output):
    out=Path(output).resolve();out.mkdir(parents=True,exist_ok=False)
    start=time.monotonic();report={'accepted':False,'budget_seconds':120,'cases':{}}
    try:
        suite=unittest.defaultTestLoader.loadTestsFromTestCase(AggregationTests)
        with (out/'unittest.log').open('w') as stream:
            result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
        if not result.wasSuccessful():raise AssertionError('script rejection tests failed')
        report['script_tests']=result.testsRun
        for name,(prefix,exports,expected) in CASES.items():
            original=prefix+footer(exports);aggregated,meta=audit.aggregate(original,exports)
            row={'expected_dependencies':sorted(expected),'metadata':meta,'runs':{}}
            report['cases'][name]=row
            for kind,source in [('Original',original),('Aggregate',aggregated)]:
                target=out/(name+kind+'.v');target.write_text(source)
                remaining=120-(time.monotonic()-start)
                if remaining<=0:raise TimeoutError('aggregate experiment cumulative budget exhausted')
                begun=time.monotonic()
                run=subprocess.run(['_opam/bin/coqc',str(target)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=remaining)
                (out/(name+kind+'.log')).write_text(run.stdout)
                row['runs'][kind]={'exit':run.returncode,'seconds':time.monotonic()-begun,'dependencies':sorted(dependencies(run.stdout)),
                    'source_sha256':hashlib.sha256(source.encode()).hexdigest()}
                if run.returncode:raise AssertionError(name+kind+' real Coq rejected source')
                row['runs'][kind]['object_sha256']=hashlib.sha256(target.with_suffix('.vo').read_bytes()).hexdigest()
            row['equal_unions']=row['runs']['Original']['dependencies']==row['runs']['Aggregate']['dependencies']
            row['expected_exact']=set(row['runs']['Aggregate']['dependencies'])==expected
            if not row['equal_unions'] or not row['expected_exact']:raise AssertionError(name+' actual dependency union mismatch')
        report['hidden_last_axiom_detected']='HiddenLast' in report['cases']['HiddenLast']['runs']['Aggregate']['dependencies']
        report['type_only_axiom_detected']='HiddenType' in report['cases']['TypeOnly']['runs']['Aggregate']['dependencies']
        report['accepted']=True
    except Exception as error:
        report['error']=str(error)
        raise
    finally:
        report['seconds']=time.monotonic()-start
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--coq-output')
    args,remaining=parser.parse_known_args()
    if args.coq_output:print(json.dumps(real_coq(args.coq_output),indent=2))
    else:unittest.main(argv=[__file__,*remaining])
