import json
from pathlib import Path
import tempfile
import unittest
from cpu_proof_bundle import plan, external_providers, build, checked_loadpaths, uses_namespace

def stage(name,needs=()):
    return dict(id=name,namespace='NS'+name,needs=list(needs))

class BundleTests(unittest.TestCase):
    def test_selected_node_builds_its_dependencies_only(self):
        m=dict(stages=[stage('a'),stage('b',['a']),stage('unused')])
        self.assertEqual([s['id'] for s in plan(m,['b'])],['a','b'])

    def test_bad_graphs_fail_before_building(self):
        for stages in [[stage('a'),stage('a')],[stage('a',['missing'])],
                       [stage('a',['b']),stage('b',['a'])],
                       [stage('a'),stage('a-source')]]:
            with self.assertRaises(ValueError):plan(dict(stages=stages))

    def test_old_built_providers_cannot_shadow_fresh_nodes(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp)/'providers.json'
            p.write_text(json.dumps([dict(namespace=n,directory='/tmp/old') for n in ['NSa','Forbidden','External']]))
            result=external_providers(dict(providers=str(p)),dict(stages=[stage('a')],forbidden_namespaces=['Forbidden']))
            self.assertEqual(result,{'External':'/tmp/old'})

    def test_generation_alone_is_never_a_proof_pass(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp);source=p/'Sample.v';source.write_text('Theorem sample : True. Proof. exact I. Qed.\nPrint Assumptions sample.\n')
            s=stage('a');s.update(kind='source',source=str(source),origin='test_fixture')
            result=build(dict(stages=[s]),'fixture',p/'out',1,generate_only=True)
            self.assertTrue(result['complete']);self.assertFalse(result['accepted'])
            self.assertEqual(result['results'][0]['status'],'generated_not_checked')

    def test_both_coq_import_forms_are_checked(self):
        self.assertTrue(uses_namespace('Require Import Legacy.Old.', 'Legacy'))
        self.assertTrue(uses_namespace('From Legacy Require Import Old.', 'Legacy'))
        self.assertFalse(uses_namespace('From LegacyExtra Require Import Old.', 'Legacy'))

    def test_explicit_loadpath_cannot_restore_forbidden_or_stale_namespace(self):
        m=dict(stages=[stage('a')],forbidden_namespaces=['Legacy'])
        for ns in ['Legacy','NSa','External']:
            with self.assertRaises(ValueError):
                checked_loadpaths(dict(loadpaths=[dict(namespace=ns,directory='/tmp/stale')]),m,{'External':'/tmp/real'})

    def test_forbidden_import_blocks_downstream(self):
        with tempfile.TemporaryDirectory() as temp:
            p=Path(temp);source=p/'Sample.v';source.write_text('Require Import Legacy.OldProof.\n')
            a=stage('a');a.update(kind='source',source=str(source),origin='test_fixture')
            b=stage('b',['a']);b.update(kind='source',source=str(source),origin='test_fixture')
            result=build(dict(stages=[a,b],forbidden_namespaces=['Legacy']),'fixture',p/'out',1,generate_only=True)
            self.assertFalse(result['complete'])
            self.assertEqual([r['status'] for r in result['results']],['failed','blocked'])

if __name__=='__main__':unittest.main()
