import json
import subprocess
import tempfile
import unittest
from pathlib import Path
import cpu_instruction_scope as scopes
import cpu_isa_input_certificate as certificate


class InstructionScopes(unittest.TestCase):
    def test_exact_catalog_domains(self):
        catalog=json.loads((scopes.ROOT/'framework/pending-rtl-inputs.json').read_text())
        for row in catalog['designs']:
            self.assertEqual(scopes.for_input(row['ast'],row['ast_module']),
                'pico29' if row['name']=='picorv32' else 'rv32i38')
        self.assertEqual(scopes.for_input('a_new_picorv32.v','NewDesign'),'rv32i38')

    def test_unknown_scope_is_rejected(self):
        with self.assertRaises(ValueError):scopes.select({},'silent_subset')

    def test_pico_manifest_and_native_exclusion(self):
        original=(scopes.ROOT/'dep/riscv-coq/src/riscv/Spec/ExecuteI.v').read_text()
        plan,source=certificate.render(original,'pico29')
        self.assertEqual(len(plan['instructions']),29)
        self.assertEqual({r['instruction']for r in plan['excluded_instructions']},scopes.PICO_EXCLUDED)
        self.assertTrue(all(r['status']=='out_of_scope'for r in plan['excluded_instructions']))
        supported=source.split('Definition requested_instruction',1)[1].split('end.',1)[0]
        for name in scopes.PICO_EXCLUDED:
            self.assertNotIn('Decode.'+name+' ',supported)
        suffix='''
Example pico_add_allowed:requested_instruction(Decode.Add 1 2 3)=true.
Proof. reflexivity. Qed.
Example pico_load_excluded:requested_instruction(Decode.Lw 1 2 0)=false.
Proof. reflexivity. Qed.
Example pico_store_excluded:requested_instruction(Decode.Sw 1 2 0)=false.
Proof. reflexivity. Qed.
Example pico_fence_i_excluded:requested_instruction Decode.Fence_i=false.
Proof. reflexivity. Qed.
'''
        with tempfile.TemporaryDirectory()as folder:
            for name,text,good in [('Scope',source+suffix,True),
                    ('WrongScope',source+'\nExample bad:requested_instruction(Decode.Lw 1 2 0)=true. Proof. reflexivity. Qed.\n',False)]:
                path=Path(folder)/(name+'.v');path.write_text(text)
                result=subprocess.run([str(scopes.ROOT/'_opam/bin/coqc'),
                    *certificate.synthesis.origin.pending.rtl.framework.FLAGS,str(path)],
                    cwd=scopes.ROOT,capture_output=True,text=True,timeout=120)
                self.assertEqual(result.returncode==0,good,result.stderr)
                self.assertEqual(path.with_suffix('.vo').exists(),good)
                if not good:self.assertIn('Unable to unify',result.stderr)


if __name__=='__main__':unittest.main()
