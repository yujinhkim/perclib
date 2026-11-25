#!/usr/bin/env python3
import copy
import unittest
from check_proof_pr import check_compiled, check_paths_and_source


def declaration(name, kind='theorem'):
    return dict(name=name, kind=kind, module='PercLib.Example', public=True, universes=0,
                type=['const', 'True', []], value=['const', 'True.intro', []], related=[],
                tag=None, statement_expr=None)


class ProofGateTests(unittest.TestCase):
    def test_theorem_and_root_import(self):
        check_paths_and_source({'PercLib/Proof.lean': 'module\n/- def outer /- opaque -/ -/\n'
            'public import PercLib.Basic\npublic theorem proof : True := by trivial\n',
            'PercLib.lean': 'module\npublic import PercLib.Proof\n'})
        check_compiled({'declarations': []}, {'declarations': [declaration('proof')]})

    def test_interface_paths_and_commands(self):
        for path, text in [('PercLib/Defs.lean', '-- comment only'),
                           ('lakefile.toml', ''), ('PercLib/Proof.lean', 'run_cmd pure ()'),
                           ('PercLib/Proof.lean', 'instance : Inhabited Nat := ⟨0⟩'),
                           ('PercLib.lean', 'theorem p : True := .intro')]:
            with self.assertRaises(ValueError):
                check_paths_and_source({path: text})

    def test_generated_private_definition_rejected(self):
        d = declaration('_private.Generated', 'definition')
        d['public'] = False
        with self.assertRaisesRegex(ValueError, 'non-theorem'):
            check_compiled({'declarations': []}, {'declarations': [d]})

    def test_changed_definition_and_tag(self):
        d = declaration('existing', 'definition')
        other = copy.deepcopy(d)
        other['value'] = ['const', 'False', []]
        with self.assertRaises(ValueError):
            check_compiled({'declarations': [d]}, {'declarations': [other]})
        proof = declaration('proof')
        proof['tag'] = 'A000'
        with self.assertRaisesRegex(ValueError, 'Tagged'):
            check_compiled({'declarations': []}, {'declarations': [proof]})

    def test_literals_cannot_hide_real_commands(self):
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': '"/-"\ndef x := 0'})
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': 'r#"/-"#\ndef x := 0'})
        with self.assertRaises(ValueError):
            check_paths_and_source({'PercLib/Proof.lean': '/- unclosed'})


if __name__ == '__main__':
    unittest.main()
