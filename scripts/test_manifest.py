#!/usr/bin/env python3
"""Compiled integration tests: run after lake build, using its toolchain/environment."""
import copy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from build_manifest import build, fingerprint, frontier, definition_index

ROOT = Path(__file__).resolve().parent.parent
CATALOG = {t: {} for t in ('A000', 'B000', 'C000', 'D000', 'E000', 'F000')}
CONTEXT = {'lean': 'test-pin'}


def run(*args, env=None):
    try:
        return subprocess.check_output(args, cwd=ROOT, env=env, text=True, stderr=subprocess.STDOUT)
    except subprocess.CalledProcessError as e:
        raise RuntimeError(e.output) from e


def fixture(directory, renamed=False, changed=False, duplicate=False, malformed=False, opaque=False, alias=False, opaque_alias=False, extra_source=''):
    a = directory / 'ManifestFixture'
    a.mkdir(exist_ok=True)
    name = 'renamed' if renamed else 'predicate'
    rhs = 'n = n' if not changed else 'n + 0 = n'
    (a / 'A.lean').write_text(f'''module
public import PercLib.Meta.Tag
public section
namespace Example
@[tag "A000"] def {name} (n : Nat) : Prop := {rhs}
@[tag "A000"] theorem witness (n : Nat) : {name} n := by simp [{name}]
@[tag "B000"] theorem base : True := True.intro
private theorem helperOne : True := base
private theorem helperTwo : True := helperOne
@[tag "C000"] theorem viaHelpers : True := helperTwo
structure LiteratureInput : Prop where
  evidence : True
@[tag "D000"] theorem conditional (_h : LiteratureInput) : True := base
@[tag "E000"] def waiting : Prop := True
end Example
''')
    (a / 'B.lean').write_text('''module
public import ManifestFixture.A
public section
namespace Example
@[tag "F000"] theorem both (h : predicate 0) : predicate 0 := by
  have _ := witness 0
  exact h
end Example
'''.replace('predicate', name))
    if extra_source:
        with (a / 'B.lean').open('a') as out:
            out.write('\n' + extra_source + '\n')
    if duplicate:
        with (a / 'B.lean').open('a') as out:
            out.write('\n@[tag "B000"] theorem duplicate : True := True.intro\n')
    if alias or opaque_alias:
        with (a / 'B.lean').open('a') as out:
            out.write('\nabbrev Proposition := Prop\n')
            kind = 'opaque' if opaque_alias else 'def'
            out.write(f'@[tag "G000"] {kind} pendingAlias : Proposition := False\n')
            if alias:
                out.write('@[tag "H000"] def etaTarget : Nat → Proposition := Example.predicate\n')
    if opaque:
        with (a / 'B.lean').open('a') as out:
            out.write('\n@[tag "G000"] opaque pending : Prop := False\n')
    if malformed:
        with (a / 'B.lean').open('a') as out:
            out.write('\n@[tag "bad"] theorem malformed : True := True.intro\n')
    (directory / 'ManifestFixture.lean').write_text('module\npublic import ManifestFixture.B\n')
    env = dict(os.environ, LEAN_PATH=str(directory) + ':' + os.environ.get('LEAN_PATH', ''))
    # lake env supplies package paths while preserving our fixture path.
    for mod in ('ManifestFixture/A', 'ManifestFixture/B', 'ManifestFixture'):
        run('lake', 'env', 'lean', '-R', str(directory), str(directory / (mod + '.lean')),
            '-o', str(directory / (mod + '.olean')), env=env)
    return json.loads(run('lake', 'env', 'lean', '--run', 'scripts/ExtractManifest.lean',
                          'ManifestFixture', env=env))


class ManifestTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory(prefix='perclib-manifest-')
        cls.directory = Path(cls.tmp.name)
        cls.raw = fixture(cls.directory)
        cls.result = build(cls.raw, CATALOG, CONTEXT)
        cls.entries = {x['tag']: x for x in cls.result['assertions']}

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def test_imports_pair_and_source_location(self):
        entry = self.entries['A000']
        self.assertEqual(entry['proof_status'], 'proved')
        self.assertEqual(len(entry['declarations']), 2)
        self.assertTrue(all(x['line'] and x['file'].endswith('/A.lean') for x in entry['declarations']))
        self.assertNotEqual(entry['statement'], 'Prop')

    def test_helpers_and_axes(self):
        self.assertEqual(self.entries['C000']['dependencies']['proof'], ['B000'])
        self.assertEqual(self.entries['F000']['dependencies'], {'statement': ['A000'], 'proof': ['A000']})

    def test_input_and_statement_status(self):
        self.assertEqual(self.entries['D000']['proof_status'], 'proved-modulo')
        self.assertEqual(self.entries['D000']['inputs'], ['Example.LiteratureInput'])
        self.assertEqual(self.entries['E000']['proof_status'], 'statement-only')
        self.assertEqual(self.entries['E000']['dependencies']['proof'], [])

    def test_unsupported_tag_kinds_fail_closed(self):
        cases = [
            ('inductive', '@[tag "G000"] inductive Pending : Prop'),
            ('inductive', '@[tag "G000"] inductive Pending : Prop where\n  | intro : Pending'),
            ('constructor', 'inductive Pending : Prop where\n  | intro : Pending\nattribute [tag "G000"] Pending.intro'),
            ('recursor', 'inductive Pending : Prop where\n  | intro : Pending\nattribute [tag "G000"] Pending.rec'),
        ]
        for kind, source in cases:
            with self.subTest(kind=kind, source=source):
                raw = fixture(self.directory, extra_source=source)
                tagged = next(d for d in raw['declarations'] if d['tag'] == 'G000')
                self.assertEqual(tagged['kind'], kind)
                with self.assertRaisesRegex(ValueError, 'Unsupported tagged declaration kind'):
                    build(raw, {**CATALOG, 'G000': {}}, CONTEXT)

    def test_supported_tag_kind_boundary(self):
        raw = fixture(self.directory, extra_source='''
@[tag "G000"] def dataDefinition : Nat := 1
@[tag "H000"] opaque dataOpaque : Nat := 1
@[tag "I000"] theorem actualProof : True := True.intro
''')
        entries = {e['tag']: e for e in build(raw,
            {**CATALOG, 'G000': {}, 'H000': {}, 'I000': {}}, CONTEXT)['assertions']}
        for tag in ('G000', 'H000', 'I000'):
            self.assertEqual(entries[tag]['proof_status'], 'proved')
        self.assertEqual(entries['E000']['proof_status'], 'statement-only')

    def test_rename_and_definition_change(self):
        renamed = build(fixture(self.directory, renamed=True), CATALOG, CONTEXT)
        changed = build(fixture(self.directory, changed=True), CATALOG, CONTEXT)
        before = {e['tag']: e['fingerprint'] for e in self.result['assertions']}
        after = {e['tag']: e['fingerprint'] for e in renamed['assertions']}
        self.assertEqual(before, after)
        # F000's text still references predicate; changing its body invalidates the review.
        self.assertNotEqual(before['F000'], changed['assertions'][-1]['fingerprint'])

    def test_missing_and_withdrawn_tags(self):
        for catalog in ({}, {k: v for k, v in CATALOG.items() if k != 'A000'}):
            with self.assertRaisesRegex(ValueError, 'Unknown, withdrawn or absent'):
                build(self.raw, catalog, CONTEXT)

    def test_incompatible_duplicate(self):
        raw = copy.deepcopy(self.raw)
        next(d for d in raw['declarations'] if d['name'] == 'Example.base')['tag'] = 'A000'
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            build(raw, CATALOG, CONTEXT)

    def test_unavailable_body_and_axioms(self):
        raw = copy.deepcopy(self.raw)
        target = next(d for d in raw['declarations'] if d['name'] == 'Example.base')
        self.assertEqual(target['proof_constants'], ['True.intro'])
        self.assertNotIn('value', target)
        target['proof_constants'] = None
        with self.assertRaisesRegex(ValueError, 'Missing body'):
            build(raw, CATALOG, CONTEXT)
        target['proof_constants'] = ['True.intro']
        target['axioms'] = ['unexpectedAxiom']
        with self.assertRaisesRegex(ValueError, 'Forbidden axioms'):
            build(raw, CATALOG, CONTEXT)

    def test_order_independence(self):
        raw = copy.deepcopy(self.raw)
        raw['declarations'].reverse()
        self.assertEqual(build(raw, CATALOG, CONTEXT), self.result)

    def test_cross_module_duplicate(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            build(fixture(self.directory, duplicate=True), CATALOG, CONTEXT)

    def test_prop_alias_and_eta_statement(self):
        result = build(fixture(self.directory, alias=True),
                       {**CATALOG, 'G000': {}, 'H000': {}}, CONTEXT)
        entries = {e['tag']: e for e in result['assertions']}
        self.assertEqual(entries['G000']['proof_status'], 'statement-only')
        self.assertEqual(entries['G000']['statement'], 'False')
        self.assertEqual(entries['H000']['proof_status'], 'statement-only')
        self.assertEqual(entries['H000']['dependencies']['statement'], ['A000'])
        self.assertIn('∀', entries['H000']['statement'])
        with self.assertRaisesRegex(ValueError, 'Opaque proposition'):
            build(fixture(self.directory, opaque_alias=True), {**CATALOG, 'G000': {}}, CONTEXT)

    def test_opaque_proposition_is_not_a_proof(self):
        with self.assertRaisesRegex(ValueError, 'Opaque proposition'):
            build(fixture(self.directory, opaque=True), {**CATALOG, 'G000': {}}, CONTEXT)

    def test_malformed_attribute(self):
        with self.assertRaisesRegex(RuntimeError, 'four characters'):
            fixture(self.directory, malformed=True)

    def test_cycle_and_definition_body(self):
        # Graph-level regression for mutual recursion; compiled declarations above exercise
        # the actual expression serialization and imported private helper traversal.
        ds = {n: {'kind': 'definition', 'universes': 0,
                  'type': ['sort', ['zero']], 'value': ['const', other, []], 'related': []}
              for n, other in [('a', 'b'), ('b', 'a')]}
        first = fingerprint(['const', 'a', []], ds, CONTEXT)
        self.assertEqual(frontier(['a'], ds, {}, 'NONE'), [])
        ds['b']['value'] = ['const', 'True', []]
        self.assertNotEqual(first, fingerprint(['const', 'a', []], ds, CONTEXT))

    def test_public_definition_index(self):
        ds = {d['name']: d for d in definition_index(self.raw, CONTEXT)['definitions']}
        self.assertIn('Example.predicate', ds)
        self.assertIn('Example.LiteratureInput', ds)
        self.assertIn('Example.waiting', ds)
        self.assertNotIn('Example.witness', ds)
        self.assertFalse(any('helper' in n for n in ds))
        self.assertTrue(all(d['type'] for d in ds.values()))
        self.assertTrue(ds['Example.predicate']['line'])

    def test_unformalised(self):
        result = build(self.raw, {**CATALOG, 'Z000': {}}, CONTEXT)
        self.assertEqual(result['assertions'][-1]['proof_status'], 'unformalised')


if __name__ == '__main__':
    unittest.main()
