#!/usr/bin/env python3
"""Exercise the public check commands against real, disposable Rocq libraries."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent


class Checks(unittest.TestCase):
    def test_abstract_preference_and_restricted_fallback(self):
        with tempfile.TemporaryDirectory(prefix='runtime-selection-') as tmp:
            root = Path(tmp)
            trees = [root / name for name in ('before', 'concrete', 'abstract')]
            source = 'From Nanofil Require Import Runtime. Module R := InterpRuntime. Lemma target : True. Proof. exact I. Qed.\n'
            def compile(tree, text):
                tree.mkdir(exist_ok=True)
                (tree / 'Toy.v').write_text(text)
                subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                                '-R', str(tree), 'Glibc', str(tree / 'Toy.v')], check=True, capture_output=True)
            for tree in trees:
                compile(tree, source)
            compile(trees[2], 'Lemma target : False -> False. Proof. auto. Qed.\n')
            command = ['python3', str(HERE / 'check.py'), 'statements', str(trees[0]), str(trees[1]),
                       '--abstract-after', str(trees[2]), '--plugin', os.environ['PE_CHECK_PLUGIN'],
                       '--expectations', str(root / 'none'), '--output', str(root / 'report')]
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 1)
            (trees[2] / 'Toy.vo').unlink()
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            compile(trees[0], 'Lemma target : True. Proof. exact I. Qed.\n')
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 1)

    def test_statement_binding_runtime_and_axiom_mutations(self):
        plugin = os.environ['PE_CHECK_PLUGIN']
        with tempfile.TemporaryDirectory(prefix='proof-check-test-') as tmp:
            root = Path(tmp)
            before, after = root / 'before', root / 'after'
            before.mkdir()
            after.mkdir()
            def compile(tree, source):
                f = tree / 'Toy.v'
                f.write_text(source)
                subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                                '-R', str(tree), 'Glibc', str(f)], check=True, capture_output=True)
            def compare(expected, manifest=None):
                out = root / 'statements'
                p = subprocess.run(['python3', str(HERE / 'check.py'), 'statements', str(before), str(after),
                                    '--plugin', plugin, '--output', str(out),
                                    '--expectations', str(manifest or root / 'no-exemptions')], capture_output=True, text=True)
                report = json.loads((out / 'report.json').read_text())
                self.assertEqual(report['errors'], [], report)
                self.assertEqual(p.returncode, expected, p.stdout)
                return report
            source = ('Module A. Definition side : Prop := True. End A.\n'
                      'Module B. Definition side : Prop := True. End B.\n'
                      'Import A. Lemma target : side. Proof. exact I. Qed.\n')
            compile(before, source)
            compile(after, '(* Different comments do not change a statement. *)\n' + source)
            compare(0)
            compile(after, source.replace('Import A.', 'Import B.'))
            changed = compare(1)['differences']
            self.assertEqual([d['name'] for d in changed], ['target'])
            self.assertIn('Glibc.Toy.A.side', changed[0]['before']['raw'])
            self.assertIn('Glibc.Toy.B.side', changed[0]['after']['raw'])
            compile(after, source.replace('target : side', 'target : True /\\ True').replace('exact I.', 'split; exact I.'))
            self.assertEqual([d['name'] for d in compare(1)['differences']], ['target'])
            manifest = root / 'approved.txt'
            manifest.write_text('changed\tToy.v\ttarget\n')
            compare(1, manifest)
            subprocess.run(['python3', str(HERE / 'expectations.py'), 'export', str(manifest),
                            str(root / 'statements/report.json')], check=True, capture_output=True)
            self.assertTrue(compare(0, manifest)['differences'][0]['accepted'])
            compile(after, source.replace('target : side', 'target : True /\\ (True /\\ True)').replace('exact I.', 'repeat split; exact I.'))
            self.assertFalse(compare(1, manifest)['differences'][0]['accepted'])
            spec = 'Definition spec (_ : Corelib.Init.Datatypes.nat) : Prop := True.\n'
            compile(before, spec)
            compile(after, spec.replace(':= True', ':= False'))
            self.assertEqual([d['name'] for d in compare(1)['differences']], ['spec'])
            prelude = 'From Nanofil Require Import Runtime.\n'
            compile(before, prelude + 'Module General (R : Runtime).\nLemma target : forall s m, R.ready s m -> R.ready s m.\nProof. auto. Qed. End General.\n')
            compile(after, prelude + 'Module R := InterpRuntime.\nLemma target : forall s m, R.ready s m -> R.ready s m.\nProof. auto. Qed.\n')
            self.assertEqual([d['name'] for d in compare(1)['differences']], ['target'])
            abstract = prelude + 'Declare Module A : Runtime. Declare Module B : Runtime.\nLemma target : forall s m, A.ready s m -> A.ready s m. Proof. auto. Qed.\n'
            compile(before, abstract)
            compile(after, abstract.replace('A.ready', 'B.ready'))
            self.assertEqual([d['name'] for d in compare(1)['differences']], ['target'])
            included = (prelude + 'Module General (R : Runtime). Definition bound : Prop := True. End General.\n'
                        'Module Copy (R : Runtime). Include General R.\n'
                        'Lemma target : bound. Proof. exact I. Qed. End Copy.\n')
            flat = 'Definition bound : Prop := True. Lemma target : bound. Proof. exact I. Qed.\n'
            compile(before, included)
            compile(after, flat)
            compare(0)
            signature_include = (prelude + 'Module General (R : Runtime). Definition bound : Prop := True. End General.\n'
                                 'Module Type Sig (R : Runtime). Include General R. End Sig.\n'
                                 'Module Copy (R : Runtime) (D : Sig R). Lemma target : D.bound. Proof. exact I. Qed. End Copy.\n')
            compile(before, signature_include)
            compare(0)
            opaque_signature = (prelude + 'Module General (R : Runtime). Definition bound : Prop := True. End General.\n'
                                'Module Type Sig (R : Runtime). Parameter bound : Prop. Parameter bound_true : bound. End Sig.\n'
                                'Module Witness (R : Runtime) : Sig R. Include General R. Definition bound_true : bound := I. End Witness.\n'
                                'Module Copy (R : Runtime) (D : Sig R). Lemma target : D.bound. Proof. exact D.bound_true. Qed. End Copy.\n')
            compile(before, opaque_signature)
            self.assertTrue(any(d['name'] == 'target' for d in compare(1)['differences']))
            compile(before, signature_include)
            compile(after, 'Module Other. Definition bound : Prop := True. End Other.\n' +
                    flat.replace('target : bound', 'target : Other.bound'))
            self.assertTrue(any(d['name'] == 'target' for d in compare(1)['differences']))
            sealed = ('Module Type S. Parameter exposed : True. End S.\n'
                      'Module Hidden : S. Lemma target : True. Proof. exact I. Qed.\n'
                      'Definition exposed := target.\nEnd Hidden.\n')
            compile(before, sealed)
            compile(after, sealed)
            compare(0)
            compile(after, sealed.replace('target : True', 'target : True /\\ True')
                    .replace('exact I.', 'split; exact I.').replace('exposed := target', 'exposed := proj1 target'))
            self.assertEqual([d['name'] for d in compare(1)['differences']], ['Hidden.target'])
            signature = 'Module Type S. Section spec. Parameter target : True. End spec. End S.\n'
            compile(before, signature)
            compile(after, signature.replace(': True.', ': True /\\ True.'))
            parameters = root / 'parameters.txt'
            parameters.write_text('changed\tToy.v\tS.target\n')
            self.assertEqual([d['name'] for d in compare(1, parameters)['differences']], ['S.target'])
            proof_alias = ('Module Type S. Parameter exposed : True. End S.\n'
                           'Module Hidden : S. Definition exposed : True := I. End Hidden.\n')
            compile(before, proof_alias)
            compile(after, proof_alias.replace(': True', ': True /\\ True').replace(':= I', ':= conj I I'))
            aliases = root / 'aliases.txt'
            aliases.write_text('changed\tToy.v\tHidden.exposed\n')
            changes = compare(1, aliases)['differences']
            self.assertEqual([d['name'] for d in changes], ['Hidden.exposed'])
            self.assertNotIn('conj', changes[0]['after']['raw'])
            layout = root / 'layout'
            layout.mkdir()
            (layout / 'toy.v').write_text('From Glibc Require Import Toy.\nPrint Assumptions target.\n')
            contracts = root / 'contracts.json'
            contracts.write_text(json.dumps({'toy': {'target': []}}))
            def audit(expected):
                p = subprocess.run(['python3', str(HERE / 'audit.py'), str(after), '--layout', str(layout),
                                    '--contracts', str(contracts), '--output', str(root / 'audit')],
                                   capture_output=True, text=True)
                self.assertEqual(p.returncode, expected, p.stdout + p.stderr)
                return json.loads((root / 'audit/report.json').read_text())
            compile(after, 'Lemma target : True. Proof. exact I. Qed.\n')
            baseline = root / 'audit-before.json'
            baseline.write_text(json.dumps(audit(0)))
            audit_compare = ['python3', str(HERE / 'compare-audits.py'), str(baseline), str(root / 'audit/report.json')]
            self.assertEqual(subprocess.run(audit_compare, capture_output=True).returncode, 0)
            compile(after, 'Lemma target : True /\\ True. Proof. split; exact I. Qed.\n')
            audit(0)
            self.assertEqual(subprocess.run(audit_compare, capture_output=True).returncode, 1)
            compile(after, 'Axiom planted : True.\nLemma target : True. Proof. exact planted. Qed.\n')
            self.assertEqual(audit(1)['toy']['targets']['target']['assumptions'], ['planted'])
            compile(before, 'Lemma target : True. Proof. exact I. Qed.\n')
            compile(after, 'Lemma target : True. Proof. exact I. Qed.\n')
            (after / 'Toy.v').rename(after / 'Renamed.v')
            subprocess.run(['rocq', 'c', '-q', '-R', str(after), 'Glibc', str(after / 'Renamed.v')], check=True)
            moves = root / 'moves.txt'
            moves.write_text('moved\tToy.v\ttarget\tRenamed.v\ttarget\n')
            self.assertTrue(compare(0, moves)['differences'][0]['accepted'])
            # Both reviewed sources must equal the destination, including
            # the universe that moves with a polymorphic declaration.
            polymorphic = 'Lemma target (A : Type) (x : A) : x = x. Proof. reflexivity. Qed.\n'
            compile(before, polymorphic)
            for tree, name in [(before, 'Other'), (after, 'Renamed')]:
                path = tree / (name + '.v')
                path.write_text(polymorphic)
                subprocess.run(['rocq', 'c', '-q', '-R', str(tree), 'Glibc', str(path)], check=True)
            moves.write_text(moves.read_text() + 'moved\tOther.v\ttarget\tRenamed.v\ttarget\n')
            self.assertEqual(len(compare(0, moves)['differences'][0]['origins']), 2)
            moves.write_text('moved\tToy.v\ttarget\tRenamed.v\ttarget\n')
            self.assertTrue(any(not d['accepted'] for d in compare(1, moves)['differences']))
            moves.write_text(moves.read_text() + 'moved\tOther.v\ttarget\tRenamed.v\ttarget\n')
            (before / 'Other.v').write_text('Lemma target (A : Type) (x : A) : True. Proof. exact I. Qed.\n')
            subprocess.run(['rocq', 'c', '-q', '-R', str(before), 'Glibc', str(before / 'Other.v')], check=True)
            failed = subprocess.run(['python3', str(HERE / 'check.py'), 'statements', str(before), str(after),
                                     '--plugin', plugin, '--output', str(root / 'bad-merge'),
                                     '--expectations', str(moves)], capture_output=True, text=True)
            self.assertEqual(failed.returncode, 1)
            self.assertTrue(json.loads((root / 'bad-merge/report.json').read_text())['errors'])
            print('PASS: comments and reviewed moves accepted; changed proposition, binding, runtime, axiom, and unapproved edits rejected')


if __name__ == '__main__':
    unittest.main()
