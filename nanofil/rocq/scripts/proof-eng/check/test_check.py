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
            print('PASS: comments and reviewed moves accepted; changed proposition, binding, runtime, axiom, and unapproved edits rejected')


if __name__ == '__main__':
    unittest.main()
