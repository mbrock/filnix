#!/usr/bin/env python3
"""Exercise the public check commands against real, disposable Rocq libraries."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import copy

from audit_changes import receipt, reference, tree_digest

HERE = Path(__file__).resolve().parent


class Checks(unittest.TestCase):
    def test_discovery_does_not_accept_changes_or_hide_probe_errors(self):
        with tempfile.TemporaryDirectory(prefix='discovery-') as tmp:
            root = Path(tmp)
            before, after = root / 'before', root / 'after'
            source = 'Definition unchanged : nat := 0. Lemma target : True. Proof. auto. Qed.\n'
            def compile(tree, text):
                tree.mkdir(exist_ok=True)
                path = tree / 'Toy.v'
                path.write_text(text)
                subprocess.run(['rocq', 'c', '-q', '-R', str(tree), 'Glibc', str(path)],
                               check=True, capture_output=True)
            compile(before, source)
            compile(after, source)
            manifest = root / 'candidates.txt'
            manifest.write_text('changed\tToy.v\ttarget\nchanged\tToy.v\tunchanged\n')
            command = ['python3', str(HERE / 'check.py'), 'statements', str(before), str(after),
                       '--plugin', os.environ['PE_CHECK_PLUGIN'], '--expectations', str(manifest),
                       '--output', str(root / 'report')]
            def run(discovery):
                result = subprocess.run(command + (['--discovery'] if discovery else []), capture_output=True)
                return result.returncode, json.loads((root / 'report/report.json').read_text())
            code, report = run(False)
            self.assertEqual(code, 1)
            self.assertEqual(len(report['errors']), 2)
            code, report = run(True)
            self.assertEqual((code, report['errors'], report['differences']), (0, [], []))
            compile(after, source.replace('target : True', 'target : False -> False'))
            code, report = run(True)
            self.assertEqual((code, report['errors']), (1, []))
            self.assertEqual([d['name'] for d in report['differences']], ['target'])
            d = report['differences'][0]
            manifest.with_suffix('.elaborated.json').write_text(json.dumps({'version': 1, 'changes': [
                {k: d[k] for k in ('kind', 'file', 'name')} |
                {s: d[s]['normalized'] for s in ('before', 'after')}]}))
            code, report = run(True)
            self.assertEqual(code, 1)
            self.assertFalse(report['differences'][0]['accepted'])
            (after / 'Toy.vo').unlink()
            code, report = run(True)
            self.assertEqual(code, 1)
            self.assertTrue(report['errors'])

    def test_reviewed_audit_permissions(self):
        # Exercise the comparison's report interface. Adapter compilation is
        # the stage's responsibility; these fixtures model its checked output.
        with tempfile.TemporaryDirectory(prefix='audit-permissions-') as tmp:
            root = Path(tmp)
            tree = root / 'tree'
            tree.mkdir()
            (tree / 'Toy.v').write_text('Lemma rule : True. Proof. exact I. Qed.\n')
            key = ('getopt/GetoptLongArg.v', 'wp_long_found')
            manifest = root / '50-program.txt'
            manifest.write_text('changed\t' + '\t'.join(key) + '\n# equivalence\t' +
                                '\t'.join(key) + '\tforward\treverse\n')
            manifest.with_suffix('.equivalence.v').write_text(
                'Lemma forward : (forall n : nat, True) -> True. Proof. auto. Qed.\n'
                'Lemma reverse : True -> (forall n : nat, True). Proof. auto. Qed.\n')
            manifest.with_suffix('.elaborated.json').write_text(json.dumps({'version': 1, 'changes': [
                {'file': key[0], 'name': key[1], 'kind': 'changed', 'before': 'old type', 'after': 'new type'}]}))
            checked = {'file': key[0], 'name': key[1], 'adapters': ['forward', 'reverse'],
                       'before': {}, 'after': {}, 'directions': [{}, {}]}
            concrete = receipt(tree, manifest, {'runtime': 'concrete', 'pairs': [checked]})
            fields = {'Glibc.Fix.R.state': 'Type'}
            abstract_checked = checked | {'before': fields, 'after': fields, 'directions': [fields, {}]}
            abstract = receipt(tree, manifest, {'runtime': 'abstract', 'pairs': [abstract_checked]})
            paths = [root / f'{name}.json' for name in ('before', 'after', 'concrete', 'abstract')]
            def run(expected, receipts, declaration=reference(key), assumption_types=None):
                target = {'pass': True, 'qualified': True, 'types': {}, 'raw': 'Closed under the global context',
                          'declaration': declaration}
                for path, statement in zip(paths[:2], ('old type', 'new type')):
                    entry = target | {'normalized_statement': statement}
                    if path == paths[1] and assumption_types is not None:
                        entry['types'] = assumption_types
                    path.write_text(json.dumps({'test': {'pass': True, 'tree_sha256': tree_digest(tree),
                                                         'targets': {key[1]: entry}}}))
                command = ['python3', str(HERE / 'compare-audits.py'), *map(str, paths[:2])]
                for path, data in zip(paths[2:], receipts):
                    path.write_text(json.dumps(data))
                    command += ['--stage50-evidence', str(path)]
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
            run(0, [concrete])
            # An unlisted file cannot borrow a listed declaration's bare name.
            run(1, [concrete], 'Glibc.other.GetoptLongArg.wp_long_found')
            run(1, [], reference(key))
            run(1, [concrete], assumption_types={'new_axiom': 'True'})
            run(1, [abstract])  # Abstract evidence also requires Closed interpreter adapters.
            run(0, [concrete, abstract])
            # Distinguish runtimes by source identity so the concrete receipt
            # cannot mask a rejected abstract receipt in the following cases.
            other_source = copy.deepcopy(concrete)
            other_source['tree_sha256'] = 'different concrete tree'
            run(0, [other_source, abstract])
            for label, mutation in (
                ('outside Fix.R', lambda e: e['directions'][0].update({'External.axiom': 'True'})),
                ('unlisted Fix.R field', lambda e: e['directions'][0].update({'Glibc.Fix.R.alloc': 'Type'})),
                ('changed field type', lambda e: e['directions'][0].update({'Glibc.Fix.R.state': 'Prop'})),
                ('unequal statement assumptions', lambda e: e['after'].update({'Glibc.Fix.R.alloc': 'Type'})),
            ):
                with self.subTest(label=label):
                    bad = copy.deepcopy(abstract)
                    # JSON roundtrip separates shared dicts in the fixture.
                    bad = json.loads(json.dumps(bad))
                    mutation(bad['declarations'][0]['assumptions'])
                    bad['validated_pairs'][0] = bad['declarations'][0]['assumptions']
                    run(1, [other_source, bad])
            bad = copy.deepcopy(concrete)
            bad['declarations'][0]['assumptions']['directions'][1] = {'Glibc.Fix.R.state': 'Type'}
            run(1, [bad])  # Interpreter evidence must be Closed, even for runtime fields.

    def test_tactics_packet_checks_whole_boundary(self):
        with tempfile.TemporaryDirectory(prefix='tactics-packet-') as tmp:
            root = Path(tmp)
            before, after, manifests = [root / n for n in ('before', 'after', 'manifests')]
            for path in (before, after, manifests):
                path.mkdir()
            def compile(tree, name, source):
                path = tree / (name + '.v')
                path.write_text(source)
                subprocess.run(['rocq', 'c', '-q', '-R', str(tree), 'Glibc', str(path)],
                               check=True, capture_output=True)
            base = 'Lemma target : True. Proof. exact I. Qed.\n'
            rule = 'Lemma step_named_rule : True. Proof. exact I. Qed.\n'
            for tree in (before, after):
                compile(tree, 'Toy', base)
            compile(after, 'GlibcTactics', rule)
            manifest = manifests / '30-tactics.txt'
            manifest.write_text('added\tGlibcTactics.v\tstep_named_rule\n')
            subprocess.run(['python3', str(HERE / 'check.py'), 'statements', str(before), str(after),
                            '--plugin', os.environ['PE_CHECK_PLUGIN'], '--expectations', str(manifest),
                            '--output', str(root / 'capture')], capture_output=True)
            subprocess.run(['python3', str(HERE / 'expectations.py'), 'export', str(manifest),
                            str(root / 'capture/report.json')], check=True, capture_output=True)
            command = ['python3', str(HERE / 'packet.py'), str(after), '--manifests', str(manifests),
                       '--stage30-before', str(before), '--stage30-after', str(after),
                       '--plugin', os.environ['PE_CHECK_PLUGIN'], '--output', str(root / 'packet.md')]
            def packet(expected):
                result = subprocess.run(command, capture_output=True, text=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
            packet(0)
            compile(after, 'Toy', 'Lemma target : False -> False. Proof. auto. Qed.\n')
            packet(1)
            compile(after, 'Toy', base)
            compile(after, 'GlibcTactics', 'Axiom planted : True.\n' + rule.replace('exact I', 'exact planted'))
            packet(1)
            compile(after, 'GlibcTactics', rule)
            compile(after, 'Toy', base + ''.join(f'Ltac extra{i} := idtac.\n' for i in range(227)))
            packet(1)

    def test_original_runtime_partition(self):
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
            compile(trees[0], 'Lemma target : True. Proof. exact I. Qed.\n')
            compile(trees[2], 'Lemma target : False -> False. Proof. auto. Qed.\n')
            command = ['python3', str(HERE / 'check.py'), 'statements', str(trees[0]), str(trees[1]),
                       '--abstract-after', str(trees[2]), '--plugin', os.environ['PE_CHECK_PLUGIN'],
                       '--expectations', str(root / 'none'), '--output', str(root / 'report')]
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 1)
            logic = 'From Nanofil Require Import Runtime Logic.\n'
            statement = 'Lemma target : forall x y, LG.L.P.program_genv x y = LG.L.P.program_genv x y. Proof. reflexivity. Qed.\n'
            compile(trees[0], logic + 'Module General (R : Runtime). Module LG := Logic R.\n' +
                    statement + 'End General. Module Concrete := General InterpRuntime.\n')
            compile(trees[1], logic + 'Module LG := Logic InterpRuntime.\n' + statement)
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            compile(trees[0], logic + 'Module General (R : Runtime) (LG : LogicSig R).\n' +
                    statement + 'End General. Module ConcreteLogic := Logic InterpRuntime.\n'
                    'Module Concrete := General InterpRuntime ConcreteLogic.\n')
            compile(trees[1], logic + 'Module R := InterpRuntime. Module General (LG : LogicSig R).\n' +
                    statement + 'End General.\n')
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            compile(trees[1], source)
            compile(trees[0], source)
            for tree in trees[:2]:
                path = tree / 'Bridge.v'
                path.write_text('From Glibc Require Import Toy. Lemma bridge_target : True. Proof. exact I. Qed.\n')
                subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                                '-R', str(tree), 'Glibc', str(path)], check=True, capture_output=True)
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            report = json.loads((root / 'report/report.json').read_text())
            self.assertEqual(report['runtime_partition']['concrete'], ['Bridge.v', 'Toy.v'])
            partition_command = ['python3', str(HERE / 'check.py'), 'partition', str(trees[0]),
                                 '--output', str(root / 'partition')]
            subprocess.run(partition_command, check=True, capture_output=True)
            self.assertEqual(json.loads((root / 'partition/report.json').read_text()),
                             {'roots': ['Toy.v'], 'concrete': ['Bridge.v', 'Toy.v'], 'general': []})
            self.assertEqual((root / 'partition/general-targets.txt').read_text(), '')
            (trees[2] / 'Toy.vo').unlink()
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
            compile(trees[0], 'Lemma target : True. Proof. exact I. Qed.\n')
            self.assertEqual(subprocess.run(command, capture_output=True).returncode, 1)
            subprocess.run(partition_command, check=True, capture_output=True)
            self.assertEqual((root / 'partition/general-targets.txt').read_text(), 'Bridge.vo\nToy.vo\n')

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
            subprocess.run(['python3', str(HERE / 'expectations.py'), 'export', str(manifest),
                            str(root / 'statements/report.json'), '--append'], check=True, capture_output=True)
            self.assertTrue(compare(0, manifest)['differences'][0]['accepted'])
            compile(after, source.replace('target : side', 'target : True /\\ True').replace('exact I.', 'split; exact I.'))
            self.assertTrue(compare(0, manifest)['differences'][0]['accepted'])
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
            # A renamed logic parameter still moves local references and
            # their universe owners; it must not equate distinct definitions.
            definitions = ('Definition bound (A : Type) : Prop := True.\n'
                           'Definition other (A : Type) : Prop := True.\n'
                           'Lemma target : forall A : Type, bound A. Proof. intros; exact I. Qed.\n')
            for logic_parameter in ('LG', 'ProofLogic'):
                compile(before, 'From Nanofil Require Import Runtime Logic.\n' +
                        f'Module General (R : Runtime) ({logic_parameter} : LogicSig R).\n' +
                        definitions + 'End General.\n')
                compile(after, definitions)
                compare(0)
                compile(after, definitions.replace('forall A : Type, bound A', 'forall A : Type, other A'))
                self.assertEqual([d['name'] for d in compare(1)['differences']], ['target'])
            compile(after, flat)
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
            captured = ('From Nanofil Require Import Runtime Logic.\n'
                        'Module R := InterpRuntime. Module Captured (LG : LogicSig R).\n'
                        'Lemma target : True. Proof. exact I. Qed. End Captured.\n')
            compile(before, captured)
            compile(after, captured)
            compare(0)
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
