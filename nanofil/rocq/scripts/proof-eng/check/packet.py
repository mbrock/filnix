#!/usr/bin/env python3
"""Assemble reviewed stage declarations, full types and kernel evidence."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from check import Tree, uncomment, compare
from expectations import Expectations

HERE = Path(__file__).resolve().parent


def unchanged_tactics(before, after, plugin, manifest, output):
    """Check the complete stage boundary, not just the relocated declarations."""
    if before is None or after is None or plugin is None:
        raise ValueError('stage 30 requires --stage30-before, --stage30-after and --plugin')
    destination = output.parent / '30-tactics-statements'
    if compare(argparse.Namespace(mode='statements', before=before, after=after,
                                  abstract_after=None, plugin=plugin, output=destination,
                                  expectations=manifest, files=None, jobs=4)):
        raise ValueError('stage 30 has unexpected statement differences; see 30-tactics-statements')
    with tempfile.TemporaryDirectory(prefix='tactics-audit-', dir=output.parent) as tmp:
        query = Path(tmp) / 'TacticsAudit.v'
        query.write_text('From Glibc Require Import GlibcTactics.\n'
                         'Print Assumptions GlibcTactics.step_named_rule.\n')
        audited = subprocess.run(['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                                  '-R', str(after.resolve()), 'Glibc', str(query)],
                                 capture_output=True, text=True, timeout=900)
        log = audited.stdout + audited.stderr
        (output.parent / '30-tactics.audit.log').write_text(log)
        if audited.returncode or 'Axioms:' in log or log.count('Closed under the global context') != 1:
            raise ValueError('step_named_rule is not Closed; see 30-tactics.audit.log')
    lint = subprocess.run([sys.executable, str(HERE.parent / 'lint-tactics.py'), str(after), '--check-inventory'],
                          capture_output=True, text=True, timeout=900)
    (output.parent / '30-tactics.lint.log').write_text(lint.stdout + lint.stderr)
    if lint.returncode:
        raise ValueError('stage 30 tactic budget failed; see 30-tactics.lint.log')


def packet(tree, manifests, output, stage30_before=None, stage30_after=None, plugin=None):
    output.parent.mkdir(parents=True, exist_ok=True)
    lines = ['# Proof-engineering cutover packet', '',
             'This packet is review material, not authorization to land.',
             'Hosted workflow status is not evidence; use the local Nix verdicts.', '']
    failures = []
    files = sorted(manifests.glob('*.txt'))
    if not files:
        failures.append('No reviewed stage manifests are present')
    for manifest in files:
        lines += ['## ' + manifest.stem, '', '### Declaration list and source guards', '',
                  '```text', manifest.read_text().rstrip(), '```', '']
        pins = manifest.with_suffix('.elaborated.json')
        proof = manifest.with_suffix('.equivalence.v')
        try:
            rules = Expectations(manifest)
            data = json.loads(pins.read_text())
            if data['version'] != 1:
                raise ValueError('unsupported elaborated version')
            changes = data['changes']
            keys = [(x['file'], x['name']) for x in changes]
            if len(set(keys)) != len(keys) or set(keys) != set(rules.rows):
                raise ValueError('elaborated declaration set differs from manifest')
            protected = {n for group in json.loads((HERE / 'audit-contracts.json').read_text()).values() for n in group}
            for change in changes:
                key = (change['file'], change['name'])
                if change['kind'] not in rules.rows[key] or change['name'] in protected:
                    raise ValueError('unapproved or audited declaration: ' + str(key))
                lines += [f"### {change['kind']} {change['file']}:{change['name']}", '']
                for side in ('before', 'after'):
                    lines += [side.capitalize() + ':', '', '```text',
                              change[side] if change[side] is not None else '<absent>', '```', '']
                for variant in change.get('variants', []):
                    lines += ['Additional exact runtime pair:', '']
                    for side in ('before', 'after'):
                        lines += [side.capitalize() + ':', '', '```text',
                                  variant[side] if variant[side] is not None else '<absent>', '```', '']
            if manifest.stem == '30-tactics':
                if any(kinds - {'moved', 'added'} for kinds in rules.rows.values()):
                    raise ValueError('stage 30 cannot exempt statement changes')
                unchanged_tactics(stage30_before, stage30_after, plugin, manifest, output)
                lines += ['PASS: statements unchanged across the complete stage-30 boundary; '
                          'every reviewed source has its target type, including universes. '
                          'The added rule has its pinned type and prints Closed. '
                          'The private-tactic count is within the recorded inventory.', '']
                continue
            source = proof.read_text()
            lines += ['### Equivalence proof', '', '```coq', source.rstrip(), '```', '']
            # Copy to a legal basename, then audit every proved declaration,
            # not only whichever Print Assumptions the author happened to add.
            names = re.findall(r"\b(?:Lemma|Theorem|Corollary)\s+([\w']+)", uncomment(source))
            if not names:
                raise ValueError('equivalence file contains no theorem')
            with tempfile.TemporaryDirectory(prefix='equivalence-', dir=output.parent) as tmp:
                path = Path(tmp) / 'Equivalence.v'
                path.write_text(source)
                command = ['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                           '-R', str(tree.resolve()), 'Glibc', str(path)]
                compiled = subprocess.run(command, capture_output=True, text=True, timeout=900)
                if compiled.returncode:
                    raise ValueError(compiled.stdout + compiled.stderr)
                declarations = Tree(Path(tmp)).declarations('Equivalence.v')
                queries = []
                for i, (name, scope, _) in enumerate(declarations):
                    qualified = (scope + '.' if scope else '') + name
                    queries += [f'Goal True. idtac "PACKET_{i}". Abort.',
                                f'Print Assumptions {qualified}.']
                path.write_text(source + '\n' + '\n'.join(queries) + '\n')
                audited = subprocess.run(command, capture_output=True, text=True, timeout=900)
                log = audited.stdout + audited.stderr
                (output.parent / (manifest.stem + '.equivalence.log')).write_text(log)
                results = re.split(r'PACKET_\d+\n', log)[1:]
                if audited.returncode or len(results) != len(declarations) or not results or any(
                        'Axioms:' in r or r.count('Closed under the global context') != 1 for r in results):
                    raise ValueError('equivalence audit is not Closed; see equivalence log')
                lines += [f'PASS: {len(results)} equivalence declarations compile and print Closed.', '']
            stage = HERE.parent / 'stages' / (manifest.stem + '.py')
            checked = subprocess.run([sys.executable, str(stage), '--check', str(tree.resolve())],
                                     capture_output=True, text=True, timeout=900)
            (output.parent / (manifest.stem + '.validation.log')).write_text(checked.stdout + checked.stderr)
            if checked.returncode:
                raise ValueError('stage --check failed; see validation log')
            lines += ['PASS: stage --check ties the equivalences to its transformation guards.', '']
        except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
            failures.append(f'{manifest.stem}: {error}')
    lines += ['## Verdict', ''] + (['FAIL: ' + x for x in failures] if failures else ['PASS: statement-changing stages have compiled equivalence evidence; stage 30 has unchanged-statement evidence.'])
    output.write_text('\n'.join(lines) + '\n')
    for failure in failures:
        print('FAIL', failure)
    print('FAIL' if failures else 'PASS', 'cutover packet:', output)
    return bool(failures)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('tree', type=Path)
    parser.add_argument('--manifests', type=Path, default=HERE / 'expected-statement-changes')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--stage30-before', type=Path)
    parser.add_argument('--stage30-after', type=Path)
    parser.add_argument('--plugin', type=Path)
    args = parser.parse_args()
    raise SystemExit(packet(args.tree, args.manifests, args.output,
                           args.stage30_before, args.stage30_after, args.plugin))
