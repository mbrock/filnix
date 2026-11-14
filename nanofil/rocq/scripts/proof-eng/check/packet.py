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
from audit_changes import reviewed, receipt, tree_digest, evidence_hashes, AuditChanges, interpreter_covers, stage50_present

HERE = Path(__file__).resolve().parent


def unchanged_tactics(before, after, plugin, manifest, output, inventory=None):
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
    inventory = inventory or HERE.parent / 'tactic-inventory.json'
    command = [sys.executable, str(HERE.parent / 'lint-tactics.py'), str(after), '--check-inventory']
    lint = subprocess.run(command + ['--inventory', str(inventory)],
                          capture_output=True, text=True, timeout=900)
    (output.parent / '30-tactics.lint.log').write_text(lint.stdout + lint.stderr)
    if lint.returncode:
        raise ValueError('stage 30 tactic budget failed; see 30-tactics.lint.log')
    data = json.loads(inventory.read_text())
    owner = next((f for f, names in data['files'].items() if names), None)
    if owner is None:
        raise ValueError('tactic inventory is empty; cannot run count-minus-one control')
    data['files'][owner].pop()
    data['total'] -= 1
    control = output.parent / '30-tactics.inventory-minus-one.json'
    control.write_text(json.dumps(data, indent=2) + '\n')
    rejected = subprocess.run(command + ['--inventory', str(control)],
                              capture_output=True, text=True, timeout=900)
    (output.parent / '30-tactics.lint-control.log').write_text(rejected.stdout + rejected.stderr)
    if rejected.returncode != 1:
        raise ValueError('tactic count-minus-one control did not exit 1; see 30-tactics.lint-control.log')


def packet(tree, manifests, output, stage30_before=None, stage30_after=None, plugin=None,
           stage50_only=False, interpreter_evidence=None, tactic_inventory=None):
    tree = tree.resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    evidence = output.with_suffix('.stage50.json')
    evidence.unlink(missing_ok=True)
    lines = ['# Proof-engineering cutover packet', '',
             'This packet is review material, not authorization to land.',
             'Hosted workflow status is not evidence; use the local Nix verdicts.', '']
    failures = []
    files = sorted(manifests.glob('*.txt'))
    if not stage50_present():
        files = [p for p in files if p.stem != '50-program']
    elif manifests == HERE / 'expected-statement-changes' and not any(p.stem == '50-program' for p in files):
        failures.append('stage 50 is present but its reviewed manifest is missing')
    if stage50_only:
        files = [p for p in files if p.stem == '50-program']
    if not files:
        failures.append('No reviewed stage manifests are present')
    for manifest in files:
        try:
            if manifest.stem == '50-program':
                source_hash = tree_digest(tree)
                checked = subprocess.run([sys.executable, str(HERE.parent / 'stages/50-program.py'),
                                          '--check', str(tree.resolve())],
                                         capture_output=True, text=True, timeout=7200)
                (output.parent / '50-program.validation.log').write_text(checked.stdout + checked.stderr)
                if checked.returncode:
                    raise ValueError('stage --check failed; see 50-program.validation.log')
                runtimes = re.findall(r'^program-runtime: (concrete|abstract)$', checked.stdout, re.M)
                reports = re.findall(r'^program-assumption-evidence: (.+)$', checked.stdout, re.M)
                if len(runtimes) != 1 or len(reports) != 1:
                    raise ValueError('stage --check did not report its runtime and assumption evidence')
                validation = json.loads(Path(reports[0]).read_text())
                if validation['runtime'] != runtimes[0]:
                    raise ValueError('stage runtime disagrees with its assumption evidence')
                manifest = tree.resolve().parent / (tree.name + '.program/50-program.txt')
                hashes = evidence_hashes(manifest)
            lines += ['## ' + manifest.stem, '', '### Declaration list and source guards', '',
                      '```text', manifest.read_text().rstrip(), '```', '']
            pins = manifest.with_suffix('.elaborated.json')
            proof = manifest.with_suffix('.equivalence.v')
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
                permitted = manifest.stem == '50-program' and key in reviewed() and change['kind'] == 'changed'
                if change['kind'] not in rules.rows[key] or (change['name'] in protected and not permitted):
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
                unchanged_tactics(stage30_before, stage30_after, plugin, manifest, output, tactic_inventory)
                lines += ['PASS: statements unchanged across the complete stage-30 boundary; '
                          'every reviewed source has its target type, including universes. '
                          'The added rule has its pinned type and prints Closed. '
                          'The private-tactic count is within the recorded inventory, and '
                          'the count-minus-one inventory control exits 1.', '']
                continue
            source = proof.read_text()
            lines += ['### Equivalence proof', '', '```coq', source.rstrip(), '```', '']
            if manifest.stem == '50-program':
                # Stage 50 validates exact source/evidence inventories and uses
                # bounded shards, auditing every direction in each shard.
                if re.search(r'\b(?:Axioms?|Parameters?|Admitted)\b|\bDeclare\s+Module\b', uncomment(source)):
                    raise ValueError('stage-50 equivalence source introduces assumptions')
                result = receipt(tree, manifest, validation)
                if result['tree_sha256'] != source_hash or result['evidence'] != hashes:
                    raise ValueError('source or evidence changed during validation')
                if result['runtime'] == 'abstract':
                    concrete = AuditChanges([interpreter_evidence] if interpreter_evidence else [])
                    if not interpreter_covers(validation['pairs'], concrete.receipts):
                        raise ValueError('abstract pairs lack matching Closed interpreter evidence')
                evidence.write_text(json.dumps(result, indent=2) + '\n')
                if result['runtime'] == 'abstract':
                    counts = {f"{e['file']}:{e['name']}": len(e['before']) for e in validation['pairs']}
                    lines += ['PASS: abstract: runtime fields only. Field counts by pair:', '',
                              '```json', json.dumps(counts, indent=2), '```', '',
                              'Every pair also has matching Closed interpreter adapters.', '']
                else:
                    lines += ['PASS: interpreter adapters are Closed.', '']
                lines += ['PASS: stage 50 validates source guards and compiles and audits both '
                          'adapter directions through its bounded-shard checker. '
                          'Changed audits additionally require identical assumptions and exact type pairs.', '']
                continue
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
                    queries += [f'Goal True. Proof. idtac "PACKET_{i}". Abort.',
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
    parser.add_argument('--tactic-inventory', type=Path, help='reviewed inventory; defaults to the pipeline inventory')
    parser.add_argument('--stage50-only', action='store_true', help='validate the additional abstract stage-50 boundary')
    parser.add_argument('--interpreter-evidence', type=Path, help='required Closed counterpart for an abstract stage-50 packet')
    args = parser.parse_args()
    raise SystemExit(packet(args.tree, args.manifests, args.output,
                           args.stage30_before, args.stage30_after, args.plugin, args.stage50_only,
                           args.interpreter_evidence, args.tactic_inventory))
