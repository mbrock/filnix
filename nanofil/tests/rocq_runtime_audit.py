#!/usr/bin/env python3
"""Match source proofs to compiled declarations and audit their assumptions."""
import json
import re
import subprocess
import sys
from pathlib import Path
from proof_inventory import inventory

FIELDS = '''state start ready alloc fresh_allocation address_space freed_bounds ready_kept
free free_lifetime retention free_keeps_ids free_checked free_succeeds
at_safepoint safepoints safepoint collector_live safepoint_lifetime non_moving
aux_round_trip rooting safepoint_ready'''.split()
ALLOWED = {f'Fix.R.{n}' for n in FIELDS}

def audit(source, glob, out):
    source_info = inventory(source)
    if source_info['unclassified_endings']:
        raise ValueError(f"unclassified proof endings: {source_info['unclassified_endings']}")
    text = glob.read_text()
    identity = re.search(r'^F([\w.]+)$', text, re.M)
    if identity is None:
        raise ValueError(f'{glob}: missing module identity')
    module = identity[1]
    entries = {(scope, name) for scope, name in re.findall(r'^(?:prf|def|inst) \d+:\d+ (\S+) (\S+)$', text, re.M)}
    compiled_proofs = set(re.findall(r'^prf \d+:\d+ (\S+) (\S+)$', text, re.M))
    source_proofs = {('.'.join(s['name'] for s in p['scope']) or '<>', p['name']) for p in source_info['proofs']}
    if compiled_proofs - source_proofs:
        raise ValueError(f'compiled proofs missing from source inventory: {sorted(compiled_proofs - source_proofs)}')
    queried, users, hypothetical = [], [], []
    for proof in source_info['proofs']:
        scope = '.'.join(s['name'] for s in proof['scope'])
        key = (scope or '<>', proof['name'])
        if key not in entries:
            raise ValueError(f'{source}:{proof["line"]}: source proof {key} absent from glob')
        name = '.'.join(filter(None, [module, scope, proof['name']]))
        if any(s.get('functor') for s in proof['scope']):
            hypothetical.append(name)
            continue
        sealed = [s for s in proof['scope'] if s.get('sealed')]
        if sealed:
            signature = sealed[-1]['signature']
            if signature not in source_info['signatures']:
                raise ValueError(f'{name}: unresolved signature {signature}')
            if proof['name'] not in source_info['signatures'][signature]:
                users.append(name)
                continue
        queried.append(name)
    declarations = len(source_info['proofs'])
    if len(queried) + len(users) + len(hypothetical) != declarations:
        raise ValueError('coverage count mismatch')
    out.mkdir(exist_ok=True)
    Path('RuntimeAudit.v').write_text(f'Require {module}.\n' + ''.join(f'Print Assumptions {n}.\n' for n in queried))
    result = subprocess.run(['rocq', 'c', '-q', '-R', 'theories', 'Nanofil', '-R', 'glibc', 'Glibc', 'RuntimeAudit.v'],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT) if queried else subprocess.CompletedProcess([], 0, stdout='')
    (out / 'assumptions.log').write_text(result.stdout)
    if result.returncode:
        raise ValueError(result.stdout)
    reports = result.stdout.count('Closed under the global context') + len(re.findall(r'^Axioms:\s*$', result.stdout, re.M))
    if reports != len(queried):
        raise ValueError(f'{reports} reports for {len(queried)} queried proofs')
    actual = set(re.findall(r'^(\S+)\s*:', result.stdout, re.M)) - {'Axioms'}
    coverage = {'source_count': declarations, 'queried': queried, 'covered_through_users': users,
                'functor_hypothetical_deferred_to_application_audit': hypothetical}
    (out / 'coverage.json').write_text(json.dumps(coverage, indent=2))
    summary = json.dumps({k: len(v) if isinstance(v, list) else v for k, v in coverage.items()})
    (out / 'summary').write_text(f'{module}: {summary}\n')
    (out / 'assumption-names').write_text(''.join(n + '\n' for n in sorted(actual)))
    print(summary)
    if actual - ALLOWED:
        raise ValueError(f'unexpected assumptions: {sorted(actual - ALLOWED)}')

if __name__ == '__main__':
    try:
        audit(*map(Path, sys.argv[1:]))
    except ValueError as e:
        sys.exit(f'runtime-audit: {e}')
