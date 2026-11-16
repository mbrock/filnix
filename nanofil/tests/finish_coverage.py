"""Classify hidden application members using validated sealed exports."""
import json
import sys
from pathlib import Path
from collections import Counter

root = Path(sys.argv[1]).resolve()
inventory = json.loads((root / 'proof-inventory.json').read_text())
results = json.loads((root / 'application-query-results.json').read_text())
sources = {(r['file'], p['line'], p['name']): (r, p) for r in inventory for p in r['proofs']}
exports = []
for record in results.values():
    if record['status'] != 'queried':
        continue
    source = record['source']
    row, proof = sources[(source['file'], source['line'], source['name'])]
    if proof['scope'] and proof['scope'][-1].get('sealed'):
        signature = proof['scope'][-1]['signature']
        if proof['name'] in row['signatures'].get(signature, []):
            exports.append(record['query'])
for record in results.values():
    if record['status'] == 'queried':
        continue
    candidates = record['source']['candidate_queries']
    if not candidates:
        record['status'] = 'scanner only, unapplied functor'
        continue
    covering = []
    for query in candidates:
        users = [export for export in exports if query.startswith(export.rsplit('.', 1)[0] + '.')]
        if not users:
            raise ValueError(f'unresolved application coverage: {query}')
        covering.extend(users)
    record['status'] = 'covered through sealed users'
    record['users'] = sorted(set(covering))
(root / 'application-coverage.json').write_text(json.dumps(results, indent=2))
print(Counter(record['status'] for record in results.values()))
