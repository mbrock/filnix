"""Exact, source-bound permissions for reviewed intermediate audit changes.

Receipts are local build results, not signatures or permission to land. Only
packet.py writes one, after the stage validates its source guards and compiles
and audits both adapters. Reusing it with different source or evidence fails.
"""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def stage50_present():
    return (HERE.parent / 'stages/50-program.py').is_file()


def reviewed():
    if not stage50_present():
        return set()
    data = json.loads((HERE / 'audit-changes.json').read_text())
    if data['version'] != 1 or data['stage'] != '50-program':
        raise ValueError('unsupported audit-change policy')
    keys = {(d['file'], d['name']) for d in data['declarations']}
    if len(keys) != len(data['declarations']):
        raise ValueError('duplicate reviewed audit declaration')
    return keys


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def tree_digest(tree):
    h = hashlib.sha256()
    for path in sorted(Path(tree).rglob('*.v')):
        h.update(str(path.relative_to(tree)).encode() + b'\0')
        h.update(bytes.fromhex(digest(path)))
    return h.hexdigest()


def reference(key):
    return 'Glibc.' + key[0][:-2].replace('/', '.') + '.' + key[1]


def evidence_hashes(manifest):
    return {p.name: digest(p) for p in (manifest, manifest.with_suffix('.elaborated.json'),
                                      manifest.with_suffix('.equivalence.v'))}


def valid_assumptions(runtime, entry):
    before, after = entry.get('before'), entry.get('after')
    directions = entry.get('directions')
    if not isinstance(before, dict) or not isinstance(after, dict) or not isinstance(directions, list) or len(directions) != 2:
        return False
    if runtime == 'concrete':
        return directions == [{}, {}]
    if runtime != 'abstract' or before != after:
        return False
    return all(isinstance(d, dict) and all(
        re.fullmatch(r"Glibc\.Fix\.R\.[\w']+", name) and
        name in before and before[name] == type_
        for name, type_ in d.items()) for d in directions)


def interpreter_covers(pairs, receipts):
    closed = {(p['file'], p['name']) for r in receipts if r['runtime'] == 'concrete'
              for p in r['validated_pairs'] if valid_assumptions('concrete', p)}
    return all((p['file'], p['name']) in closed for p in pairs)


def receipt(tree, manifest, validation):
    """Call only after this stage's source-bound --check succeeds."""
    if not stage50_present():
        raise ValueError('stage 50 is absent; audited statement changes are forbidden')
    adapters = {}
    for line in manifest.read_text().splitlines():
        fields = line.split('\t')
        if fields[0] == '# equivalence':
            key = tuple(fields[1:3])
            if len(fields) != 5 or key in adapters or fields[3] == fields[4]:
                raise ValueError('invalid or duplicate bidirectional adapter pair')
            adapters[key] = fields[3:5]
    entries = []
    audited = {(e['file'], e['name']): e for e in validation['pairs']}
    if len(audited) != len(validation['pairs']):
        raise ValueError('duplicate audited adapter pair')
    for key, entry in audited.items():
        if entry['adapters'] != adapters.get(key) or not valid_assumptions(validation['runtime'], entry):
            raise ValueError('invalid adapter assumption evidence: ' + str(key) + ': ' + json.dumps(entry))
    if validation['runtime'] == 'concrete' and set(audited) != set(adapters):
        raise ValueError('concrete audit omitted adapter pairs')
    for item in json.loads(manifest.with_suffix('.elaborated.json').read_text())['changes']:
        key = (item['file'], item['name'])
        if key not in reviewed():
            continue
        if validation['runtime'] == 'abstract' and key not in audited:
            continue
        if item['kind'] != 'changed' or key not in adapters:
            raise ValueError('reviewed audit change lacks both adapters: ' + str(key))
        entries.append({'file': key[0], 'name': key[1], 'adapters': adapters[key],
                        'assumptions': audited[key],
                        'pairs': [{s: pair[s] for s in ('before', 'after')}
                                  for pair in [item] + item.get('variants', [])]})
    return {'version': 1, 'stage': '50-program', 'runtime': validation['runtime'],
            'tree': str(tree.resolve()), 'tree_sha256': tree_digest(tree),
            'manifest': str(manifest.resolve()),
            'actions_sha256': digest(HERE / 'expected-statement-changes/50-program.txt'),
            'policy_sha256': digest(HERE / 'audit-changes.json'),
            'evidence': evidence_hashes(manifest), 'declarations': entries,
            'validated_pairs': validation['pairs']}


class AuditChanges:
    def __init__(self, paths=()):
        self.receipts = []
        if paths and not stage50_present():
            raise ValueError('stage 50 is absent; audit-change receipts cannot be used')
        for path in paths:
            data = json.loads(Path(path).read_text())
            manifest = Path(data['manifest'])
            if (data.get('version') != 1 or data.get('stage') != '50-program' or
                    data.get('runtime') not in ('concrete', 'abstract') or
                    data.get('tree_sha256') != tree_digest(Path(data['tree'])) or
                    data.get('policy_sha256') != digest(HERE / 'audit-changes.json') or
                    data.get('actions_sha256') != digest(HERE / 'expected-statement-changes/50-program.txt') or
                    data.get('evidence') != evidence_hashes(manifest)):
                raise ValueError('stale or invalid stage-50 audit evidence: ' + str(path))
            pins = {(e['file'], e['name']): e for e in
                    json.loads(manifest.with_suffix('.elaborated.json').read_text())['changes']}
            adapters = {tuple(f[1:3]): f[3:5] for line in manifest.read_text().splitlines()
                        if (f := line.split('\t'))[0] == '# equivalence'}
            seen = set()
            for entry in data['declarations']:
                key = (entry['file'], entry['name'])
                pin = pins.get(key, {})
                pairs = [{s: p[s] for s in ('before', 'after')}
                         for p in [pin] + pin.get('variants', [])] if pin else []
                if (key not in reviewed() or key in seen or pin.get('kind') != 'changed' or
                        entry['adapters'] != adapters.get(key) or entry['pairs'] != pairs):
                    raise ValueError('receipt differs from generated evidence: ' + str(key))
                seen.add(key)
            validated = {(p['file'], p['name']): p for p in data['validated_pairs']}
            if len(validated) != len(data['validated_pairs']) or any(
                    p['adapters'] != adapters.get(k) for k, p in validated.items()):
                raise ValueError('invalid validated pair inventory')
            if data['runtime'] == 'concrete' and set(validated) != set(adapters):
                raise ValueError('concrete receipt omitted adapter pairs')
            if any(e['assumptions'] != validated.get((e['file'], e['name'])) for e in data['declarations']):
                raise ValueError('receipt assumption records disagree')
            self.receipts.append(data)

    def permits(self, key, before, after, source_digest):
        if key not in reviewed() or before is None or after is None or not source_digest:
            return False
        for data in self.receipts:
            if data['tree_sha256'] != source_digest:
                continue
            for entry in data['declarations']:
                if (entry['file'], entry['name']) != key:
                    continue
                if (not valid_assumptions(data['runtime'], entry.get('assumptions', {})) or len(entry.get('adapters', [])) != 2 or
                        len(set(entry['adapters'])) != 2):
                    continue
                if data['runtime'] == 'abstract' and not interpreter_covers([entry], self.receipts):
                    continue
                if {'before': before, 'after': after} in entry['pairs']:
                    return True
        return False

    def accepts_audit(self, before, after, source_digest):
        if (not before or not after or not before.get('qualified') or not after.get('qualified') or
                not before['pass'] or not after['pass'] or before['types'] != after['types']):
            return False
        for key in reviewed():
            if before.get('declaration') == after.get('declaration') == reference(key):
                return self.permits(key, before['normalized_statement'],
                                    after['normalized_statement'], source_digest)
        return False
