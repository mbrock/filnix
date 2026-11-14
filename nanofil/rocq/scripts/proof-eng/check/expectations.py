#!/usr/bin/env python3
"""Read reviewed relocation lists and exact elaborated statement transitions."""
import argparse
import json
from pathlib import Path


class Expectations:
    def __init__(self, location):
        location = Path(location)
        files = sorted(location.glob('*.txt')) if location.is_dir() else ([location] if location.exists() else [])
        self.rows = {}
        self.moves = {}
        self.pins = {}
        for file in files:
            for line in file.read_text().splitlines():
                if not line.strip() or line.startswith('#'):
                    continue
                fields = line.split('\t')
                kind = fields[0]
                if kind not in ('changed', 'added', 'removed', 'moved') or len(fields) != (5 if kind == 'moved' else 3):
                    raise ValueError(f'{file}: invalid expectation row: {line}')
                key = tuple(fields[1:3])
                if not key[0].endswith('.v') or '*' in line:
                    raise ValueError(f'{file}: expectations must name exact declarations')
                if kind == 'moved':
                    target = tuple(fields[3:5])
                    if key in self.moves and self.moves[key] != target:
                        raise ValueError(f'conflicting move for {key}')
                    self.moves[key] = target
                    key = target
                self.rows.setdefault(key, set()).add(kind)
            pins = file.with_suffix('.elaborated.json')
            if pins.exists():
                data = json.loads(pins.read_text())
                if data['version'] != 1:
                    raise ValueError(f'{pins}: unsupported version')
                for item in data['changes']:
                    key = (item['file'], item['name'])
                    for pair in [item] + item.get('variants', []):
                        self.pins.setdefault(key, []).append((pair['before'], pair['after']))

    def names(self, file):
        return {n for f, n in set(self.rows) | set(self.moves) if f == file}

    def identity(self, key):
        seen = set()
        while key in self.moves:
            if key in seen:
                raise ValueError('cyclic declaration move')
            seen.add(key)
            key = self.moves[key]
        return key

    def canonical(self, text):
        # Replace full reference tokens, never suffixes or arbitrary qualifiers.
        import re
        for (file, name), target in sorted(self.moves.items(), key=lambda item: -len(str(item[0]))):
            old = 'Glibc.' + file[:-2].replace('/', '.') + '.' + name
            new = 'Glibc.' + target[0][:-2].replace('/', '.') + '.' + target[1]
            text = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?![\w'])", new, text)
            universe = Path(file).stem + '.' + name
            text = re.sub(r"(?<![\w.'])" + re.escape(universe) + r"(?=\.u\d+(?![\w.']))", new, text)
        return text

    def accepts(self, difference):
        key = (difference['file'], difference['name'])
        kind = difference['kind']
        before = difference['before']['normalized'] if difference['before'] else None
        after = difference['after']['normalized'] if difference['after'] else None
        if kind == 'moved' and 'moved' in self.rows.get(key, ()) and before == after:
            return True
        if kind not in self.rows.get(key, ()) and not (kind == 'moved' and 'changed' in self.rows.get(key, ())):
            return False
        # Several intentional stages may change the same intermediate lemma.
        # Each edge is an exact reviewed pair, not a wildcard for its name.
        todo, seen = [before], set()
        while todo:
            value = todo.pop()
            if value == after:
                return True
            if value in seen:
                continue
            seen.add(value)
            todo.extend(b for a, b in self.pins.get(key, ()) if a == value)
        return False


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['files', 'export'])
    parser.add_argument('manifest', type=Path)
    parser.add_argument('report', type=Path, nargs='?')
    parser.add_argument('--append', action='store_true', help='retain existing pairs and append exact runtime variants')
    args = parser.parse_args()
    rules = Expectations(args.manifest)
    if args.operation == 'files':
        print(' '.join(sorted({f for f, _ in set(rules.rows) | set(rules.moves)})))
    else:
        if args.report is None:
            parser.error('export requires a checker report.json')
        report = json.loads(args.report.read_text())
        if report['errors']:
            raise SystemExit('Refusing to export an incomplete statement check')
        changes = []
        found = set()
        for d in report['differences']:
            key = (d['file'], d['name'])
            if d['kind'] not in rules.rows.get(key, ()):
                raise SystemExit(f'Refusing unlisted difference: {key}')
            found.add(key)
            changes.append({k: d[k] for k in ('kind', 'file', 'name')} | {
                side: d[side]['normalized'] if d[side] else None for side in ('before', 'after')})
        if set(rules.rows) - found:
            raise SystemExit(f'Manifest entries not observed: {set(rules.rows) - found}')
        output = args.manifest.with_suffix('.elaborated.json')
        if args.append and output.exists():
            previous = json.loads(output.read_text())['changes']
            old = {(d['file'], d['name']): d for d in previous}
            if set(old) != found:
                raise SystemExit('Existing declaration set differs from export')
            for change in changes:
                item = old[(change['file'], change['name'])]
                if item['kind'] != change['kind']:
                    raise SystemExit('Existing declaration kind differs from export')
                pair = {k: change[k] for k in ('before', 'after')}
                if pair not in [{k: item[k] for k in ('before', 'after')}] + item.get('variants', []):
                    item.setdefault('variants', []).append(pair)
            changes = previous
        output.write_text(json.dumps({'version': 1, 'changes': changes}, indent=2) + '\n')
        print(f'Wrote {output}; review both statements before committing this approval')
