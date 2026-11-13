#!/usr/bin/env python3
"""Compare successful campaign audits, retaining every non-Closed assumption."""
import argparse
import json
from pathlib import Path


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path)
    parser.add_argument('after', type=Path)
    parser.add_argument('--hello-abstract', type=Path,
                        help='compare generic Hello against this abstract-tree audit; require concrete Hello Closed')
    a = parser.parse_args()
    before, after = [json.loads(p.read_text()) for p in (a.before, a.after)]
    abstract = json.loads(a.hello_abstract.read_text()) if a.hello_abstract else None
    failures = 0
    for group in sorted(set(before) | set(after)):
        left, right = before.get(group), after.get(group)
        if not left or not right or not left['pass'] or not right['pass']:
            print('FAIL', group, 'missing or failed audit')
            failures += 1
            continue
        for name in sorted(set(left['targets']) | set(right['targets'])):
            x, y = left['targets'].get(name), right['targets'].get(name)
            if abstract is not None and group == 'm3' and name == 'hello_never_panics':
                closed = y and y['pass'] and not y['types'] and not y['expected']
                print('PASS' if closed else 'FAIL', 'hello-concrete:Closed')
                failures += not closed
                y = abstract.get('m3', {}).get('targets', {}).get(name)
            same = (x and y and x.get('qualified') and y.get('qualified') and
                    x['pass'] and y['pass'] and
                    x['types'] == y['types'] and
                    x['normalized_statement'] == y['normalized_statement'])
            print('PASS' if same else 'FAIL', group + ':' + name)
            if not same:
                print('before:', x['raw'] if x else '<absent>')
                print('after:', y['raw'] if y else '<absent>')
                print('before statement:', x.get('normalized_statement', '<unqualified>') if x else '<absent>')
                print('after statement:', y.get('normalized_statement', '<unqualified>') if y else '<absent>')
                failures += 1
    raise SystemExit(bool(failures) or not before or not after)
