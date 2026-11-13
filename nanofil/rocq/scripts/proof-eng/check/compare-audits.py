#!/usr/bin/env python3
"""Compare successful campaign audits, retaining every non-Closed assumption."""
import argparse
import json
from pathlib import Path
import re


def payload(raw):
    # Rocq announces lazily fetched proof bodies before giving the result.
    if 'Axioms:' in raw:
        raw = raw[raw.index('Axioms:'):]
    elif 'Closed under the global context' in raw:
        raw = raw[raw.index('Closed under the global context'):]
    return re.sub(r'\s+', ' ', raw).strip()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('before', type=Path)
    parser.add_argument('after', type=Path)
    a = parser.parse_args()
    before, after = [json.loads(p.read_text()) for p in (a.before, a.after)]
    failures = 0
    for group in sorted(set(before) | set(after)):
        left, right = before.get(group), after.get(group)
        if not left or not right or not left['pass'] or not right['pass']:
            print('FAIL', group, 'missing or failed audit')
            failures += 1
            continue
        for name in sorted(set(left['targets']) | set(right['targets'])):
            x, y = left['targets'].get(name), right['targets'].get(name)
            same = x and y and payload(x['raw']) == payload(y['raw'])
            print('PASS' if same else 'FAIL', group + ':' + name)
            if not same:
                print('before:', x['raw'] if x else '<absent>')
                print('after:', y['raw'] if y else '<absent>')
                failures += 1
    raise SystemExit(bool(failures) or not before or not after)
