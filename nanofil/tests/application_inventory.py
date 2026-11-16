"""Find candidate named application paths; these still require Rocq validation."""
import json
import sys
from collections import defaultdict

rows = json.load(open(sys.argv[1]))
functors = {}
apps = defaultdict(list)

def module(row):
    p = row['file'].split('/rocq/')[1]
    root, rest = p.split('/', 1)
    return ('Nanofil.' if root == 'theories' else 'Glibc.') + rest[:-2].replace('/', '.')

for row in rows:
    for proof in row['proofs']:
        for scope in proof['scope']:
            if scope.get('functor'):
                old = functors.setdefault(scope['name'], row['file'])
                assert old == row['file'], ('ambiguous functor', scope['name'])
    for app in row['applications']:
        body = app['body']
        i = 0
        while i < len(body) and body[i] == '(':
            i += 1
        if i < len(body):
            op = body[i]
            while i+2 < len(body) and body[i+1] == '.':
                i += 2
                op = body[i]
            apps[op].append((row, app))

def candidates(row, scopes, tail, visited=()):
    for i, s in enumerate(scopes):
        if s.get('functor'):
            op = s['name']
            if op in visited:
                return []
            suffix = [p['name'] for p in scopes[i+1:]] + tail
            result = []
            for target, app in apps[op]:
                result += candidates(target, app['scope'], ([app['name']] if app['name'] else []) + suffix, visited+(op,))
            return result
    return ['.'.join([module(row)] + [s['name'] for s in scopes] + tail)]

output = []
for row in rows:
    for proof in row['proofs']:
        found = sorted(set(candidates(row, proof['scope'], [proof['name']])))
        output.append({'file': row['file'], 'line': proof['line'], 'name': proof['name'],
                       'functor': any(s.get('functor') for s in proof['scope']),
                       'candidate_queries': found})
print(json.dumps(output, indent=2))
