"""Inventory named source proofs independently of the compiler's glob output."""
import json
import sys
from pathlib import Path
from assumption_scan import tokens

DECLARATIONS = set('Lemma Theorem Example Corollary Fact Remark Proposition Definition Instance Fixpoint'.split())

def inventory(path):
    commands, current = [], []
    for word, line in tokens(path.read_text()):
        if word == '<end>':
            commands.append(current)
            current = []
        else:
            current.append((word, line))
    scopes, pending, proofs, unsupported, applications = [], None, [], [], []
    signatures = {}
    for cmd in commands:
        if not cmd:
            continue
        words = [w for w, _ in cmd]
        # Attributes and locality do not change the declaration's name.
        start = 0
        while start < len(words) and words[start] in {'{', '}'}:
            start += 1
        while start < len(words) and words[start] in {'Local', 'Global', 'Polymorphic', 'Monomorphic', 'Program', '#', '['}:
            if words[start:start+2] == ['#', '[']:
                start = words.index(']', start) + 1
            else:
                start += 1
        words = words[start:]
        if not words:
            continue
        signature_scopes = [s for s in scopes if s['kind'] == 'signature']
        if signature_scopes and words[0] in DECLARATIONS | {'Parameter', 'Parameters', 'Axiom', 'Axioms'}:
            signatures[signature_scopes[-1]['name']].append(words[1])
        if words[0] in DECLARATIONS:
            pending = {'name': words[1], 'line': cmd[start][1],
                       'scope': [dict(s) for s in scopes if s['kind'] != 'section']}
        elif words[0] in {'Qed', 'Defined'}:
            if pending is None:
                unsupported.append(cmd[0][1])
            else:
                proofs.append(pending)
                pending = None
        elif words[0] in {'Abort', 'Admitted'}:
            pending = None
        elif words[0] == 'Section':
            scopes.append({'kind': 'section', 'name': words[1]})
        elif words[0] == 'Include':
            applications.append({'name': '', 'body': words[1:],
                                 'scope': [dict(s) for s in scopes if s['kind'] != 'section'],
                                 'line': cmd[start][1]})
        elif words[0] == 'Module' and ':=' in words:
            j = 2 if words[1] in {'Import', 'Export', 'Type'} else 1
            applications.append({'name': words[j], 'body': words[words.index(':=')+1:],
                                 'scope': [dict(s) for s in scopes if s['kind'] != 'section'],
                                 'line': cmd[start][1]})
        elif words[0] == 'Module' and ':=' not in words:
            kind = 'signature' if words[1] == 'Type' else 'module'
            j = 2 if words[1] in {'Type', 'Import', 'Export'} else 1
            depth, outer = 0, []
            for w in words[j+1:]:
                if w == '(':
                    depth += 1
                elif w == ')':
                    depth -= 1
                elif not depth:
                    outer.append(w)
            scopes.append({'kind': kind, 'name': words[j],
                           'functor': '(' in words[j+1:],
                           'sealed': ':' in outer,
                           'signature': outer[outer.index(':')+1] if ':' in outer else None})
            if kind == 'signature':
                signatures[words[j]] = []
        elif words[0] == 'End' and scopes:
            scopes.pop()
    return {'file': str(path), 'proofs': proofs, 'unclassified_endings': unsupported,
            'applications': applications, 'signatures': signatures}

if __name__ == '__main__':
    paths = sorted(p for arg in sys.argv[1:] for p in Path(arg).rglob('*.v'))
    rows = [inventory(p) for p in paths]
    print(json.dumps(rows, indent=2))
