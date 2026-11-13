#!/usr/bin/env python3
"""Run the campaign's queries with explicit, layout-independent assumption sets.

An empty set means Closed, not merely identical to an equally open baseline.
The original query files are the lead's exact sources, including regression
lemmas. A different layout supplies different .v files with the same targets.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent


def audit(tree, layout, contracts, output, groups=None):
    output.mkdir(parents=True, exist_ok=True)
    report = {}
    for group, targets in contracts.items():
        if groups and group not in groups:
            continue
        source = (layout / (group + '.v')).read_text()
        found = []
        def query(m):
            term = m[1]
            name = term.split('.')[-1]
            if name not in targets or name in found:
                raise ValueError(f'{group}: unexpected/duplicate query {term}')
            found.append(name)
            return (f'Goal True. idtac "PE_STATEMENT_{name}". Abort.\n'
                    f'Set Printing All. Check @{term}. Unset Printing All.\n'
                    f'Goal True. idtac "PE_AUDIT_{name}". Abort.\n'
                    f'Print Assumptions {term}.\n'
                    f'Goal True. idtac "PE_END_{name}". Abort.')
        try:
            source = re.sub(r'Print Assumptions\s+([\w.\']+)\s*\.', query, source)
            if set(found) != set(targets):
                raise ValueError(f'{group}: missing queries {set(targets) - set(found)}')
            with tempfile.TemporaryDirectory(prefix='audit-', dir=output) as tmp:
                path = Path(tmp) / 'Audit.v'
                path.write_text(source)
                command = ['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                           '-R', str(tree.resolve()), 'Glibc', str(path)]
                p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, timeout=900)
                (output / (group + '.log')).write_text(p.stdout)
                if p.returncode:
                    raise ValueError(f'rocq exited {p.returncode}; see {group}.log')
            results = {}
            for name, allowed in targets.items():
                statement = re.search(rf'PE_STATEMENT_{name}\n(.*?)PE_AUDIT_{name}\n', p.stdout, re.S)
                result = re.search(rf'PE_AUDIT_{name}\n(.*?)PE_END_{name}', p.stdout, re.S)
                if not statement or not result:
                    raise ValueError('missing output for ' + name)
                text = result[1].strip()
                closed = text.splitlines().count('Closed under the global context') == 1
                assumptions = sorted(n for n in re.findall(r"^([\w.']+)\s*:", text, re.M) if n != 'Axioms')
                valid = (closed and not assumptions and 'Axioms:' not in text) if not allowed else (
                    not closed and 'Axioms:' in text and assumptions == sorted(allowed))
                results[name] = {'pass': valid, 'assumptions': assumptions, 'expected': allowed,
                                 'statement': statement[1].strip(), 'raw': text}
            report[group] = {'pass': all(r['pass'] for r in results.values()), 'targets': results}
        except (ValueError, subprocess.TimeoutExpired, OSError) as e:
            report[group] = {'pass': False, 'error': str(e)}
        print(f"{'PASS' if report[group]['pass'] else 'FAIL'} audit {group}", flush=True)
    (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('tree', type=Path)
    p.add_argument('--layout', type=Path, default=HERE / 'layouts/original')
    p.add_argument('--contracts', type=Path, default=HERE / 'audit-contracts.json')
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--groups', nargs='+')
    a = p.parse_args()
    results = audit(a.tree, a.layout, json.loads(a.contracts.read_text()), a.output.resolve(), a.groups)
    raise SystemExit(not results or not all(r['pass'] for r in results.values()))
