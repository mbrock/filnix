#!/usr/bin/env python3
"""Run the campaign's queries with explicit, layout-independent assumption sets.

An empty set means Closed, not merely identical to an equally open baseline.
The original query files are the lead's exact sources, including regression
lemmas. A different layout supplies different .v files with the same targets.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from check import PATH, Tree
from expectations import Expectations

HERE = Path(__file__).resolve().parent


def assumption_types(text, aliases):
    """Keep types, not just axiom names; only reviewed module paths may move."""
    if 'Axioms:' not in text:
        return {}
    text = text.split('Axioms:', 1)[1]
    for old, new in sorted(aliases.items(), key=lambda pair: -len(pair[0])):
        text = re.sub(r"(?<![\w.'])" + re.escape(old) + r"(?=\.)", new, text)
    matches = list(re.finditer(r"^([\w.']+)\s*:", text, re.M))
    return {m[1]: re.sub(r'\s+', ' ', text[m.end():matches[i + 1].start()
            if i + 1 < len(matches) else len(text)]).strip() for i, m in enumerate(matches)}


def audit(tree, layout, contracts, output, groups=None):
    output.mkdir(parents=True, exist_ok=True)
    plugin = output / 'printer'
    subprocess.run(['bash', str(HERE / 'plugin.sh'), str(plugin)], check=True,
                   stdout=subprocess.DEVNULL)
    env = dict(os.environ)
    env['OCAMLPATH'] = str(plugin.parent) + ':' + env.get('OCAMLPATH', '')
    aliases_file = layout / 'assumption-aliases.json'
    aliases = {'Audit.AuditRuntime': 'AuditRuntime'}
    if aliases_file.exists():
        aliases.update(json.loads(aliases_file.read_text()))
    library = Tree(tree)
    moves = Expectations(HERE / 'expected-statement-changes')
    report = {}
    for group, targets in contracts.items():
        if groups and group not in groups:
            continue
        source = (f'Declare ML Module "{plugin.name}".\n' +
                  (layout / (group + '.v')).read_text())
        found = []
        def query(m):
            term = m[1]
            name = term.split('.')[-1]
            if name not in targets or name in found:
                raise ValueError(f'{group}: unexpected/duplicate query {term}')
            found.append(name)
            return (f'Goal True. idtac "PE_STATEMENT_{name}". Abort.\n'
                    f'Set Printing All. Set Printing Depth 1000000. Set Printing Width 1000000. Check @{term}.\n'
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
                context = copy.copy(library)
                local = Tree(Path(tmp))
                for field in ('modules', 'aliases', 'functors', 'module_types', 'signatures'):
                    setattr(context, field, getattr(library, field) | getattr(local, field))
                context.abstract_runtimes = library.abstract_runtimes | local.abstract_runtimes
                if 'Glibc.Audit.AuditRuntime' in local.abstract_runtimes:
                    context.aliases['Glibc.Audit.AuditRuntime'] = ('', '@RuntimeAbstract')
                command = ['rocq', 'c', '-q', '-R', os.environ['PE_MODEL'], 'Nanofil',
                           '-R', str(tree.resolve()), 'Glibc', str(path)]
                p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, timeout=900, env=env)
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
                if re.search(r'\.\.\.|…', statement[1] + text):
                    raise ValueError('truncated printed statement or assumptions: ' + name)
                closed = text.splitlines().count('Closed under the global context') == 1
                types = assumption_types(text, aliases)
                assumptions = sorted(types)
                valid = (closed and not assumptions and 'Axioms:' not in text) if not allowed else (
                    not closed and 'Axioms:' in text and assumptions == sorted(allowed))
                printed = statement[1].strip()
                printed = printed.split('\n     :', 1)[1].strip() if '\n     :' in printed else printed.split(' : ', 1)[1].strip()
                chunks = re.split(r'("(?:[^"]|"")*")', printed)
                for i in range(0, len(chunks), 2):
                    chunks[i] = re.sub(PATH, lambda m: 'Glibc.' + m[0] if m[0].startswith('Audit.') else m[0], chunks[i])
                normalized = moves.canonical(context.normalize(''.join(chunks), {}, concrete=not bool(allowed)))
                results[name] = {'pass': valid, 'assumptions': assumptions, 'expected': allowed,
                                 'statement': statement[1].strip(), 'raw': text, 'types': types,
                                 'qualified': True, 'normalized_statement': normalized}
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
    p.add_argument('--contracts', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--groups', nargs='+')
    a = p.parse_args()
    contracts = a.contracts or (a.layout / 'contracts.json')
    if not contracts.exists() and a.contracts is None:
        contracts = HERE / 'audit-contracts.json'
    results = audit(a.tree, a.layout, json.loads(contracts.read_text()), a.output.resolve(), a.groups)
    raise SystemExit(not results or not all(r['pass'] for r in results.values()))
