"""Scratch compiler validation of source-indexed application candidates."""
import json
import re
import subprocess
import sys
import time
from pathlib import Path
from collections import defaultdict
from rocq_runtime_audit import ALLOWED

root = Path(sys.argv[1]).resolve()
work = root / 'full-abstract'
rows = json.loads((root / 'application-inventory.json').read_text())
available = {str(p.relative_to(work))[:-3].replace('/', '.').replace('glibc.', 'Glibc.', 1).replace('theories.', 'Nanofil.', 1)
             for p in work.rglob('*.vo') if p.exists() and str(p.relative_to(work)).startswith(('glibc/', 'theories/'))}
pending, results = {}, {}
for i, row in enumerate(rows):
    if not row['functor']:
        continue
    choices = []
    for query in row['candidate_queries']:
        modules = [m for m in available if query.startswith(m + '.')]
        if modules:
            choices.append((max(modules, key=len), query))
    pending[i] = sorted(choices)
start = time.monotonic()
attempts = 0
while pending:
    groups = defaultdict(list)
    for i, choices in list(pending.items()):
        if not choices:
            results[i] = {'status': 'no accessible candidate', 'source': rows[i]}
            del pending[i]
        else:
            module, query = choices.pop(0)
            groups[module].append((i, query))
    for module, queries in groups.items():
        code = f'Require {module}.\n'
        for i, query in queries:
            code += f'Goal True. idtac "AUDIT_START_{i}". Abort.\nPrint Assumptions {query}.\n'
        code += 'Goal True. idtac "AUDIT_END". Abort.\nQuit.\n'
        t = time.monotonic()
        run = subprocess.run(['rocq', 'top', '-quiet', '-R', 'theories', 'Nanofil', '-R', 'glibc', 'Glibc'],
                             input=code, cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (root / 'application-query-last.log').write_text(run.stdout)
        if run.returncode:
            raise RuntimeError(run.stdout[-2000:])
        sections = re.split(r'\nAUDIT_(?:START_(\d+)|END)\n', run.stdout)
        if re.search(r'\bError:', sections[0]):
            raise RuntimeError(sections[0])
        blocks = {int(sections[n]): sections[n+1].replace('Rocq < ', '')
                  for n in range(1, len(sections)-1, 2) if sections[n] is not None}
        for i, query in queries:
            attempts += 1
            block = blocks[i]
            if re.search(r'\bError:', block):
                if 'was not found in the current environment' not in block:
                    raise RuntimeError((query, block))
                continue
            reports = block.count('Closed under the global context') + len(re.findall(r'^Axioms:\s*$', block, re.M))
            if reports != 1:
                raise RuntimeError((query, block))
            axioms = set(re.findall(r'^(\S+)\s*:', block, re.M)) - {'Axioms'}
            if axioms - ALLOWED:
                raise RuntimeError(f'UNEXPECTED ASSUMPTIONS {query}: {sorted(axioms - ALLOWED)}')
            results[i] = {'status': 'queried', 'query': query, 'assumptions': sorted(axioms), 'source': rows[i]}
            del pending[i]
        (root / 'application-query-results.json').write_text(json.dumps(results, indent=2))
        print(module, len(queries), f'{time.monotonic()-t:.2f}s', 'remaining', len(pending), flush=True)
    if not groups:
        break
(root / 'application-query-results.json').write_text(json.dumps(results, indent=2))
print(f'{attempts} attempts; elapsed={time.monotonic()-start:.3f}s', flush=True)
