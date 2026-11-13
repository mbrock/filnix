#!/usr/bin/env python3
"""Compile a glibc import closure at fixed fanout and retain every compiler log."""
import csv
import concurrent.futures
import os
import pathlib
import subprocess
import sys
import time

tree = pathlib.Path(sys.argv[1]).resolve()
model = pathlib.Path(os.environ['PE_MODEL']).resolve()
out = pathlib.Path(str(tree) + '.measure')
out.mkdir(exist_ok=True)
sources = sorted(str(p.relative_to(tree)) for p in tree.rglob('*.v'))
flags = ['-R', str(model), 'Nanofil', '-R', '.', 'Glibc']
dep = subprocess.run(['rocq', 'dep', *flags, *sources], cwd=tree, text=True, capture_output=True, check=True)
(out / 'deps').write_text(dep.stdout)
(out / 'dep.err').write_text(dep.stderr)
edges = {}
for line in dep.stdout.splitlines():
    if ': ' not in line:
        continue
    targets, deps = line.split(': ', 1)
    for target in targets.split():
        if target.endswith('.vo'):
            edges[target] = [p for p in deps.split() if p.endswith('.vo') and not p.startswith('/')]
order, seen = [], set()
def visit(p):
    if p in seen:
        return
    seen.add(p)
    for d in edges[p]:
        visit(d)
    order.append(p)
for target in sys.argv[2:]:
    visit(target.removesuffix('.v') + '.vo')
(out / 'order.txt').write_text('\n'.join(order) + '\n')
if os.environ.get('PE_PLAN_ONLY') == '1':
    print(f'{len(order)} files in closure')
    sys.exit(0)
(out / 'machine.txt').write_text(subprocess.check_output(['uname', '-a'], text=True) +
    pathlib.Path('/proc/loadavg').read_text() + pathlib.Path('/proc/cpuinfo').read_text())
def compile_one(obj):
    source = obj[:-1]
    log = out / (source + '.log')
    log.parent.mkdir(parents=True, exist_ok=True)
    timing = out / (source + '.time')
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(['/usr/bin/time', '-f', '%U,%S,%M', '-o', str(timing),
            'rocq', 'c', '-q', *flags, source], cwd=tree, stdout=stream, stderr=subprocess.STDOUT)
    return [source, f'{time.monotonic()-start:.6f}', *timing.read_text().splitlines()[-1].split(','),
           (tree / obj).stat().st_size if not result.returncode else 0, result.returncode]

jobs = int(os.environ.get('PE_JOBS', '4'))
print(f'fanout={jobs}', flush=True)
start = time.monotonic()
with (out / 'times.csv').open('w') as table, concurrent.futures.ThreadPoolExecutor(jobs) as pool:
    writer = csv.writer(table, lineterminator='\n')
    writer.writerow(['file', 'seconds', 'user_seconds', 'system_seconds', 'maxrss_kb', 'vo_bytes', 'status'])
    pending, running, done, failed = list(order), {}, set(), set()
    while pending or running:
        for obj in pending[:]:
            if set(edges[obj]) & failed:
                pending.remove(obj); failed.add(obj)
            elif len(running) < jobs and set(edges[obj]) <= done:
                pending.remove(obj)
                running[pool.submit(compile_one, obj)] = obj
        if not running:
            assert not pending, pending
            break
        complete, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
        for future in complete:
            obj = running.pop(future)
            row = future.result()
            writer.writerow(row); table.flush()
            print(' '.join(map(str, row)), flush=True)
            if row[-1]:
                failed.add(obj)
                print((out / (row[0] + '.log')).read_text(), flush=True)
            else:
                done.add(obj)
(out / 'elapsed.txt').write_text(f'{time.monotonic()-start:.6f}\n')
(out / 'failed.txt').write_text('\n'.join(sorted(failed)))
sys.exit(bool(failed))
