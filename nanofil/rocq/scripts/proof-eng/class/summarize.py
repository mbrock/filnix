#!/usr/bin/env python3
"""Report measured closures and their common-file comparison."""
import csv
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
layouts = ('functor', 'flat', 'glibc')
tables, graphs = {}, {}
for layout in layouts:
    folder = root / (layout + '.measure')
    tables[layout] = {r['file']: r for r in csv.DictReader((folder / 'times.csv').open())}
    graph = {}
    for line in (folder / 'deps').read_text().splitlines():
        if ': ' not in line:
            continue
        targets, deps = line.split(': ', 1)
        for target in targets.split():
            if target.endswith('.vo'):
                graph[target[:-1]] = {d[:-1] for d in deps.split()
                                     if d.endswith('.vo') and not d.startswith('/')}
    graphs[layout] = graph

def closure(layout, target):
    seen = set()
    def visit(p):
        if p in seen:
            return
        seen.add(p)
        for d in graphs[layout][p]:
            visit(d)
    visit(target)
    return seen

def row(label, layout, files):
    rows = [tables[layout][f] for f in files]
    return totals(label, layout, rows)

def totals(label, layout, rows):
    assert all(r['status'] == '0' for r in rows), (label, layout)
    return [label, layout, len(rows),
            f"{sum(float(r['seconds']) for r in rows):.3f}",
            f"{sum(float(r['user_seconds']) + float(r['system_seconds']) for r in rows):.3f}",
            sum(int(r['vo_bytes']) for r in rows)]

writer = csv.writer(sys.stdout, lineterminator='\n')
writer.writerow(['closure', 'layout', 'files', 'sum_wall_seconds', 'sum_cpu_seconds', 'vo_bytes'])
targets = {'hello': 'hello/HelloGlibcJoin.v', 'hi': 'hi_atexit/HiAtexitSafe.v',
           'xsputn': 'stdio/PrintfBufferXsputnHeapSwitch.v', 'puts': 'libio/LibioPutsNl.v'}
for label, target in targets.items():
    sets = {layout: closure(layout, target) for layout in layouts}
    common = set.intersection(*sets.values())
    for layout in layouts:
        writer.writerow(row(label, layout, sets[layout]))
        writer.writerow(row(label + '-matched', layout, common))
for layout in layouts:
    writer.writerow(row('measured-union', layout, set(tables[layout])))
    writer.writerow(row('hello-hi-intersection', layout,
                        closure(layout, targets['hello']) & closure(layout, targets['hi'])))
common = set.intersection(*(set(tables[layout]) for layout in layouts))
for layout in layouts:
    writer.writerow(row('matched-union', layout, common))
abstract = root / 'abstract.measure/times.csv'
if abstract.exists():
    rows = list(csv.DictReader(abstract.open()))
    writer.writerow(totals('hello', 'abstract-flat', rows))
    concrete_hi = [tables['flat'][f] for f in closure('flat', targets['hi'])]
    writer.writerow(totals('hello-hi-union', 'two-flat-trees', rows + concrete_hi))
    writer.writerow(row('hello-hi-union', 'glibc',
                        closure('glibc', targets['hello']) | closure('glibc', targets['hi'])))
