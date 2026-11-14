#!/usr/bin/env python3
"""Compare two measure.sh runs of the same tree, one per Rocq version.

    report.py OLD_TREE[,OLD_TREE...] NEW_TREE[,NEW_TREE...] OUTPUT_DIR

Each tree is a directory that measure.sh compiled, with TREE.build beside
it. With several runs of one version, a file's seconds are their mean and
its memory the largest peak; sentences, warnings and errors come from the
first run. The report writes per-file.tsv (time, peak memory and slowest sentence
of every file in both versions, and the differences), warnings.tsv (warning
counts by kind, marking deprecations), failures.tsv (file, line and error of
each failed compile) and summary.md (totals and the ten largest changes
either way). A file that a run did not attempt is reported as such, never
given a substituted measurement.
"""
import collections
import csv
import importlib.util
from pathlib import Path
import re
import sys

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sentence_times', here.parent / 'sentence-times.py')
st = importlib.util.module_from_spec(spec)
spec.loader.exec_module(st)

WARNING = re.compile(r'^\[([\w.-]+(?:,[\w.-]+)*)\]\s*$', re.M)
ERROR = re.compile(r'File "[^"]*", line (\d+), characters \d+-\d+:\nError:(.*?)(?=\nFile "|\Z)', re.S)


def run(tree):
    tree = Path(tree).resolve()
    build = tree.parent / (tree.name + '.build')
    rows = {}
    for line in (build / 'times.txt').read_text().splitlines():
        if line.startswith('Command'):
            continue
        seconds, rss, name = line.split(' ', 2)
        rows[name] = {'seconds': float(seconds), 'rss_mb': round(int(rss) / 1024)}
    failed = {line.split(' ', 1)[1] for line in (build / 'make.log').read_text().splitlines()
              if line.startswith('FAIL ')}
    warnings = collections.Counter()
    errors = {}
    for name, row in rows.items():
        log = build / 'logs' / (name + '.log')
        text = log.read_text(errors='replace')
        row['status'] = 'fail' if name in failed else 'pass'
        for group in WARNING.findall(text):
            kinds = group.split(',')
            warnings[(kinds[0], 'deprecated' in kinds)] += 1
        timed = list(st.sentences(log, tree / name))
        if timed:
            seconds, line, declaration, sentence = max(timed)
            row['slowest'] = f'{seconds:.2f}s line {line} {declaration or "-"}: {" ".join(sentence.split())[:60]}'
        if name in failed:
            m = list(ERROR.finditer(text))
            errors[name] = (m[-1][1], ' '.join(m[-1][2].split())[:300]) if m else ('', text.strip()[-300:])
    return rows, warnings, errors


def runs(trees):
    results = [run(t) for t in trees.split(',')]
    rows, warnings, errors = results[0]
    for name, row in rows.items():
        others = [r[0][name] for r in results if name in r[0]]
        row['seconds'] = round(sum(o['seconds'] for o in others) / len(others), 2)
        row['rss_mb'] = max(o['rss_mb'] for o in others)
        if any(o['status'] == 'fail' for o in others):
            row['status'] = 'fail'
    return rows, warnings, errors


def main(old, new, out):
    out = Path(out)
    out.mkdir(parents=True, exist_ok=True)
    (a, wa, ea), (b, wb, eb) = runs(old), runs(new)
    old = old.split(',')[0]
    files = sorted(p.relative_to(Path(old)).as_posix() for d in ('theories', 'glibc') for p in (Path(old) / d).rglob('*.v'))
    table = []
    for f in files:
        x, y = a.get(f, {}), b.get(f, {})
        row = {'file': f}
        for tag, r in (('old', x), ('new', y)):
            row[f'{tag}_status'] = r.get('status', 'not attempted')
            row[f'{tag}_seconds'] = r.get('seconds', '')
            row[f'{tag}_rss_mb'] = r.get('rss_mb', '')
            row[f'{tag}_slowest'] = r.get('slowest', '')
        if x.get('status') == y.get('status') == 'pass':
            row['delta_seconds'] = round(y['seconds'] - x['seconds'], 2)
            row['delta_rss_mb'] = y['rss_mb'] - x['rss_mb']
        else:
            row['delta_seconds'] = row['delta_rss_mb'] = ''
        table.append(row)
    with (out / 'per-file.tsv').open('w', newline='') as fh:
        w = csv.DictWriter(fh, list(table[0]), delimiter='\t', lineterminator='\n')
        w.writeheader()
        w.writerows(table)
    with (out / 'warnings.tsv').open('w') as fh:
        fh.write('kind\tdeprecation\told\tnew\n')
        for kind, dep in sorted(set(wa) | set(wb), key=lambda k: -(wa[k] + wb[k])):
            fh.write(f'{kind}\t{"yes" if dep else "no"}\t{wa[(kind, dep)]}\t{wb[(kind, dep)]}\n')
    with (out / 'failures.tsv').open('w') as fh:
        fh.write('version\tfile\tline\terror\n')
        for tag, errors in (('old', ea), ('new', eb)):
            for f, (line, error) in sorted(errors.items()):
                fh.write(f'{tag}\t{f}\t{line}\t{error}\n')
    lines = ['| Part | Files | Old pass | New pass | Old seconds | New seconds | Change | Old peak MB | New peak MB |',
             '| --- | --- | --- | --- | --- | --- | --- | --- | --- |']
    for part, test in (('theories', lambda f: f.startswith('theories/')),
                       ('glibc/libio', lambda f: f.startswith('glibc/libio/')),
                       ('other glibc', lambda f: f.startswith('glibc/') and not f.startswith('glibc/libio/')),
                       ('all', lambda f: True)):
        rows = [r for r in table if test(r['file'])]
        paired = [r for r in rows if r['delta_seconds'] != '']
        so = sum(r['old_seconds'] for r in paired)
        sn = sum(r['new_seconds'] for r in paired)
        lines.append(f'| {part} | {len(rows)} | {sum(r["old_status"] == "pass" for r in rows)} | '
                     f'{sum(r["new_status"] == "pass" for r in rows)} | {so:.0f} | {sn:.0f} | '
                     f'{(sn - so) / so * 100 if so else 0:+.1f}% | '
                     f'{max((r["old_rss_mb"] for r in rows if r["old_rss_mb"] != ""), default=0)} | '
                     f'{max((r["new_rss_mb"] for r in rows if r["new_rss_mb"] != ""), default=0)} |')
    paired = [r for r in table if r['delta_seconds'] != '']
    for title, rows in (('Largest increases', sorted(paired, key=lambda r: -r['delta_seconds'])[:10]),
                        ('Largest decreases', sorted(paired, key=lambda r: r['delta_seconds'])[:10])):
        lines += ['', f'{title}:', '', '| File | Old s | New s | Change s | Old MB | New MB |', '| --- | --- | --- | --- | --- | --- |']
        lines += [f'| {r["file"]} | {r["old_seconds"]} | {r["new_seconds"]} | {r["delta_seconds"]:+} | '
                  f'{r["old_rss_mb"]} | {r["new_rss_mb"]} |' for r in rows]
    (out / 'summary.md').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main(*sys.argv[1:4])
