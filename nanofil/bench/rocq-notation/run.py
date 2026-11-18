#!/usr/bin/env python3
"""Run with rocq and its standard library on the path. All objects go in a temporary directory."""
import argparse
from pathlib import Path
import re
import shutil
import statistics
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROCQ = HERE.parents[1] / 'rocq'
ERROR_NAMES = "hello_image_item_glibc_errname'23_sys_errname"


# Keep the measured constructor baseline after the live emitter adopts SSA.
def baseline_source(name):
    path = f"nanofil/rocq/glibc/gen/hello/{name}.v"
    return subprocess.check_output(["git", "show", "7c7dccd80368:" + path], cwd=HERE, text=True)


def errnames(work):
    source = baseline_source('HelloImageTypedObjects10')
    header = source[:source.index('Definition ')]
    definition = re.search(rf'^Definition {ERROR_NAMES} : item :=.*?\.$', source, re.M | re.S)
    body = definition.group()

    def literal(match):
        values = [int(x) for x in match[1].split('; ')]
        if all(32 <= x <= 126 for x in values):
            return '"' + bytes(values).decode('ascii').replace('"', '""') + '"%irbytes'
        return match[0]

    (work / 'DataBaseline.v').write_text(header + body + '\n')
    rewritten, count = re.subn(r'\(Str \[([0-9]+(?:; [0-9]+)*)\]\)', literal, body)
    assert count and rewritten != body
    (work / 'DataLiteral.v').write_text(header + 'Require Import ByteSyntax.\n\n' + rewritten + '\n')


def measure(work, flags, names, repeats):
    def compile_one(name):
        subprocess.run(['rocq', 'c', '-q', *flags, name + '.v'], cwd=work, check=True)

    times = {name: [] for name in names}
    for name in names:
        compile_one(name)
    for i in range(repeats):
        offset = i % len(names)
        for name in names[offset:] + names[:offset]:
            start = time.perf_counter()
            compile_one(name)
            times[name].append(time.perf_counter() - start)
    print('module             .v bytes   .vo bytes   median seconds', flush=True)
    for name in names:
        source = (work / (name + '.v')).stat().st_size
        obj = (work / (name + '.vo')).stat().st_size
        print(f'{name:18} {source:8} {obj:11} {statistics.median(times[name]):16.3f}', flush=True)


def run(work, repeats, copies):
    core = work / 'theories/core'
    core.mkdir(parents=True)
    for name in ['Term.v', 'Syntax.v']:
        shutil.copy(ROCQ / 'theories/core' / name, core)
    flags = ['-R', 'theories', 'Nanofil']
    for path in HERE.glob('*.v'):
        shutil.copy(path, work)
    (work / 'Baseline.v').write_text(baseline_source('HelloImageTypedAL'))
    errnames(work)
    for name in ['theories/core/Term', 'theories/core/Syntax', 'CompactSyntax', 'AssemblySyntax', 'ByteSyntax']:
        subprocess.run(['rocq', 'c', '-q', *flags, name + '.v'], cwd=work, check=True)
    names = ['Baseline', 'Compact', 'Assembly']
    measure(work, flags, names, repeats)
    measure(work, flags, ['DataBaseline', 'DataLiteral'], repeats)
    subprocess.run(['rocq', 'c', '-q', *flags, 'Verify.v'], cwd=work, check=True)
    if copies > 1:
        for name in names:
            path = work / (name + '.v')
            header, sep, body = path.read_text().partition('Definition ')
            sample = sep + body
            path.write_text(header + '\n'.join(
                sample.replace('Definition hello_image_fn_', f'Definition copy{i}_') for i in range(copies)))
        print(f'Synthetic input: {copies} copies of both functions in one file', flush=True)
        measure(work, flags, names, repeats)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeats', type=int, default=6, help='timed compiles per form after warmup')
    parser.add_argument('--copies', type=int, default=1, help='also time a synthetic file with this many copies')
    args = parser.parse_args()
    if min(args.repeats, args.copies) < 1:
        parser.error('counts must be positive')
    subprocess.run(['rocq', '-v'], check=True)
    with tempfile.TemporaryDirectory(prefix='rocq-notation-') as directory:
        run(Path(directory), args.repeats, args.copies)
