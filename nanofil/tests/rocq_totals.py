#!/usr/bin/env python3
"""Print how long a Rocq tree takes to build, so the time is visible.

This is a readout, not a gate: nothing fails on these numbers. It prints

- serial: the summed time of every file, what one core pays to build
  the tree;
- critical path: the longest chain of imports, the wall time of a full
  rebuild with unlimited cores;
- edit-to-result: for an edit to a uniformly random source line, with
  every other object cached, the time until that file is checked, the
  summed time to recheck it and everything that imports it, and that
  recheck's longest chain.

It also lists the slowest files.

TIMES holds one line per file, as the per-file derivations write them:
"@@LABEL <seconds>s <lines> lines <path>.v". DEPS holds "name: dep dep"
lines naming files by base name. A dep may carry a namespace prefix
(Glibc/X); with --namespace, a prefixed dep counts only in that
namespace, since an edit in this tree never rebuilds another tree's
objects.
"""
import argparse
import re
import sys

RECORD = re.compile(r"^@@\S+\s+(\d+(?:\.\d+)?)s\s+(\d+) lines (\S+)\.v$")


def load(times_path, deps_path, namespace=None):
    time, lines = {}, {}
    with open(times_path) as fh:
        records = fh.read().splitlines()
    with open(deps_path) as fh:
        dep_lines = fh.read().splitlines()
    for line in records:
        m = RECORD.match(line.strip())
        if m:
            name = m[3].rsplit("/", 1)[-1]
            time[name], lines[name] = float(m[1]), int(m[2])
    deps = {n: set() for n in time}
    for line in dep_lines:
        name, sep, rest = line.partition(":")
        name = name.strip()
        if not sep or name not in deps:
            continue
        for d in rest.split():
            ns, _, d = d.rpartition("/")
            if ns and ns != namespace:
                continue
            if d in time and d != name:
                deps[name].add(d)
    return time, lines, deps


def totals(time, lines, deps):
    """Return the serial sum, the critical path and its files, and the
    line-weighted edit-to-result means (own, rebuild sum, rebuild path)."""
    users = {n: set() for n in time}
    for n, ds in deps.items():
        for d in ds:
            users[d].add(n)
    finish = {}  # end time of n in an unlimited-core full build

    def end(n):
        if n not in finish:
            finish[n] = time[n] + max((end(d) for d in deps[n]), default=0)
        return finish[n]

    sys.setrecursionlimit(max(1000, 4 * len(time)))
    last = max(time, key=end)
    chain = [last]
    while deps[chain[-1]]:
        chain.append(max(deps[chain[-1]], key=end))
    weight = own = rebuild = path = 0.0
    for n in time:
        seen, todo = {n}, [n]
        while todo:
            for u in users[todo.pop()]:
                if u not in seen:
                    seen.add(u)
                    todo.append(u)
        tail = {}  # longest chain from m to the end, within the recheck

        def longest(m):
            if m not in tail:
                tail[m] = time[m] + max((longest(u) for u in users[m] if u in seen), default=0)
            return tail[m]

        w = lines[n]
        weight += w
        own += w * time[n]
        rebuild += w * sum(time[m] for m in seen)
        path += w * longest(n)
    weight = weight or 1
    return (sum(time.values()), end(last), chain,
            own / weight, rebuild / weight, path / weight)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--label", required=True)
    parser.add_argument("--namespace", help="the logical prefix of this tree's files, such as Glibc")
    parser.add_argument("times")
    parser.add_argument("deps")
    args = parser.parse_args()
    time, lines, deps = load(args.times, args.deps, args.namespace)
    if not time:
        sys.exit(f"rocq_totals: no time records in {args.times}")
    serial, critical, chain, own, rebuild, path = totals(time, lines, deps)
    p = f"@@rocq-totals {args.label}:"
    slow = [n for n in chain if time[n] >= 5][:8]
    print(f"{p} {len(time)} files, serial {serial:.1f}s, critical path {critical:.1f}s "
          f"({' <- '.join(f'{n} {time[n]:.0f}s' for n in slow)})")
    print(f"{p} edit a random line: {own:.1f}s to that file's result, "
          f"{rebuild:.1f}s to recheck its importers serially, {path:.1f}s with unlimited cores")
    top = sorted(time, key=time.get, reverse=True)[:10]
    print(f"{p} slowest: {', '.join(f'{n} {time[n]:.0f}s' for n in top)}")


if __name__ == "__main__":
    main()
