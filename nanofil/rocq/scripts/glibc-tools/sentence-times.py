#!/usr/bin/env python3
"""Report where a glibc build spends its time, one Rocq sentence at a time.

The Nix gate compiles each file with `rocq c -time` and keeps the output as
`sentence-timings/NAME.log`.  This program reads those logs together with the
sources and answers three questions:

    sentence-times.py LOGS TREE                 # time per kind of sentence
    sentence-times.py LOGS TREE --file NAME     # the slowest sentences of one file
    sentence-times.py LOGS TREE --over 5        # every sentence over 5 seconds

With `--check LIST` it fails when a sentence over the limit is not in LIST, and
`--write LIST` records the current ones.  A list entry names the file, the
declaration that contains the sentence, and the start of the sentence, so that
an entry survives edits elsewhere in the file.
"""
import argparse
import collections
from pathlib import Path
import re
import sys

TIMING = re.compile(r"^Chars (\d+) - (\d+) \[.*\] (\d+(?:\.\d*)?) secs \(")
DECLARATION = re.compile(
    rb"^\s*(?:Local\s+|Global\s+|#\[[^\]]*\]\s*)*"
    rb"(?:Lemma|Theorem|Corollary|Fact|Remark|Proposition|Definition|Example|Instance|Fixpoint|Program\s+Definition)"
    rb"\s+([A-Za-z_][A-Za-z0-9_']*)", re.M)
LOADING = ("From", "Require", "Import", "Export", "Include", "Module", "End", "Section")
COMMANDS = ("Definition", "Lemma", "Theorem", "Corollary", "Local", "Global", "Instance", "Ltac", "Notation",
            "Context", "Proof", "Fixpoint", "Hint", "Arguments", "Check", "Print", "Opaque", "Transparent")


def sentences(log, source):
    """Yield (seconds, line, declaration, text) for each timed sentence."""
    data = source.read_bytes()
    starts = [(m.start(), m[1].decode()) for m in DECLARATION.finditer(data)]
    for line in log.read_text(errors="replace").replace("\r", "\n").split("\n"):
        m = TIMING.match(line)
        if not m:
            continue
        start, end = int(m[1]), int(m[2])
        declaration = ""
        for position, name in starts:
            if position > start:
                break
            declaration = name
        text = " ".join(data[start:end].decode("utf-8", errors="replace").split())
        yield float(m[3]), data[:start].count(b"\n") + 1, declaration, text


def kind(text):
    word = re.match(r"[-+*{} ]*([A-Za-z_][A-Za-z0-9_']*)", text)
    word = word[1] if word else text[:10]
    if word in LOADING:
        return "load:" + word
    if word in ("Qed", "Defined"):
        return word
    if word in COMMANDS:
        return "command:" + word
    return "tactic:" + word


def key(path, declaration, text):
    return f"{path}\t{declaration}\t{text[:60]}"


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("logs", type=Path, help="directory of NAME.log files from rocq c -time")
    parser.add_argument("tree", type=Path, help="the glibc source tree those logs were compiled from")
    parser.add_argument("--file", help="report one file, by base name without .v")
    parser.add_argument("--over", type=float, help="list every sentence slower than this many seconds")
    parser.add_argument("--check", type=Path, help="fail on a sentence over the limit that this list lacks")
    parser.add_argument("--write", type=Path, help="write the list of sentences over the limit")
    parser.add_argument("--limit", type=float, default=5.0, help="seconds, for --check and --write (default 5)")
    args = parser.parse_args()

    sources = {}
    for path in args.tree.rglob("*.v"):
        if path.stem in sources:
            sys.exit(f"two files are named {path.stem}.v")
        sources[path.stem] = path
    rows = []
    for log in sorted(args.logs.glob("*.log")):
        if args.file and log.stem != args.file:
            continue
        source = sources.get(log.stem)
        if source is None:
            sys.exit(f"no source for {log.name} under {args.tree}")
        relative = str(source.relative_to(args.tree))
        rows += [(s, relative, line, d, t) for s, line, d, t in sentences(log, source)]
    if not rows:
        sys.exit("no timed sentences found")

    if args.check or args.write:
        slow = sorted((r for r in rows if r[0] > args.limit), reverse=True)
        if args.write:
            args.write.write_text("".join(f"{key(p, d, t)}\t{s:.1f}\n" for s, p, _, d, t in slow))
            print(f"wrote {len(slow)} sentences over {args.limit:g} s to {args.write}")
            return
        allowed = {line.rsplit("\t", 1)[0] for line in args.check.read_text().splitlines() if line.strip()}
        new = [r for r in slow if key(r[1], r[3], r[4]) not in allowed]
        for s, p, line, d, t in new:
            print(f"{p}:{line}: {s:.1f} s in {d or 'the file header'}: {t[:80]}")
        print(f"{len(slow)} sentences over {args.limit:g} s, {len(new)} not in {args.check}")
        sys.exit(1 if new else 0)

    if args.over is not None or args.file:
        threshold = args.over if args.over is not None else 0.0
        shown = sorted((r for r in rows if r[0] > threshold), reverse=True)
        for s, p, line, d, t in shown[: None if args.over is not None else 25]:
            print(f"{s:7.2f}  {p}:{line}  {d}  {t[:80]}")
        if args.over is not None:
            print(f"{len(shown)} sentences over {threshold:g} s")
            return

    total = sum(r[0] for r in rows)
    seconds, count = collections.Counter(), collections.Counter()
    for s, _, _, _, t in rows:
        seconds[kind(t)] += s
        count[kind(t)] += 1
    print(f"{len({r[1] for r in rows})} files, {total:.0f} s in {len(rows)} sentences")
    for k, s in seconds.most_common(20):
        print(f"{s:8.1f} s  {100 * s / total:5.1f}%  {count[k]:6d}  {k}")
    loading = sum(s for k, s in seconds.items() if k.startswith("load:"))
    print(f"{loading:8.1f} s  {100 * loading / total:5.1f}%  loading in all")


if __name__ == "__main__":
    main()
