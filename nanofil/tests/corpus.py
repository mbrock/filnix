#!/usr/bin/env python3
"""Survey pinned corpora through progtest.sh; compare every expected outcome.

Usage: corpus.py CPROC C_TESTSUITE [--record] [--work DIR]
--record writes the baseline only after an intentional review of diagnostics.
--work retains assembly, compiler diagnostics, output and diffs for triage.
"""
import argparse
import collections
import pathlib
import re
import subprocess
import tempfile

HERE = pathlib.Path(__file__).resolve().parent


def survey(args, work):
    results = []
    for suite, root in [("cproc", pathlib.Path(args.cproc) / "test"),
                        ("c-testsuite", pathlib.Path(args.c_testsuite) / "tests/single-exec")]:
        root = root.resolve()
        if not root.is_dir():
            raise SystemExit(f"Corpus directory not found: {root}")
        for source in sorted(root.rglob("*.c")):
            # Ignore comments when finding entry points. No generated harnesses:
            # cproc's function-only and invalid constraint tests are inventoried.
            code = re.sub(r'/\*.*?\*/|//[^\n]*', '', source.read_text(), flags=re.S)
            name = suite + "/" + source.relative_to(root).as_posix()
            if args.test and name not in args.test:
                continue
            if not re.search(r'\bmain\s*\(', code):
                results.append((name, "no-main"))
                continue
            dest = work / name
            subprocess.run(["bash", str(HERE / "progtest.sh"), "--result",
                            str(dest), str(source)], check=False)
            result = (dest / "result").read_text().strip()
            results.append((name, result))
            print(name, result, flush=True)
    text = ''.join(f'{name}\t{result}\n' for name, result in results)
    if not results:
        raise SystemExit("No tests found; check source paths / --test")
    (work / "results.tsv").write_text(text)
    print(dict(collections.Counter(result for _, result in results)))
    expected = HERE / "corpus-expected.tsv"
    if args.record:
        expected.write_text(text)
    else:
        old = ''.join(line for line in expected.read_text().splitlines(True)
                      if not args.test or line.split('\t')[0] in args.test)
        if old != text:
            import difflib
            print(''.join(difflib.unified_diff(old.splitlines(True), text.splitlines(True),
                                             fromfile=str(expected), tofile="observed")))
            baseline = dict(line.split('\t') for line in old.splitlines())
            for name, result in results:
                if baseline.get(name) != result and (work / name / "log").exists():
                    print(name, (work / name / "log").read_text())
            raise SystemExit("Corpus changed (including newly passing tests); review and --record")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cproc")
    parser.add_argument("c_testsuite")
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--work", type=pathlib.Path)
    parser.add_argument("--test", action="append", help="run only this suite/path.c (repeatable)")
    args = parser.parse_args()
    if args.record and args.test:
        parser.error("--record requires the full corpus")
    if args.work:
        args.work.mkdir(parents=True, exist_ok=True)
        survey(args, args.work.resolve())
    else:
        with tempfile.TemporaryDirectory() as temp:
            survey(args, pathlib.Path(temp))
