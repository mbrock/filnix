#!/usr/bin/env python3
"""Check that flake outputs and their whole closures are in the public caches.

CI cannot build the Fil-C toolchain, so it requires the campaign to have
published it: for each attribute, evaluate its output paths and walk their
references through narinfo lookups on filc.cachix.org, falling back to
cache.nixos.org for ordinary dependencies. Nothing is downloaded or built.
Exits 1 naming the roots whose closures are incomplete, 2 if evaluation
or the cache check itself fails. Only missing paths count as incomplete.

    scripts/ci-cache-check.py [--flake .] [ATTR...]
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import subprocess
import sys
import traceback
import urllib.error
import urllib.request

CACHES = ("https://filc.cachix.org", "https://cache.nixos.org")
STORE = "/nix/store/"


def nix(*args):
    return subprocess.run(["nix", "--extra-experimental-features", "nix-command flakes", *args],
                          check=True, text=True, stdout=subprocess.PIPE).stdout


def outputs(flake, attr):
    expr = "p: map (o: p.${o}.outPath) (p.outputs or [ \"out\" ])"
    try:
        return json.loads(nix("eval", "--json", f"{flake}#{attr}", "--apply", expr))
    except subprocess.CalledProcessError:
        # Distinct from 1 (not cached): the flake itself is broken.
        print(f"{attr}: evaluation failed", file=sys.stderr)
        sys.exit(2)


def narinfo(cache, path):
    """Return the path's references if the cache has it, else None.

    Reads the narinfo over HTTP rather than with nix path-info: newer Nix
    fails a whole path-info query when one path is missing, and every Nix
    remembers a missing narinfo for an hour."""
    name = path.removeprefix(STORE)
    try:
        request = urllib.request.Request(f"{cache}/{name.split('-', 1)[0]}.narinfo",
                                         headers={"User-Agent": "filnix-ci-cache-check"})
        with urllib.request.urlopen(request, timeout=30) as response:
            text = response.read().decode()
    except urllib.error.HTTPError as error:
        if error.code == 404:
            return None
        raise
    for line in text.splitlines():
        if line.startswith("References:"):
            return [STORE + ref for ref in line.split()[1:]]
    return []


def lookup(cache, paths):
    """Return {path: references} for the paths the cache has."""
    with ThreadPoolExecutor(32) as pool:
        results = dict(zip(paths, pool.map(lambda path: narinfo(cache, path), paths)))
    return {path: refs for path, refs in results.items() if refs is not None}


def closure(roots, known):
    """Walk references from roots, recording them in known; return the
    paths no cache has."""
    missing, frontier = set(), set(roots) - known.keys()
    while frontier:
        remaining = set(frontier)
        for cache in CACHES:
            hits = lookup(cache, remaining)
            known.update(hits)
            remaining -= hits.keys()
        missing |= remaining
        known.update((path, []) for path in remaining)
        frontier = {ref for path in frontier for ref in known[path]} - known.keys()
    return missing


def descendants(roots, known):
    seen, stack = set(), list(roots)
    while stack:
        path = stack.pop()
        if path not in seen:
            seen.add(path)
            stack.extend(known.get(path, []))
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--flake", default=".")
    parser.add_argument("attrs", nargs="*",
                        help="flake attributes; default: those in scripts/ci-outputs.txt")
    args = parser.parse_args()
    if not args.attrs:
        listing = Path(__file__).with_name("ci-outputs.txt").read_text().splitlines()
        args.attrs = [line for line in listing if line and not line.startswith("#")]
    known, missing, rows, failed = {}, set(), [], []
    for attr in args.attrs:
        roots = outputs(args.flake, attr)
        missing |= closure(roots, known)
        paths = descendants(roots, known)
        absent = sorted(paths & missing)
        rows.append((attr, len(paths), absent))
        if absent:
            failed.append(attr)
        status = "missing " + str(len(absent)) if absent else "ok"
        print(f"{attr}: {len(paths)} paths, {status}", flush=True)
        for path in absent[:20]:
            print(f"  not cached: {path}", flush=True)
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a") as out:
            out.write("### Binary cache coverage\n\n| Output | Closure | Status |\n| --- | --- | --- |\n")
            for attr, size, absent in rows:
                status = f"❌ {len(absent)} paths not cached" if absent else "✅ cached"
                out.write(f"| `{attr}` | {size} paths | {status} |\n")
            if failed:
                out.write("\nThe campaign on nix.swa.sh publishes these outputs once it has built "
                          "this revision; rerun the workflow after it has.\n")
    if failed:
        raise SystemExit("Not in the public caches: " + ", ".join(failed))


if __name__ == "__main__":
    try:
        main()
    except Exception:
        # Reserve exit 1 for the explicit missing-path result above. Network,
        # filesystem and unexpected errors must not look like pending caches.
        traceback.print_exc()
        sys.exit(2)
