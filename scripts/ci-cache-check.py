#!/usr/bin/env python3
"""Check that flake outputs and their whole closures are in the public caches.

CI cannot build the Fil-C toolchain, so it requires the campaign to have
published it: for each attribute, evaluate its output paths and walk their
references through narinfo lookups on filc.cachix.org, falling back to
cache.nixos.org for ordinary dependencies. Nothing is downloaded or built.
Exits 1 naming the roots whose closures are incomplete.

    scripts/ci-cache-check.py [--flake .] ATTR...
"""
import argparse
import json
import os
import subprocess
import sys

CACHES = ("https://filc.cachix.org", "https://cache.nixos.org")


def nix(*args):
    return subprocess.run(["nix", "--extra-experimental-features", "nix-command flakes", *args],
                          check=True, text=True, stdout=subprocess.PIPE).stdout


def outputs(flake, attr):
    expr = "p: map (o: p.${o}.outPath) (p.outputs or [ \"out\" ])"
    return json.loads(nix("eval", "--json", f"{flake}#{attr}", "--apply", expr))


def lookup(cache, paths):
    """Return {path: references} for the paths the cache has."""
    if not paths:
        return {}
    result = subprocess.run(
        # Nix remembers a missing narinfo for an hour; a rerun after the
        # campaign publishes must ask again.
        ["nix", "--extra-experimental-features", "nix-command", "path-info", "--json",
         "--option", "narinfo-cache-negative-ttl", "0", "--store", cache, *sorted(paths)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        info = json.loads(result.stdout or "{}")
    except json.JSONDecodeError:
        raise SystemExit(f"{cache}: {result.stderr.strip()}")
    if isinstance(info, list):  # Nix before 2.19
        info = {item["path"]: item for item in info if item.get("valid", True)}
    return {path: item["references"] for path, item in info.items() if item}


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
    parser.add_argument("attrs", nargs="+")
    args = parser.parse_args()
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
    main()
