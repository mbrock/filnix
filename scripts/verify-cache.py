#!/usr/bin/env python3
"""Verify a closure against Cachix and its official NixOS-cache dependencies."""
import json
import subprocess
import sys


def query(paths, *options):
    result = subprocess.run(
        ["nix", "path-info", "--json", *options, *paths],
        check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    return json.loads(result.stdout)


local = query([sys.argv[1]], "--recursive")
remaining = set(local)
for cache in ("https://filc.cachix.org", "https://cache.nixos.org"):
    if not remaining:
        break
    remote = query(sorted(remaining), "--store", cache)
    verified = 0
    for path, info in remote.items():
        if info is None:
            continue
        for field in ("narHash", "narSize", "references"):
            expected, actual = local[path][field], info[field]
            if field == "references":
                expected, actual = sorted(expected), sorted(actual)
            if expected != actual:
                raise SystemExit(f"{cache}: {path}: {field} differs from local output")
        remaining.remove(path)
        verified += 1
    print(f"Verified {verified} paths on {cache}", flush=True)
if remaining:
    raise SystemExit("Missing public cache paths:\n" + "\n".join(sorted(remaining)))
print(f"Verified complete public closure: {len(local)} paths for {sys.argv[1]}")
