#!/usr/bin/env python3
"""Compare active Fil-C ports with pinned Nixpkgs and a selected upstream Git tree."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALIASES = {
    "gnugrep": "grep", "gnused": "sed", "gnum4": "m4", "gnumake": "make",
    "gnutar": "tar", "python312": "Python", "libpng": "libpng",
    "linux-pam": "Linux-PAM", "procps": "procps-ng", "icu": "icu",
    "libxkbcommon": "libxkbcommon-xkbcommon", "gtk3": "gtk", "gtk4": "gtk",
    "openssl-sarcasm": "openssl",
}


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args], text=True)


def upstream_projects(repo, rev):
    """Read directories and Projeny Orignames from Git, ignoring the worktree."""
    projects = set()
    tree = git(repo, "ls-tree", f"{rev}:projects")
    for entry in tree.splitlines():
        metadata, name = entry.split("\t", 1)
        if metadata.split()[1] == "tree":
            projects.add(name)
        elif name.endswith(".projeny"):
            descriptor = git(repo, "show", f"{rev}:projects/{name}")
            header = descriptor.split("diff --git ", 1)[0]
            match = re.search(r"^Origname: ([^/\n]+)$", header, re.M)
            if not match:
                raise ValueError(f"{name}: missing Origname")
            projects.add(match[1])
    return sorted(projects)


def candidates(row, projects):
    base = ALIASES.get(row["name"], row["pname"])
    prefix = base + "-"
    versions = [project[len(prefix):] for project in projects
                if project.startswith(prefix) and re.match(r"\d", project[len(prefix):])]
    if row["name"] in ("gtk3", "gtk4"):
        versions = [v for v in versions if v.startswith(row["name"][-1] + ".")]
    return versions


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.home() / "fil-c")
    parser.add_argument("--rev", help="upstream comparison revision; defaults to portsRev")
    parser.add_argument("--system", default="x86_64-linux")
    parser.add_argument("--all", action="store_true", help="include ports without version overrides")
    parser.add_argument("--json", action="store_true", help="emit every evaluated record as JSON")
    args = parser.parse_args()
    pin = json.loads((ROOT / "ports/upstream.json").read_text())["portsRev"]
    rev = git(args.repo, "rev-parse", "--verify", (args.rev or pin) + "^{commit}").strip()
    projects = upstream_projects(args.repo, rev)
    rows = json.loads(subprocess.check_output([
        "nix", "eval", "--impure", "--json", "--no-write-lock-file", "--file",
        str(ROOT / "scripts/audit-port-versions.nix"), "--apply",
        'f: f { root = builtins.getEnv "FILNIX_AUDIT_ROOT"; '
        'system = builtins.getEnv "FILNIX_AUDIT_SYSTEM"; }',
    ], text=True, env=dict(os.environ, FILNIX_AUDIT_ROOT=str(ROOT),
                           FILNIX_AUDIT_SYSTEM=args.system)))
    for row in rows:
        if "error" not in row:
            row["upstreamVersions"] = candidates(row, projects)
            row["upstreamPatches"] = [Path(p).name for p in row["patches"] if "/ports/patch/" in p]
    counts = Counter(row.get("comparison", "error") for row in rows)
    report = {"system": args.system, "portsRev": pin, "upstreamRev": rev,
              "counts": dict(counts), "ports": rows}
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print(f"{len(rows)} declarations; {sum(r.get('versionOverride', False) for r in rows)} "
              f"explicit/custom version overrides; {counts['older']} older, "
              f"{counts['newer']} newer, {counts['custom']} without comparable Nixpkgs versions")
        print(f"Upstream comparison: {rev}" + (" (ports pin)" if rev == pin else ""))
        print("Upstream versions are available candidates, not validated upgrades.\n")
        print(f"{'Port':<34} {'Filnix':<21} {'Nixpkgs':<21} Upstream candidates")
        for row in rows:
            if "error" in row:
                print(f"{row['name']}: {row['error']}")
            elif args.all or row["versionOverride"] or row["comparison"] != "same":
                print(f"{row['name']:<34} {str(row['version'] or '-'):21} "
                      f"{str(row['nativeVersion'] or '-'):21} "
                      f"{', '.join(row['upstreamVersions']) or '-'}")
    return int(bool(counts["error"]))


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (subprocess.CalledProcessError, ValueError, OSError) as error:
        print(f"audit failed: {error}", file=sys.stderr)
        sys.exit(1)
