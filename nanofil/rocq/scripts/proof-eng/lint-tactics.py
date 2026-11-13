#!/usr/bin/env python3
"""Count private Ltac definitions; optionally enforce a cutover budget."""
import argparse
import importlib.util
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    "tactic_stage", Path(__file__).parent / "stages/30-tactics.py")
stage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(stage)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("tree", type=Path)
parser.add_argument("--max", type=int, dest="maximum")
parser.add_argument("--json", action="store_true")
args = parser.parse_args()
files = {}
libraries = {}
for path in sorted(args.tree.rglob("*.v")):
    names = [name for name, _, _ in stage.tactics(path.read_text())]
    if path.name in {"GlibcTactics.v", "LibioTactics.v"}:
        libraries[str(path.relative_to(args.tree))] = names
        continue
    if names:
        files[str(path.relative_to(args.tree))] = names
total = sum(map(len, files.values()))
if args.json:
    print(json.dumps(dict(total=total, files=files, libraries=libraries), indent=2))
else:
    for path, names in files.items():
        print(f"{path}: {len(names)}: {' '.join(names)}")
    print(f"{total} Ltac definitions outside the shared libraries in {len(files)} files")
raise SystemExit(args.maximum is not None and total > args.maximum)
