#!/usr/bin/env python3
"""Count private Ltac definitions; optionally enforce a cutover budget."""
import argparse
import json
import re
from pathlib import Path


def masked(text):
    """Hide nested comments and strings, preserving positions and newlines."""
    out = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        pair = text[i:i + 2]
        if not string and pair == "(*":
            depth += 1
            out[i:i + 2] = "  "
            i += 2
            continue
        if depth and pair == "*)":
            depth -= 1
            out[i:i + 2] = "  "
            i += 2
            continue
        if not depth and text[i] == '"':
            if string and pair == '""':
                out[i:i + 2] = "  "
                i += 2
                continue
            string = not string
            out[i] = " "
        elif depth or string:
            if text[i] != "\n":
                out[i] = " "
        i += 1
    if depth or string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def tactics(text):
    code = masked(text)
    for match in re.finditer(r"\b(?:(?:Local|Global)\s+)?Ltac\s+([\w']+)(?![\w'])", code):
        end = re.search(r"\.(?=\s|$)", code[match.end():])
        if not end:
            raise ValueError(f"unterminated Ltac {match[1]}")
        yield match[1], match.start(), match.end() + end.end()

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("tree", type=Path)
parser.add_argument("--max", type=int, dest="maximum")
parser.add_argument("--json", action="store_true")
parser.add_argument("--inventory", type=Path, default=Path(__file__).parent / "tactic-inventory.json",
                    help="the reviewed private definitions of the cutover tree")
parser.add_argument("--write-inventory", action="store_true", help="record this tree's private definitions")
parser.add_argument("--check-inventory", action="store_true",
                    help="fail when the tree has more private definitions than the inventory")
args = parser.parse_args()
files = {}
libraries = {}
for path in sorted(args.tree.rglob("*.v")):
    names = [name for name, _, _ in tactics(path.read_text())]
    # GlibcSym.v is the block executor: its tactics quote a goal for the
    # executor and are shared by every proof that runs it.
    if path.name in {"GlibcTactics.v", "LibioTactics.v", "GlibcSym.v"}:
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
if args.write_inventory:
    args.inventory.write_text(json.dumps(dict(total=total, files=files), indent=2) + "\n")
failed = args.maximum is not None and total > args.maximum
if args.check_inventory:
    inventory = json.loads(args.inventory.read_text())
    if sum(map(len, inventory["files"].values())) != inventory["total"]:
        raise SystemExit(f"{args.inventory}: the total does not match the listed definitions")
    for path, names in files.items():
        known = list(inventory["files"].get(path, []))
        for name in names:
            if name in known:
                known.remove(name)
            else:
                print(f"not in the inventory: {path}: {name}")
    print(f"the inventory records {inventory['total']} definitions")
    failed = failed or total > inventory["total"]
raise SystemExit(failed)
