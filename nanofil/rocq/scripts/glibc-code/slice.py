"""Slice gallina.pl output at whole-item and whole-block boundaries.

    python3 -I slice.py INPUT.v OUTDIR getopt|formatter

The option parser and formatter keep their original term representation.
"""
import pathlib
import re
import sys

BUDGET = 500  # lines of items or blocks in one file


def main(src, outdir, profile):
    if profile not in ("formatter", "getopt"):
        raise ValueError(f"unknown term slice profile {profile}")
    lines = open(src, encoding="utf-8").read().split("\n")
    top = lines.index('  TApp "module" [TList [')
    end = lines.index("  ]].")
    body = lines[top + 1:end]
    items = []
    for l in body:
        if l.startswith("    ") and not l.startswith("     "):
            items.append([l])
        else:
            items[-1].append(l)
    for it in items[:-1]:
        assert it[-1].endswith(";"), it[-1][:80]
        it[-1] = it[-1][:-1]

    # Units, in order: ("item", lines) or ("blocks", lines, owner index).
    files = []  # each: (kind, [lines of the list's elements])
    cur = []
    def flush():
        nonlocal cur
        if cur:
            files.append(("items", cur))
            cur = []
    def count(f):
        return sum(len(x) for x in f)
    for it in items:
        if len(it) <= BUDGET:
            if count(cur) + len(it) > BUDGET:
                flush()
            cur.append(it)
            continue
        # A function too long for a file: its blocks in files of their own,
        # after the items before it.
        flush()
        assert it[0].startswith('    cap_fn{ ') and it[1] == "      {", it[:2]
        assert it[-1] == "      } }", it[-1]
        blocks = []
        for l in it[2:-1]:
            if l.startswith("        @"):
                blocks.append([l])
            else:
                blocks[-1].append(l)
        for b in blocks[:-1]:
            assert b[-1].endswith(";")
            b[-1] = b[-1][:-1]
        names = []
        chunk = []
        for b in blocks:
            b[0] = "        cap_blk{ " + b[0].lstrip()
            b[-1] += " }"
            assert len(b) <= BUDGET
            if chunk and count(chunk) + len(b) > BUDGET:
                files.append(("blocks", chunk))
                names.append(len(files))
                chunk = []
            chunk.append(b)
        files.append(("blocks", chunk))
        names.append(len(files))
        item = [it[0], "      blocks (" + " ++ ".join(f"{profile}_blocks_{k:02d}" for k in names) + ") }"]
        # The items file after the blocks holds the function.
        cur.append(item)
    flush()

    render_slices(files, outdir, profile)


def render_slices(files, destination, profile):
    stem = {"formatter": "Formatter", "getopt": "Getopt"}[profile]
    header = [
        "(** This file contains part of glibc's checked option-parser module.",
        "    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)",
        "", "From Stdlib Require Import String ZArith List Ascii.",
        "From Nanofil Require Import Term.", "From Nanofil Require Import CaptureNotation.",
    ]
    if profile == "formatter":
        header[:2] = [
            "(** This file retains complete items or blocks of glibc's checked formatter.",
            "    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)",
        ]
    for k, (kind, elements) in enumerate(files, 1):
        uses = sorted(set(re.findall(rf"{profile}_blocks_(\d+)", str(elements))))
        out = header.copy()
        if uses:
            out.append("From Glibc Require Import " + " ".join(f"{stem}Code{n}" for n in uses) + ".")
        out += ["Import ListNotations.", "Open Scope string_scope.", "Open Scope Z_scope."]
        if uses:
            out.append("Open Scope list_scope.")
        out += ["", "(** Character atoms retain their byte values. *)",
                "Definition chr (n : nat) : term := TAtom (String (ascii_of_nat n) EmptyString).",
                "", f"(** These {kind} retain their order in the linked module. *)",
                f"Definition {profile}_{kind}_{k:02} : list term :=", "  ["]
        for j, element in enumerate(elements):
            out += element[:-1] + [element[-1] + (";" if j + 1 < len(elements) else "")]
        out += ["  ]."]
        assert len(out) <= 700
        pathlib.Path(destination, f"{stem}Code{k:02}.v").write_text("\n".join(out) + "\n")
    ns = [f"{k:02}" for k, (kind, _) in enumerate(files, 1) if kind == "items"]
    out = header + ["From Glibc Require Import " + " ".join(f"{stem}Code{n}" for n in ns) + ".",
                    "Import ListNotations.", "Open Scope string_scope.", "",
                    "(** The linked module joins every generated item without changing its order. *)",
                    f"Definition {profile}_term : term :=",
                    '  TApp "module" [TList (' + " ++ ".join(f"{profile}_items_{n}" for n in ns) + ")]."]
    assert len(out) <= 700
    pathlib.Path(destination, f"{stem}Term.v").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main(*sys.argv[1:])
