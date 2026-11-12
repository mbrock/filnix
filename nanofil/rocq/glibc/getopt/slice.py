"""Split gallina.pl output at item and block boundaries, as hi_atexit does.

The resulting files retain every generated term in order. A function too
large for one file refers to lists of its complete blocks in earlier files.
"""
import pathlib
import re
import sys


def main(source, destination):
    lines = pathlib.Path(source).read_text().splitlines()
    body = lines[lines.index('  TApp "module" [TList [') + 1:lines.index("  ]].")]
    items = []
    for line in body:
        if line.startswith("    ") and not line.startswith("     "):
            items.append([])
        items[-1].append(line)
    for item in items[:-1]:
        assert item[-1].endswith(";")
        item[-1] = item[-1][:-1]

    files = []
    pending = []

    def size(elements):
        return sum(map(len, elements))

    def flush():
        if pending:
            files.append(("items", pending.copy()))
            pending.clear()

    for item in items:
        if len(item) <= 500:
            if size(pending) + len(item) > 500:
                flush()
            pending.append(item)
            continue
        flush()
        assert item[0].startswith('    TApp "func" [') and item[1] == "      TList ["
        assert item[-1].endswith("]]")
        blocks = []
        for line in item[2:]:
            if line.startswith('        TApp "block" ['):
                blocks.append([])
            blocks[-1].append(line)
        blocks[-1][-1] = blocks[-1][-1][:-2]
        for block in blocks[:-1]:
            assert block[-1].endswith(";")
            block[-1] = block[-1][:-1]
        chunks, chunk = [], []
        for block in blocks:
            assert len(block) <= 500
            if chunk and size(chunk) + len(block) > 500:
                files.append(("blocks", chunk))
                chunks.append(len(files))
                chunk = []
            chunk.append(block)
        files.append(("blocks", chunk))
        chunks.append(len(files))
        pending.append([item[0], "      TList (" + " ++ ".join(
            f"getopt_blocks_{k:02}" for k in chunks) + ")]"])
    flush()

    header = [
        "(** This file contains part of glibc's checked option-parser module.",
        "    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)",
        "", "From Stdlib Require Import String ZArith List Ascii.",
        "From Nanofil Require Import Term.",
    ]
    for k, (kind, elements) in enumerate(files, 1):
        uses = sorted(set(re.findall(r"getopt_blocks_(\d+)", str(elements))))
        out = header.copy()
        if uses:
            out.append("From Glibc Require Import " + " ".join(f"GetoptCode{n}" for n in uses) + ".")
        out += ["Import ListNotations.", "Open Scope string_scope.", "Open Scope Z_scope.",
                "", "(** Character atoms retain their byte values. *)",
                "Definition chr (n : nat) : term := TAtom (String (ascii_of_nat n) EmptyString).",
                "", f"(** These {kind} retain their order in the linked module. *)",
                f"Definition getopt_{kind}_{k:02} : list term :=", "  ["]
        for j, element in enumerate(elements):
            out += element[:-1] + [element[-1] + (";" if j + 1 < len(elements) else "")]
        out += ["  ]."]
        assert len(out) <= 700
        pathlib.Path(destination, f"GetoptCode{k:02}.v").write_text("\n".join(out) + "\n")
    ns = [f"{k:02}" for k, (kind, _) in enumerate(files, 1) if kind == "items"]
    out = header + ["From Glibc Require Import " + " ".join(f"GetoptCode{n}" for n in ns) + ".",
                    "Import ListNotations.", "Open Scope string_scope.", "",
                    "(** The linked module joins every generated item without changing its order. *)",
                    "Definition getopt_term : term :=",
                    '  TApp "module" [TList (' + " ++ ".join(f"getopt_items_{n}" for n in ns) + ")]."]
    pathlib.Path(destination, "GetoptTerm.v").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main(*sys.argv[1:])
