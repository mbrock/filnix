#!/usr/bin/env python3
"""Require documented native probes for Runtime's logical fields.

The witness is compiled separately by rocq.nix. This check covers the
documentation side, including derived lemmas and predicate parameters.
It deliberately refuses declaration forms it does not understand.
"""

import re
import sys
from pathlib import Path


def uncomment(text):
    depth = 0
    parts = []
    for token in re.split(r"(\(\*|\*\))", text):
        if token == "(*":
            depth += 1
        elif token == "*)":
            depth -= 1
        elif not depth:
            parts.append(token)
    if depth:
        raise ValueError("unbalanced Rocq comments")
    return "".join(parts)


def check(root):
    source = uncomment((root / "rocq/theories/core/Runtime.v").read_text())
    signature = source.split("Module Type Runtime.", 1)[1].split("End Runtime.", 1)[0]
    # Proof bodies contain tactics, not new fields.
    signature = re.sub(r"\bProof\..*?\bQed\.", "", signature, flags=re.S)
    fields = {}
    for sentence in re.split(r"\.(?=\s|$)", signature):
        if not sentence.strip():
            continue
        match = re.fullmatch(r"\s*(Axiom|Parameter|Lemma)\s+(\w+)\s*:\s*(.*?)\s*", sentence, re.S)
        if not match:
            raise ValueError(f"unrecognized Runtime declaration: {sentence.strip()}")
        kind, name, typ = match.groups()
        if kind != "Parameter" or re.search(r"\bProp\b", typ):
            fields[name] = kind
        elif name not in {"state", "start", "alloc", "free", "at_safepoint"}:
            # A new parameter might hide a proposition behind a type alias.
            # Require a row rather than silently classifying it as computation.
            fields[name] = kind
    page = (root / "docs/runtime-axioms.md").read_text()
    for name in fields:
        rows = re.findall(rf"^\| `{name}`(?:\s|\|).*?$", page, re.M)
        if len(rows) != 1:
            raise ValueError(f"{name}: expected exactly one runtime-axioms.md table row")
        probes = re.findall(r"\]\(\.\./tests/c/prog/(axiom-[\w-]+\.c)\)", rows[0])
        if probes and any(not (root / "tests/c/prog" / p).is_file() for p in probes):
            raise ValueError(f"{name}: row must name existing axiom-*.c probes")
        if not probes and not (fields[name] == "Lemma" and any(
            fields.get(parent) == "Axiom" for parent in re.findall(r"`(\w+)`", rows[0])[1:]
        )):
            raise ValueError(f"{name}: row must name existing axiom-*.c probes or, for a lemma, its axiom")
    print(f"runtime-signature: {len(fields)} logical fields have documented probes")


if __name__ == "__main__":
    try:
        check(Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parents[1])
    except (ValueError, IndexError) as error:
        sys.exit(f"runtime-signature: {error}")
