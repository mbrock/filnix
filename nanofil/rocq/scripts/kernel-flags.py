#!/usr/bin/env python3
"""Fail when a proof file weakens what the Rocq kernel checks.

`Print Assumptions` lists the axioms a theorem depends on, but it does not
report every way a development can switch kernel checks off.  A file can
turn off the guard, positivity or universe checker, attach a
`bypass_check` attribute to one definition, declare rewrite rules or
kernel primitives, load an OCaml plugin, or ask for an inlined parameter,
and the theorems built on top can still print "Closed under the global
context" or a short axiom list.  This script is
an independent check: it reads every `.v` file under the given
directories (by default `theories` and `glibc` beside this script), drops
comments and strings, and prints each command or attribute that changes
how the kernel checks terms.  It exits 1 when it finds one.

    kernel-flags.py [DIR_OR_FILE...]

Each `_RocqProject` under the directories is also read for the command-line
options with the same effect, such as `-type-in-type`.
"""
from pathlib import Path
import re
import sys

# A command that sets or unsets one of the kernel's checking flags, with
# any locality or attribute prefix.  Setting a flag back on is listed too:
# a file has no reason to touch these at all.
PREFIX = r"(?:(?:#\[[^\]]*\]|Local|Global|Export)\s+)*"
COMMANDS = [
    ("checking flag", PREFIX + r"(?:Set|Unset)\s+(?:Universe|Guard|Positivity)\s+Checking\b"),
    ("typing flags", r"\bTyping\s+Flags\b"),
    ("definitional UIP", PREFIX + r"(?:Set|Unset)\s+Definitional\s+UIP\b"),
    ("rewrite rules", PREFIX + r"(?:Set|Unset)\s+Rewrite\s+Rules\b|^\s*" + PREFIX + r"(?:Symbol|Symbols|Rewrite\s+Rules?)\s"),
    ("inlined parameter", PREFIX + r"(?:Parameters?|Axioms?|Conjectures?)\s+Inline\b"),
    ("bypass_check attribute", r"#\[[^\]]*\bbypass_check\b"),
    ("kernel primitive", r"^\s*" + PREFIX + r"(?:Primitive|Register)\s"),
    ("plugin load", PREFIX + r"Declare\s+ML\s+Module\b"),
]
OPTIONS = re.compile(r"(?:^|\s)(-type-in-type|-impredicative-set|-allow-rewrite-rules|-(?:un)?set)(?=\s|$)")


def code_only(text):
    """Return text with comments and string contents blanked, keeping line breaks."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            out.append("  ")
            i += 2
        elif depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and not text.startswith('""', j)):
                j += 2 if text.startswith('""', j) else 1
            out.append('"' + "".join("\n" if c == "\n" else " " for c in text[i + 1:j]) + '"')
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def findings(path):
    code = code_only(path.read_text(errors="replace"))
    for kind, pattern in COMMANDS:
        for m in re.finditer(pattern, code, re.M):
            line = code.count("\n", 0, m.start()) + 1
            yield line, kind, " ".join(m.group(0).split())


def main(args):
    here = Path(__file__).resolve().parent.parent
    roots = [Path(a) for a in args] or [here / "theories", here / "glibc"]
    found = 0
    for root in roots:
        files = [root] if root.is_file() else sorted(root.rglob("*"))
        for path in files:
            if path.suffix == ".v":
                for line, kind, text in sorted(findings(path)):
                    print(f"{path}:{line}: {kind}: {text}")
                    found += 1
            elif path.name in ("_RocqProject", "_CoqProject"):
                for line, text in enumerate(path.read_text().splitlines(), 1):
                    for m in OPTIONS.finditer(text):
                        print(f"{path}:{line}: command-line option: {m.group(1)}")
                        found += 1
    if found:
        print(f"kernel-flags: {found} command(s) weaken kernel checking", file=sys.stderr)
        return 1
    print(f"kernel-flags: no command weakens kernel checking in {', '.join(map(str, roots))}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
