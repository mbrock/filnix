#!/usr/bin/env python3
"""Split libpizlo's Linux syscall layer out of filc_runtime.c.

filc_runtime.c holds both the runtime core (GC entry, threads, signals,
checks) and about 300 filc_native_zsys_* functions that check their arguments
and call Linux libc. This script moves every zsys definition, with the comment
directly above it, together with the static helpers and struct types
that only those functions use, into filc_zsys_linux.c, and makes
filc_runtime.c include a per-OS backend at its end:

    #if PAS_OS(SERENITY)
    #include "filc_zsys_serenity.c"
    #else
    #include "filc_zsys_linux.c"
    #endif

The backend is included at the end, inside the same file-wide guards, so the
moved functions still see every static helper and variable they used before.
Definitions inside an #ifdef __x86_64__ group keep that guard.

Usage: split_zsys.py LIBPAS_SRC_DIR   (the directory holding filc_runtime.c)
"""

import re
import sys
from pathlib import Path

src = Path(sys.argv[1])
lines = (src / "filc_runtime.c").read_text().split("\n")

start_re = re.compile(r"^[A-Za-z_].*\bfilc_native_zsys_\w+\s*\(")
cond_re = re.compile(r"\s*#\s*(if|ifdef|ifndef|elif|else|endif)\b")

stack = []
moved = []  # (first_line, last_line, guards)
i = 0
while i < len(lines):
    line = lines[i]
    m = cond_re.match(line)
    if m:
        kind = m.group(1)
        if kind in ("if", "ifdef", "ifndef"):
            stack.append(line.strip())
        elif kind == "endif":
            stack.pop()
        else:
            stack[-1] = stack[-1] + " " + line.strip()
    if start_re.match(line) and not line.rstrip().endswith(";"):
        end = i
        while lines[end] != "}":
            end += 1
        first = i
        # Take the comment block that ends on the line just above.
        if first > 0 and lines[first - 1].strip().endswith("*/"):
            k = first - 1
            while "/*" not in lines[k]:
                k -= 1
            first = k
        guards = [g for g in stack if g not in ("#if LIBPAS_ENABLED", "#if PAS_ENABLE_FILC")]
        assert all(g in ("#ifdef __x86_64__",) + ("#if !PAS_COSMO",) for g in guards), guards
        moved.append((first, end, guards))
        i = end
    i += 1

nzsys = len(moved)

# Then move static helpers and struct types that only moved code uses,
# repeating until nothing more moves: a helper used by one moved helper may
# itself become movable. Entities inside an "#if !PAS_COSMO" block move with
# that guard.
static_re = re.compile(r"^static\b[^;=]*?\b(\w+)\s*\(")
struct_re = re.compile(r"^struct (\w+) \{$")
FILE_GUARDS = ["#if LIBPAS_ENABLED", "#if PAS_ENABLE_FILC"]
MOVABLE_GUARDS = ("#if !PAS_COSMO",)


def movable_entities():
    stack = []
    found = []
    taken = {k for f, e, _ in moved for k in range(f, e + 1)}
    i = 0
    while i < len(lines):
        if i in taken:
            i += 1
            continue
        line = lines[i]
        m = cond_re.match(line)
        if m:
            kind = m.group(1)
            if kind in ("if", "ifdef", "ifndef"):
                stack.append(line.strip())
            elif kind == "endif":
                stack.pop()
            else:
                stack[-1] = stack[-1] + " " + line.strip()
        extra = stack[2:]
        ok = stack[:2] == FILE_GUARDS and all(g in MOVABLE_GUARDS for g in extra)
        fm = static_re.match(line)
        sm = struct_re.match(line)
        if ok and fm and not line.rstrip().endswith(";"):
            end = i
            while lines[end] != "}":
                end += 1
            found.append((fm.group(1), i, end, list(extra)))
            i = end
        elif ok and sm:
            end = i
            while lines[end] != "};":
                end += 1
            found.append((sm.group(1), i, end, list(extra)))
            i = end
        i += 1
    return found


while True:
    taken = {k for f, e, _ in moved for k in range(f, e + 1)}
    moved_text = "\n".join(lines[k] for k in sorted(taken))
    core_lines = [(k, l) for k, l in enumerate(lines) if k not in taken]
    progress = False
    for name, first, end, guards in movable_entities():
        word = re.compile(rf"\b{re.escape(name)}\b")
        used_in_core = any(word.search(l) for k, l in core_lines if not first <= k <= end)
        if not used_in_core and word.search(moved_text):
            if first > 0 and lines[first - 1].strip().endswith("*/"):
                k = first - 1
                while "/*" not in lines[k]:
                    k -= 1
                first = k
            moved.append((first, end, guards))
            progress = True
            break
    if not progress:
        break

moved.sort()

out_linux = [
    "/* libpizlo's Linux syscall layer, moved out of filc_runtime.c by",
    "   split_zsys.py. filc_runtime.c includes this file at its end, inside its",
    "   file-wide guards, so these functions see its static helpers. */",
    "",
]
keep = [True] * len(lines)
for first, end, guards in moved:
    for k in range(first, end + 1):
        keep[k] = False
    body = lines[first : end + 1]
    for g in reversed(guards):
        body = [g] + body + ["#endif"]
    out_linux += body + [""]

core = [l for l, k in zip(lines, keep) if k]
tail = max(i for i, l in enumerate(core) if l.strip() == "PAS_END_EXTERN_C;")
core[tail:tail] = [
    "#if PAS_OS(SERENITY)",
    '#include "filc_zsys_serenity.c"',
    "#else",
    '#include "filc_zsys_linux.c"',
    "#endif",
    "",
]

(src / "filc_runtime.c").write_text("\n".join(core))
(src / "filc_zsys_linux.c").write_text("\n".join(out_linux) + "\n")
print(f"moved {nzsys} zsys functions and {len(moved) - nzsys} helpers "
      f"({sum(e - f + 1 for f, e, _ in moved)} lines); filc_runtime.c now {len(core)} lines")
