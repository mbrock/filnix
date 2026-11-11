#!/usr/bin/env python3
"""Shard CertiRocq's emitted nb.c into 16 compilation units, fold constant
Ascii/String constructor chains into static tables (const_strs.c / const_strs.h),
omit definitions superseded by overrides.c, and cast tag switches through intnat
so the shards compile cleanly under both native C compilers and filcc -DVERIFFI."""

import re
import sys

OVERRIDDEN = {
    "f_case_known_505884",
    "f_case_known_505857",
    "f_case_known_504260",
    "y_uncurried_known_504189",
    "f_case_known_531006",
    "NanofildMapsdhash_step_uncurried_17156",
    "f_case_known_509515",
    "StdlibdStringsdAsciidnat_of_ascii_known_502635",
    "StdlibdStringsdAsciidascii_of_nat_known_504633",
    "CorelibdBinNumsdPosDefdPosdto_nat_known_502300",
    "CorelibdBinNumsdIntDefdZdto_nat_known_504654",
    "CorelibdBinNumsdIntDefdZdof_nat_known_503816",
    "f_case_known_502275",
    "f_case_known_503847",
    "f_case_known_502700",
    "f_case_known_502804",
    "f_case_known_530876",
    "f_case_known_530885",
    "BackenddRegsdnat_leb_uncurried_known_629219",
    "BackenddRegsdnat_ltb_uncurried_known_629304",
    "f_case_known_507007",
    "f_case_known_503195",
    "BackenddIrTextdstring_of_rev_known_503223",
    "f_case_known_511259",
    "f_case_known_511786",
    "NanofildTermdlookup_uncurried_uncurried_known_511686",
    "NanofildTermdput_uncurried_uncurried_uncurried_known_511372",
    "f_case_known_509826",
    "NanofildMapsdZMapdRawdcreate_uncurried_uncurried_uncurried_uncurried_17435",
    "NanofildMapsdZMapdRawdbal_uncurried_uncurried_uncurried_uncurried_17530",
    "f_case_known_510779",
    "BackenddIrTextdis_layout_503",
    "BackenddIrTextdbetween_uncurried_uncurried_known_502835",
    "piece_clauses_uncurried_uncurried_uncurried_uncurried_uncurried_known_507608",
    "clauses_uncurried_uncurried_uncurried_uncurried_known_507228",
}

ASCII_RE = re.compile(
    r"^\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"\s*\$[A-Za-z0-9_]+ = ([13])LL;\n"
    r"(\s*)(\$[A-Za-z0-9_]+) = \(value\) \(\$alloc \+ 1LL\);\n"
    r"\s*\$alloc = \$alloc \+ 9LL;\n"
    r"\s*\*\(\(value \*\) \10 \+ -1LL\) = 8192LL;\n"
    r"(?:\s*\*\(\(value \*\) \10 \+ [0-7]LL\) = \$[A-Za-z0-9_]+;\n){8}",
    re.MULTILINE,
)

STR_RE = re.compile(
    r"^(\s*)(\$[A-Za-z0-9_]+) = \(value\) \(\$alloc \+ 1LL\);\n"
    r"\s*\$alloc = \$alloc \+ 3LL;\n"
    r"\s*\*\(\(value \*\) \2 \+ -1LL\) = 2048LL;\n"
    r"\s*\*\(\(value \*\) \2 \+ 0LL\) = (\$[A-Za-z0-9_]+);\n"
    r"\s*\*\(\(value \*\) \2 \+ 1LL\) = (\$[A-Za-z0-9_]+);\n",
    re.MULTILINE,
)

ZERO_RE = re.compile(r"^\s*(\$[A-Za-z0-9_]+) = 1LL;$", re.MULTILINE)
SW1_RE = re.compile(r"switch \(\$([A-Za-z0-9_]+) & 1\)")
SW2_RE = re.compile(r"switch \(\*\(\(value \*\) \$([A-Za-z0-9_]+) \+ -1LL\) & 255LL\)")
SW3_RE = re.compile(r"switch \(\$([A-Za-z0-9_]+) >> 1LL\)")


def patch_veriffi_switches(text: str) -> str:
    text = SW1_RE.sub(r"switch (((intnat)$\1) & 1)", text)
    text = SW2_RE.sub(r"switch (((intnat)*((value *) $\1 + -1LL)) & 255LL)", text)
    text = SW3_RE.sub(r"switch (((intnat)$\1) >> 1LL)", text)
    return text


def main() -> None:
    num_shards = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    with open("nb.c", "r") as f:
        lines = f.readlines()

    # Locate the end of declarations and the first function definition.
    decl_end = None
    first_def = None
    for idx, line in enumerate(lines):
        if decl_end is None and line.startswith("unsigned long long const "):
            decl_end = idx
        if idx + 1 < len(lines) and (line.startswith("value ") or line.startswith("void ")) and lines[idx + 1] == "{\n":
            first_def = idx
            break
    assert first_def is not None, "could not find first function definition in nb.c"
    if decl_end is None:
        decl_end = first_def

    with open("nb_decls.h", "w") as f:
        f.write("#pragma once\n#include \"values.h\"\n")
        for line in lines[:decl_end]:
            if line.startswith("#") or line.startswith("extern unsigned long long const "):
                continue
            f.write(line)

    funcs = []
    cur = []
    for line in lines[first_def:]:
        cur.append(line)
        if line == "}\n":
            funcs.append("".join(cur))
            cur = []

    str_pool = {}
    str_nodes = [None]

    def get_str_node(c: int, tail_id: int) -> int:
        key = (c, tail_id)
        sid = str_pool.get(key)
        if sid is None:
            sid = len(str_nodes)
            str_pool[key] = sid
            str_nodes.append((c, tail_id))
        return sid

    folded_funcs = []
    for fn in funcs:
        first_line = fn.lstrip().split("\n", 1)[0]
        m_name = re.match(r"^(?:value|void)\s+([A-Za-z0-9_$]+)\s*\(", first_line)
        if m_name and m_name.group(1) in OVERRIDDEN:
            continue

        ascii_vars = {}

        def repl_ascii(m):
            c = 0
            for b in range(8):
                if m.group(b + 1) == "3":
                    c |= 1 << b
            indent = m.group(9)
            var = m.group(10)
            ascii_vars[var] = c
            return f"{indent}{var} = ascii_vals[{c}];\n"

        fn2 = ASCII_RE.sub(repl_ascii, fn)
        if ascii_vars:
            const_strs = {v: 0 for v in ZERO_RE.findall(fn2)}
            const_strs["1LL"] = 0

            def repl_str(m):
                indent, outvar, cvar, tvar = m.group(1), m.group(2), m.group(3), m.group(4)
                if cvar in ascii_vars and tvar in const_strs:
                    sid = get_str_node(ascii_vars[cvar], const_strs[tvar])
                    const_strs[outvar] = sid
                    return f"{indent}{outvar} = const_str_vals[{sid}];\n"
                return m.group(0)

            while True:
                fn3 = STR_RE.sub(repl_str, fn2)
                if fn3 == fn2:
                    break
                fn2 = fn3

        folded_funcs.append(patch_veriffi_switches(fn2))

    with open("const_strs.h", "w") as f:
        f.write("#pragma once\n#include \"values.h\"\n")
        f.write("extern value ascii_vals[256];\n")
        f.write(f"extern value const_str_vals[{len(str_nodes)}];\n")
        f.write("void init_const_strs(void);\n")

    with open("const_strs.c", "w") as f:
        f.write("#include \"const_strs.h\"\n")
        f.write(f"static value const_str_blocks[{len(str_nodes)}][3];\n")
        f.write(f"value const_str_vals[{len(str_nodes)}];\n")
        f.write("static const unsigned char const_str_chars[] = {\n  0,")
        for idx in range(1, len(str_nodes)):
            f.write(f"{str_nodes[idx][0]},")
            if idx % 32 == 0:
                f.write("\n  ")
        f.write("\n};\n")
        f.write("static const unsigned int const_str_tails[] = {\n  0,")
        for idx in range(1, len(str_nodes)):
            f.write(f"{str_nodes[idx][1]},")
            if idx % 32 == 0:
                f.write("\n  ")
        f.write("\n};\n")
        f.write("void init_const_strs(void) {\n")
        f.write("  const_str_vals[0] = (value)1LL;\n")
        f.write(f"  for (unsigned int i = 1; i < {len(str_nodes)}; i++) {{\n")
        f.write("    const_str_blocks[i][0] = (value)2048LL;\n")
        f.write("    const_str_blocks[i][1] = ascii_vals[const_str_chars[i]];\n")
        f.write("    unsigned int t = const_str_tails[i];\n")
        f.write("    const_str_blocks[i][2] = (t == 0) ? (value)1LL : const_str_vals[t];\n")
        f.write("    const_str_vals[i] = (value)(&const_str_blocks[i][1]);\n")
        f.write("  }\n}\n")

    total_chars = sum(len(fn) for fn in folded_funcs)
    target_chars = (total_chars + num_shards - 1) // num_shards
    shards = [[] for _ in range(num_shards)]
    cur_shard = 0
    cur_chars = 0
    for fn in folded_funcs:
        if cur_shard + 1 < num_shards and cur_chars >= target_chars:
            cur_shard += 1
            cur_chars = 0
        shards[cur_shard].append(fn)
        cur_chars += len(fn)

    for s, chunk in enumerate(shards):
        with open(f"nb_{s}.c", "w") as f:
            f.write("#include <stdio.h>\n#include <stdlib.h>\n")
            f.write("#include \"gc_stack.h\"\n#include \"nb_decls.h\"\n#include \"const_strs.h\"\n\n")
            for fn in chunk:
                f.write(fn)


if __name__ == "__main__":
    main()
