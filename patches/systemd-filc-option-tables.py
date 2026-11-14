#!/usr/bin/env python3
"""Move systemd's OPTION*() stanzas out of their switch statements for Fil-C.

systemd 262 declares each command-line option where it is handled:

    switch (c) {
    OPTION_LONG("static", NULL, "Only set static hostname"):
            arg_static = true;

Natively, each stanza places a static Option in the SYSTEMD_OPTIONS ELF section
and expands to a case label, and the parser walks the section from
__start_SYSTEMD_OPTIONS to __stop_SYSTEMD_OPTIONS. Fil-C cannot walk from one
global into the next, so patches/systemd-262-filc.patch makes _OPTION() expand
to the fields of a table entry instead, and this script rewrites every parse
function as

    static const Option filc_options_0[] = {
    FILC_OPTION(7, OPTION_LONG("static", NULL, "Only set static hostname"))
    };
    FILC_REGISTER_OPTIONS(filc_options_0);

    static int parse_argv(...) {
            switch (c) {
            case 0x100 + 7 /* OPTION_LONG("static", NULL, "Only set static hostname") */:
                    arg_static = true;

The stanzas keep their order and the #if blocks around them, and each file
numbers its ids from 0, as __COUNTER__ does natively. A stanza is any use of a
macro that expands to _OPTION(); the script finds those from the #defines
themselves. Anything it does not understand (a stanza outside a function or
not used as a label) stops the build.

Usage: systemd-filc-option-tables.py SOURCE-ROOT
"""

import pathlib
import re
import sys

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def logical_lines(text):
    """Yield (start, end) of each preprocessor directive, continuations included."""
    for m in re.finditer(r"^[ \t]*#(?:[^\n\\]|\\.|\\\n)*", text, re.M):
        yield m.start(), m.end()


def option_macros(root):
    """Names of the macros whose expansion reaches _OPTION(), so their uses are stanzas."""
    bodies = {}
    for path in root.rglob("*.[ch]"):
        text = path.read_text(errors="replace")
        if "OPTION" not in text:
            continue
        for start, end in logical_lines(text):
            m = re.match(r"[ \t]*#[ \t]*define[ \t]+([A-Za-z_]\w*)(\([^)]*\))?(.*)", text[start:end], re.S)
            if m:
                bodies.setdefault(m.group(1), set()).update(IDENT.findall(m.group(3)))
    names = {"_OPTION"}
    while True:
        more = {n for n, refs in bodies.items() if n not in names and refs & names}
        if not more:
            break
        names |= more
    # FILC_OPTION and _OPTION are the expansion itself, not stanzas.
    return names - {"_OPTION", "FILC_OPTION"}


class Scanner:
    """Walks C source, skipping comments, literals and directives, tracking braces and #if blocks."""

    def __init__(self, text):
        self.text = text

    def tokens(self):
        """Yield (kind, start, end, depth, ifstack); kinds: ident, punct, directive."""
        t = self.text
        i, n, depth = 0, len(t), 0
        ifstack = []  # one list of directive lines per open #if group
        at_line_start = True
        while i < n:
            c = t[i]
            if c == "\n":
                at_line_start = True
                i += 1
                continue
            if c in " \t\r\f\v":
                i += 1
                continue
            if c == "#" and at_line_start:
                m = re.compile(r"#(?:[^\n\\]|\\.|\\\n)*").match(t, i)
                line = m.group(0)
                word = re.match(r"#\s*(\w*)", line).group(1)
                if word in ("if", "ifdef", "ifndef"):
                    ifstack = ifstack + [[line]]
                elif word in ("elif", "else", "elifdef", "elifndef"):
                    ifstack = ifstack[:-1] + [ifstack[-1] + [line]]
                elif word == "endif":
                    ifstack = ifstack[:-1]
                yield ("directive", i, m.end(), depth, ifstack)
                i = m.end()
                continue
            at_line_start = False
            if t.startswith("/*", i):
                i = t.index("*/", i + 2) + 2
                continue
            if t.startswith("//", i):
                j = t.find("\n", i)
                i = n if j < 0 else j
                continue
            if c in "\"'":
                j = i + 1
                while t[j] != c:
                    j += 2 if t[j] == "\\" else 1
                yield ("literal", i, j + 1, depth, ifstack)
                i = j + 1
                continue
            m = IDENT.match(t, i)
            if m:
                yield ("ident", i, m.end(), depth, ifstack)
                i = m.end()
                continue
            if c == "{":
                depth += 1
            elif c == "}":
                depth -= 1
            yield ("punct", i, i + 1, depth, ifstack)
            i += 1


def replay(ifstack):
    """Directives that reopen the given #if groups, positioned in their current branch."""
    return [line for group in ifstack for line in group]


def transform(text, macros, path):
    toks = list(Scanner(text).tokens())
    edits = []  # (start, end, replacement)
    functions = []  # dicts: insert, ifstack, entries
    next_id = 0
    toplevel_end = 0
    toplevel_stack = []
    current = None
    prev_sig = None  # last non-directive token at depth 0
    k = 0
    while k < len(toks):
        kind, s, e, depth, ifstack = toks[k]
        if kind == "directive":
            if depth == 0:
                toplevel_end, toplevel_stack = e, ifstack
            k += 1
            continue
        if kind == "punct" and text[s] == "{" and depth == 1 and current is None:
            # A brace opening at file scope: a function body if it follows a parameter list.
            if prev_sig is not None and text[prev_sig[0]:prev_sig[1]] == ")":
                current = {"insert": toplevel_end, "ifstack": toplevel_stack, "entries": []}
            else:
                current = {"insert": None}
            k += 1
            continue
        if kind == "punct" and text[s] == "}" and depth == 0:
            if current is not None and current.get("entries"):
                functions.append(current)
            current = None
            toplevel_end, toplevel_stack = e, ifstack
            prev_sig = (s, e)
            k += 1
            continue
        if depth == 0:
            if kind == "punct" and text[s] == ";":
                toplevel_end, toplevel_stack = e, ifstack
            prev_sig = (s, e)
            k += 1
            continue
        if kind == "ident" and text[s:e] in macros:
            line = text.count("\n", 0, s) + 1
            if current is None or current.get("insert") is None:
                sys.exit(f"{path}:{line}: {text[s:e]} outside a function body")
            j = k + 1
            end = e
            if j < len(toks) and toks[j][0] == "punct" and text[toks[j][1]] == "(":
                level = 0
                while j < len(toks):
                    ch = text[toks[j][1]] if toks[j][0] == "punct" else ""
                    level += ch == "("
                    level -= ch == ")"
                    if toks[j][0] == "directive":
                        sys.exit(f"{path}:{line}: directive inside {text[s:e]}()")
                    if level == 0:
                        break
                    j += 1
                end = toks[j][2]
                j += 1
            if j >= len(toks) or toks[j][0] != "punct" or text[toks[j][1]] != ":":
                sys.exit(f"{path}:{line}: {text[s:e]} is not used as a case label")
            base = current["ifstack"]
            if ifstack[: len(base)] != base:
                sys.exit(f"{path}:{line}: #if structure differs from the function's")
            current["entries"].append((next_id, text[s:end], ifstack[len(base):]))
            label = f"case 0x100 + {next_id}"
            stanza = " ".join(text[s:end].split())
            if "*/" not in stanza:
                label += f" /* {stanza} */"
            edits.append((s, end, label))
            next_id += 1
            k = j
            continue
        k += 1

    for f in functions:
        name = f"filc_options_{f['entries'][0][0]}"
        lines = [f"static const Option {name}[] = {{"]
        for i, stanza, extra in f["entries"]:
            reopen = replay(extra)
            lines += reopen
            lines.append(f"FILC_OPTION({i}, {stanza})")
            lines += ["#endif"] * len(extra)
        lines += ["};", f"FILC_REGISTER_OPTIONS({name});"]
        block = "\n".join(lines) + "\n"
        insert = f["insert"]
        # Start the block on a line of its own.
        if insert > 0 and text[insert - 1] != "\n":
            block = "\n" + block
        edits.append((insert, insert, block))

    for s, e, r in sorted(edits, key=lambda x: (x[0], x[1]), reverse=True):
        text = text[:s] + r + text[e:]
    return text, next_id


def main():
    root = pathlib.Path(sys.argv[1])
    macros = option_macros(root)
    files = stanzas = 0
    for path in sorted(root.rglob("*.c")):
        text = path.read_text()
        if not any(m in text for m in macros):
            continue
        new, count = transform(text, macros, path)
        if count:
            path.write_text(new)
            files += 1
            stanzas += count
    print(f"filc-option-tables: moved {stanzas} option stanzas in {files} files")


if __name__ == "__main__":
    main()
