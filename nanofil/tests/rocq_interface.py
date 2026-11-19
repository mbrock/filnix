#!/usr/bin/env python3
"""Write the interface of a Rocq file: the file with its comments removed
and each opaque proof that no other file can see replaced by Admitted.

The proof-using tool uses the statistics to find section proofs for which
Rocq can suggest an explicit list of variables.

A proof is replaced only when it starts with "Proof." or "Proof using
...", ends with "Qed.", and stands outside every Section, or inside one
with a "Proof using" clause. Inside a Section, Rocq takes the section
variables a Qed proof uses into the lemma's type, so without the clause
the interface could not know them, and the proof is kept. "Proof using"
is kept with its clause, since it names those variables. Everything else
is kept as written, so the interface compiles exactly the declarations
of the file.

    rocq_interface.py SRC DST            # one file
    rocq_interface.py --tree SRC DST     # every .v file under SRC, and DST/replaced
    rocq_interface.py --stats FILE...    # how many proofs each keeps
"""
import pathlib
import re
import sys


def sentences(text):
    """Split text, without comments, into Rocq sentences. A sentence ends
    at a dot followed by white space or the end, outside a string, that
    is not part of "..". The pieces keep every character, so they join
    back to the text."""
    out, start, i, n = [], 0, 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            i = j + 1
            continue
        if c == "." and (i + 1 == n or text[i + 1].isspace()) and not (text[i - 1 : i + 1] == ".." and text[i - 2 : i - 1] != "."):
            out.append(text[start : i + 1])
            start = i + 1
        i += 1
    out.append(text[start:])
    return out


def strip_comments(text):
    """Remove (* ... *) comments, which nest, outside strings."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if depth == 0 and text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append(text[i : j + 1])
            i = j + 1
        elif text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


# A sentence's words after any bullets or braces that precede it.
LEAD = re.compile(r"^[\s{}\-+*]*")


def words(s):
    return LEAD.sub("", s).split()


def interface(text):
    """Return (interface text, proofs replaced, proofs kept)."""
    parts = sentences(strip_comments(text))
    out, stack = [], []
    replaced = kept = 0
    i = 0
    while i < len(parts):
        s = parts[i]
        w = words(s)
        head = w[0] if w else ""
        if head in ("Proof.", "Proof") and (head == "Proof." or (len(w) > 1 and w[1] in ("using", "with"))):
            # Find the sentence that ends this proof.
            j = i + 1
            while j < len(parts):
                ww = words(parts[j])
                if ww and ww[-1] in ("Qed.", "Defined.", "Admitted.", "Abort.", "Save."):
                    break
                j += 1
            ends = j < len(parts) and words(parts[j]) == ["Qed."]
            using = len(w) > 1 and w[1] == "using"
            in_section = "S" in stack
            if ends and (using or not in_section):
                lead = s[: len(s) - len(s.lstrip())]
                out.append((s if using else lead) + ("\nAdmitted." if using else "Admitted."))
                replaced += 1
                i = j + 1
                continue
            kept += 1
            out.extend(parts[i : j + 1])
            i = j + 1
            continue
        if head == "Section" and len(w) > 1:
            stack.append("S")
        elif head == "Module" and ":=" not in s:
            stack.append("M")
        elif head == "End" and stack:
            stack.pop()
        out.append(s)
        i += 1
    return "".join(out), replaced, kept


def main(argv):
    if argv[:1] == ["--stats"]:
        tot_r = tot_k = 0
        for f in argv[1:]:
            _, r, k = interface(pathlib.Path(f).read_text())
            tot_r += r
            tot_k += k
            print(f"{r:5d} replaced {k:5d} kept {f}")
        print(f"{tot_r:5d} replaced {tot_k:5d} kept total")
        return 0
    if argv[:1] == ["--tree"]:
        # DST/replaced lists "path replaced" for every file, the number of
        # proofs its interface replaces.
        src, dst = pathlib.Path(argv[1]), pathlib.Path(argv[2])
        counts = []
        for f in sorted(src.rglob("*.v")):
            t = dst / f.relative_to(src)
            t.parent.mkdir(parents=True, exist_ok=True)
            text, replaced, _ = interface(f.read_text())
            t.write_text(text)
            counts.append(f"{f.relative_to(src).with_suffix('')} {replaced}\n")
        (dst / "replaced").write_text("".join(counts))
        return 0
    src, dst = argv
    pathlib.Path(dst).write_text(interface(pathlib.Path(src).read_text())[0])
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
