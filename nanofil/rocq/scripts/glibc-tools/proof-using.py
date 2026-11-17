#!/usr/bin/env python3
"""Give each Qed proof inside a Section the Proof using clause that Rocq
infers for it, so that tests/rocq_interface.py can replace the proof in
the file's interface.

Rocq adds to a section lemma's type the section variables that its proof
uses. Without a Proof using clause only the proof script says which ones,
so the interface has to keep the proof, and an edit to it recompiles every
importer. With "Set Suggest Proof Using", Rocq prints, for each such
proof, the clauses that name exactly the variables it inferred. Every
clause it prints gives the lemma the type it has now, so this script
picks the shortest one: "Type*" or "Type" when Rocq offers it, the list
of names otherwise. It changes no statement and no proof script.

    proof-using.py FILE.v LOG     # LOG: rocq c -set "Suggest Proof Using" output

A proof that starts with "Proof." gets "Proof using CLAUSE.", one that
starts with "Proof with TAC." gets "Proof using CLAUSE with TAC.", and one
without a Proof command gets "Proof using CLAUSE." after its statement.
The script matches Rocq's suggestions to the proofs by name, in order,
and leaves alone any proof that has no suggestion.
"""
import re
import sys

SUGGESTION = re.compile(
    r"^The proof of (\S+) should start with one of the following commands:\n((?:Proof using[^\n]*\n)+)",
    re.M,
)


def suggestions(log):
    out = []
    for m in SUGGESTION.finditer(log):
        clauses = [
            l[len("Proof using") :].strip().rstrip(".").strip()
            for l in m[2].splitlines()
        ]
        out.append((m[1].rsplit(".", 1)[-1], clauses))
    return out


def pick(clauses):
    for c in ("Type*", "Type"):
        if c in clauses:
            return c
    return min(clauses, key=len)


def spans(text):
    """Return (start, end) of each sentence in text, skipping comments and
    strings: a sentence ends at a dot followed by white space or the end
    of the text, not part of "..". Comments between sentences belong to
    no span."""
    out, i, n, start = [], 0, len(text), None
    while i < n:
        if text.startswith("(*", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("(*", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("*)", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            continue
        c = text[i]
        if start is None:
            if c.isspace():
                i += 1
                continue
            start = i
        if c == '"':
            i += 1
            while i < n:
                if text[i] == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        i += 2
                        continue
                    break
                i += 1
            i += 1
            continue
        if c == "." and (i + 1 == n or text[i + 1].isspace()) and not (text[i - 1 : i + 1] == ".." and text[i - 2 : i - 1] != "."):
            out.append((start, i + 1))
            start = None
        i += 1
    return out


LEAD = re.compile(r"^[\s{}\-+*]*")
STATEMENT = {
    "Lemma", "Theorem", "Fact", "Remark", "Corollary", "Proposition",
    "Instance", "Definition", "Example", "Let", "Fixpoint", "Property",
}
DEFINITION = {"Instance", "Definition", "Example", "Let", "Fixpoint"}
PREFIX = {"Local", "Global", "Program", "Polymorphic", "Monomorphic", "#[global]", "#[local]", "#[export]"}


def declared(words):
    """The name a statement sentence declares, or None."""
    i = 0
    while i < len(words) and (words[i] in PREFIX or words[i].startswith("#[")):
        i += 1
    if i + 1 < len(words) and words[i] in STATEMENT:
        name = words[i + 1].rstrip(":")
        return name if name and name not in (":", "{", "`{") else None
    return None


def rewrite(text, sugg):
    ss = spans(text)
    words = [LEAD.sub("", text[a:b]).split() for a, b in ss]
    edits, stack, k, i = [], [], 0, 0
    pending = list(sugg)
    while i < len(ss):
        w = words[i]
        head = w[0] if w else ""
        if head == "Section" and len(w) > 1:
            stack.append("S")
        elif head == "Module" and ":=" not in text[ss[i][0] : ss[i][1]]:
            stack.append("M")
        elif head == "End" and stack:
            stack.pop()
        # A definition's body follows :=, but a lemma's statement can hold
        # one too, as in let n := e or <[k := v]>.
        name = declared(w)
        kw = next((x for x in w if x not in PREFIX and not x.startswith("#[")), "")
        if name and kw in DEFINITION and ":=" in text[ss[i][0] : ss[i][1]]:
            name = None
        if name and "S" in stack and pending and pending[0][0] == name and i + 1 < len(ss):
            # The proof's first sentence, and its end.
            j = i + 1
            while j < len(ss) and not (words[j] and words[j][-1] in ("Qed.", "Defined.", "Admitted.", "Abort.")):
                j += 1
            if j < len(ss) and words[j] == ["Qed."]:
                clause = pick(pending.pop(0)[1])
                a, b = ss[i + 1]
                first = words[i + 1]
                if first == ["Proof."]:
                    edits.append((a, b, f"Proof using {clause}."))
                elif first[:2] == ["Proof", "with"]:
                    edits.append((a, a + len("Proof"), f"Proof using {clause}"))
                elif first[:1] != ["Proof"]:
                    indent = text[text.rfind("\n", 0, a) + 1 : a]
                    edits.append((a, a, f"Proof using {clause}.\n{indent}"))
                k += 1
            i = j + 1
            continue
        i += 1
    for a, b, s in sorted(edits, reverse=True):
        text = text[:a] + s + text[b:]
    return text, k, pending


def main(argv):
    path, log = argv
    text = open(path).read()
    sugg = suggestions(open(log).read())
    new, done, left = rewrite(text, sugg)
    if left:
        print(f"proof-using: {path}: {len(left)} suggestions matched no proof: {[n for n, _ in left]}", file=sys.stderr)
        return 1
    if new != text:
        open(path, "w").write(new)
    print(f"{done:4d} clauses {path}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
