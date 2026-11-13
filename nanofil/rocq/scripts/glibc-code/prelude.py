"""Replace repeated generated helpers by imports of CodePrelude."""
import re


CHR = re.compile(
    r"\(\*\* (?:The one-character atom with code n\.|Character atoms retain their byte values\.|"
    r"This helper constructs the atom containing one character with code n\.) \*\)\n"
    r"Definition chr \(n : nat\) : term := TAtom \(String \(ascii_of_nat n\) EmptyString\)\.\n\n")
MODULE = re.compile(
    r"(Definition \w+ : module := Eval vm_compute in\n)"
    r"  match decode_module (\w+) with Some md => md \| None => \[\] end\.")
FUNCTION = re.compile(
    r"(Definition \w+ \(n : string\) : func :=\n)"
    r"  match find_direct \(TAtom n\) (\w+) with\n"
    r"  \| Some \(Defined f\) => f\n"
    r'  \| _ => mkFunc \(TAtom n\) \(TAtom "export"\) \(RClass W\) \[\] \[\]\n'
    r"  end\.")


def shared(text):
    """Preserve terms and statements; factor only the generated helper bodies."""
    if "From Glibc Require Import CodePrelude." in text:
        return text
    if "Definition chr (n : nat)" not in text:
        # The two Term files only concatenate slices; they define no helpers.
        return text
    text, count = CHR.subn("", text)
    if count != 1:
        raise ValueError("unrecognized generated chr definition")
    old = "From Nanofil Require Import Term.\n"
    if text.count(old) != 1:
        raise ValueError("expected exactly one generated Term import")
    text = text.replace(old, "From Glibc Require Import CodePrelude.\n")
    text = MODULE.sub(r"\1  code_module \2.", text)
    text = FUNCTION.sub(r"\1  code_function \2 n.", text)
    if "match decode_module" in text or "match find_direct" in text:
        raise ValueError("unrecognized generated decoding helper")
    return text
