"""Readable Nix evaluation errors, derived without changing the raw observation."""

import re


def evaluation_summary(message):
    # Nix prints warnings and an evaluation trace before its final `error:`.
    # Only use a nonempty error line; a lone warning must remain visible.
    text = re.sub(r"\x1b\[[0-?]*[ -/]*[@-~]", "", message or "")
    errors = list(re.finditer(r"(?m)^[ \t]*error:[ \t]*(?=[^\s])", text))
    if not errors:
        return text[:500]
    diagnostic = text[errors[-1].end() :].strip()
    paragraph = re.split(r"\n[ \t]*\n", diagnostic, maxsplit=1)[0]
    # The full source location remains in the diagnostic. Its store hash can
    # otherwise hide the refusal reason in a narrow package row.
    paragraph = re.sub(
        r"^(Package [‘'][^’']+[’']) in /nix/store/\S+ (?=is |has )",
        r"\1 ",
        paragraph,
    )
    return paragraph[:500]
