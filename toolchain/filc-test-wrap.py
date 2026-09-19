"""Adapt GNU ld test wrappers to Fil-C's symbol names, within one package.

Invoke as CC with FILNIX_WRAP_CC, FILNIX_WRAP_NM and FILNIX_WRAP_OBJCOPY set.
Only separate -c compilation is rewritten; test links then wrap the Fil-C
function descriptors, leaving the runtime's native libc calls untouched.
"""

import os
from pathlib import Path
import re
import shlex
import subprocess
import sys


def main():
    args = sys.argv[1:]
    command = shlex.split(os.environ["FILNIX_WRAP_CC"])
    flags = [
        re.sub(r"--wrap=([A-Za-z_][A-Za-z_0-9]*)", r"--wrap=pizlonated_\1", arg)
        for arg in args
    ]
    result = subprocess.run(command + flags)
    if result.returncode:
        return result.returncode
    if "-c" not in args:
        return 0
    if "-o" in args:
        output = args[args.index("-o") + 1]
    else:
        sources = [arg for arg in args if arg.endswith((".c", ".cc", ".cpp", ".cxx"))]
        if len(sources) != 1:
            raise ValueError("test wrapper requires one source or an explicit -o")
        output = Path(sources[0]).with_suffix(".o").name
    if not Path(output).is_file():
        return 0
    symbols = subprocess.check_output(
        [os.environ["FILNIX_WRAP_NM"], "--format=posix", "--no-demangle", output],
        text=True,
    )
    entries = [line.split() for line in symbols.splitlines() if line.strip()]
    undefined = {entry[0] for entry in entries if entry[1] == "U"}
    renames = []
    for symbol, kind, *_ in entries:
        # An external call has a weak direct-call thunk that loads its
        # descriptor. If the real function is linked from another object,
        # its strong entry point would replace this thunk and bypass --wrap.
        # Keep the caller's thunk local so it uses the wrapped descriptor.
        thunk = re.fullmatch(r"pizlonatedFI[0-9]+_(.+)", symbol)
        if kind == "W" and thunk and f"pizlonated_{thunk[1]}" in undefined:
            renames += ["--localize-symbol", symbol]
        # Fil-C lowers malloc/free directly to runtime operations, even with
        # -fno-builtin. Tests may compile with -Dmalloc=filnix_wrap_malloc
        # (and likewise free) to keep real, interposable function calls.
        # Restore the libc descriptor name only after compilation.
        if symbol in {"pizlonated_filnix_wrap_malloc", "pizlonated_filnix_wrap_free"}:
            renames += ["--redefine-sym", f"{symbol}={symbol.replace('filnix_wrap_', '')}"]
        match = re.fullmatch(
            r"pizlonated___(wrap|real)_([A-Za-z_][A-Za-z_0-9]*)", symbol
        )
        if match:
            kind, name = match.groups()
            renames += ["--redefine-sym", f"{symbol}=__{kind}_pizlonated_{name}"]
    if renames:
        subprocess.run(
            [os.environ["FILNIX_WRAP_OBJCOPY"], *renames, output], check=True
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
