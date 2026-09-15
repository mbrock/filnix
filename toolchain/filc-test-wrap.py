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
    renames = []
    for line in symbols.splitlines():
        if not line.strip():
            continue
        symbol = line.split()[0]
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
