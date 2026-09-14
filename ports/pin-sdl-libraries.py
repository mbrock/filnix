"""Resolve SDL's configured dlopen backends within its Nix dependencies."""
from pathlib import Path
import re
import sys

header = Path(sys.argv[1])
search = [Path(directory) for directory in sys.argv[2:]]


def pin(match):
    definition, soname = match.groups()
    for directory in search:
        library = directory / soname
        if library.is_file():
            return f'{definition}"{library}"'
    raise SystemExit(f"No declared SDL dependency supplies {soname}")


header.write_text(re.sub(
    r'^(#define SDL_\w*DYNAMIC\w*\s+)"(lib[^"/]+\.so(?:\.[0-9]+)*)"',
    pin, header.read_text(), flags=re.MULTILINE,
))
