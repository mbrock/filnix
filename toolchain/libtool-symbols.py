"""Adapt libtool's symbol probes to the Fil-C ABI without changing nm output.

Only pizlonated_<name> entries can be referenced by generated C declarations.
The FI/FIP direct-call entry points, ET thunks, and native runtime symbols are
not separate C identifiers. Libtool keeps the raw name and C name in separate
columns; its usual C declaration and export-list machinery then works unchanged.
"""

import os
import sys
from pathlib import Path

# Libtool already models a platform prefix separately from the C identifier.
# Select Fil-C's prefix instead of trying the ELF/Mach-O defaults. This leaves
# the normal probe enabled and its raw-symbol and C-name columns distinct.
marker = 'for ac_symprfx in "" "_"; do'
replacement = 'for ac_symprfx in "pizlonated_"; do'

paths = set(Path(".").rglob("configure"))
# A package's preConfigure can move into a separate build directory.
if len(sys.argv) > 1 and sys.argv[1]:
    configure = Path(sys.argv[1])
    paths.add(configure)
    paths.update(configure.parent.rglob("configure"))

for path in sorted(paths):
    if not path.is_file():
        continue
    text = path.read_text(errors="surrogateescape")
    if marker not in text:
        continue

    original = text
    text = text.replace(marker, replacement)

    if text != original:
        stat = path.stat()
        path.write_text(text, errors="surrogateescape")
        # Do not trigger make's automatic regeneration of configure.
        os.utime(path, ns=(stat.st_atime_ns, stat.st_mtime_ns))
        print(f"Fil-C: adapting libtool symbol probes in {path}")
