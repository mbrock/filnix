# Put back the .note.dlopen ELF notes (https://systemd.io/ELF_DLOPEN_METADATA/)
# that the Fil-C compiler drops: it ignores section() on globals, so the
# notes' JSON payloads end up as ordinary data. Find each payload in an ELF
# file and add it again as a .note.dlopen section, so tools that read the
# notes (make-initrd-ng, autoPatchelf) see them.
#
# Usage: restore-dlopen-notes.py OBJCOPY DIR...
import json
import os
import re
import struct
import subprocess
import sys
import tempfile

NT_FDO_DLOPEN = 0x407C0C0A
PAYLOAD = re.compile(rb'\[\{"feature":.*?\}\](?=\x00)')


def pad4(b):
    return b + b"\0" * (-len(b) % 4)


def note(payload):
    owner = b"FDO\0"
    desc = payload + b"\0"
    return struct.pack("<III", len(owner), len(desc), NT_FDO_DLOPEN) + pad4(owner) + pad4(desc)


def restore(objcopy, path):
    with open(path, "rb") as f:
        data = f.read()
    if not data.startswith(b"\x7fELF") or b".note.dlopen" in data:
        return
    payloads = []
    for m in PAYLOAD.finditer(data):
        try:
            json.loads(m.group())
        except ValueError:
            continue
        if m.group() not in payloads:
            payloads.append(m.group())
    if not payloads:
        return
    with tempfile.NamedTemporaryFile() as section:
        section.write(b"".join(note(p) for p in payloads))
        section.flush()
        subprocess.run(
            [objcopy, "--add-section", f".note.dlopen={section.name}",
             "--set-section-flags", ".note.dlopen=readonly", path],
            check=True,
        )
    print(f"restore-dlopen-notes: {len(payloads)} notes in {path}")


objcopy, *dirs = sys.argv[1:]
for d in dirs:
    for root, _, files in os.walk(d):
        for name in files:
            path = os.path.join(root, name)
            if os.path.isfile(path) and not os.path.islink(path):
                restore(objcopy, path)
