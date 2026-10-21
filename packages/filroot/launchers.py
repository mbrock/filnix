"""Put launchers in front of the programs of a relocatable Fil-C root.

usage: launchers.py ROOT LAUNCHER

Each program in ROOT/bin and ROOT/sbin that needs ROOT open as descriptor
987, an ELF file with an interpreter or a script with #!, moves to
ROOT/libexec/filroot/DIR/NAME, or a symlink to it is put there, and
ROOT/DIR/NAME becomes a hard link to ROOT/libexec/filroot/launcher. Links
to other entries of the same directory stay as they are.
"""

import os
import shutil
import struct
import sys

PT_INTERP = 3


def needs_root(path):
    with open(path, "rb") as f:
        head = f.read(64)
        if head.startswith(b"#!"):
            return True
        if not head.startswith(b"\x7fELF\x02\x01"):
            return False
        phoff, = struct.unpack_from("<Q", head, 32)
        phentsize, phnum = struct.unpack_from("<HH", head, 54)
        f.seek(phoff)
        table = f.read(phentsize * phnum)
    return any(
        struct.unpack_from("<I", table, i * phentsize)[0] == PT_INTERP
        for i in range(phnum)
    )


def main():
    root, launcher = sys.argv[1:]
    real_root = os.path.join(root, "libexec", "filroot")
    os.makedirs(real_root, exist_ok=True)
    copy = os.path.join(real_root, "launcher")
    shutil.copyfile(launcher, copy)
    os.chmod(copy, 0o555)

    for dirname in ["bin", "sbin"]:
        d = os.path.join(root, dirname)
        if not os.path.isdir(d):
            continue
        real_dir = os.path.join(real_root, dirname)
        os.makedirs(real_dir, exist_ok=True)
        for name in sorted(os.listdir(d)):
            path = os.path.join(d, name)
            final = os.path.realpath(path)
            if os.path.islink(path) and os.path.dirname(final) == os.path.realpath(d):
                continue
            if not os.path.isfile(final) or not needs_root(final):
                continue
            real = os.path.join(real_dir, name)
            if os.path.islink(path):
                os.symlink(os.path.relpath(final, real_dir), real)
            else:
                os.rename(path, real)
            if os.path.lexists(path):
                os.unlink(path)
            os.link(copy, path)
        if dirname == "bin":
            os.link(copy, os.path.join(d, "fil-run"))


main()
