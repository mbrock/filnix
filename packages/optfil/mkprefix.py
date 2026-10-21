"""Turn a Nix closure into a tree that runs from a fixed prefix.

usage: mkprefix.py OUT PREFIX CLOSURE [--merge PATH...] [--alias PATH...]
                   [--relative-links]

CLOSURE lists store paths, one per line (closureInfo's store-paths). OUT
becomes the tree that is to be installed at PREFIX:

- Each --merge path is copied into OUT itself, in the order given; a file
  that an earlier path already provided is skipped, with a warning when the
  two differ. References to the path become PREFIX.
- Each --alias path is not copied, but references to it also become PREFIX:
  the merged paths provide the files under it that are needed.
- Every other path is copied to OUT/s/HASH-NAME, and references to it
  become PREFIX/s/HASH-NAME. When PREFIX/s/ is longer than /nix/store/, the
  hash is shortened by the difference.

References are rewritten in the bytes of every file, so they also change
inside ELF interpreters and RUNPATHs, scripts and compiled-in strings. A
replacement must not change the length of the bytes: PREFIX/s/HASH-NAME has
as many characters as /nix/store/HASH-NAME, and PREFIX is padded with
slashes to the length of the store path it replaces, which names the same
directory.

Symlinks to store paths point to PREFIX, or with --relative-links to the
same file inside OUT by a relative path.
"""

import argparse
import filecmp
import hashlib
import os
import re
import shutil
import stat
import sys

STORE = "/nix/store/"
# Documentation is left out, and nix-support only matters to Nix builds.
SKIP = {"nix-support", "share/man", "share/doc", "share/info", "share/gtk-doc"}
REF = re.compile(rb"/nix/store/([0-9a-df-np-sv-z]{32})-")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("out")
    ap.add_argument("prefix")
    ap.add_argument("closure")
    ap.add_argument("--merge", nargs="*", default=[])
    ap.add_argument("--alias", nargs="*", default=[])
    ap.add_argument("--relative-links", action="store_true")
    args = ap.parse_args()

    prefix = args.prefix.rstrip("/")
    store_dir = prefix + "/s/"
    # Characters to drop from each hash; 20 of 32 keep collisions unlikely.
    cut = len(store_dir) - len(STORE)
    if not 0 <= cut <= 12:
        sys.exit(f"{store_dir} must be at most 12 characters longer than {STORE}")

    closure = open(args.closure).read().split()
    flat = args.merge + args.alias
    for path in flat:
        if path not in closure or not os.path.isdir(path):
            sys.exit(f"{path}: not a directory in the closure")

    # hash -> (store path, replacement); flat replacements get padded.
    targets = {}
    names = {}  # store path -> its directory in OUT/s
    for path in closure:
        base = os.path.basename(path)
        names[path] = base[: 32 - cut] + base[32:]
        repl = prefix if path in flat else store_dir + names[path]
        targets[base[:32].encode()] = (path.encode(), repl.encode())
    if len(set(names.values())) != len(names):
        sys.exit("shortened store path names collide")

    def relink(target, dest):
        if not target.startswith(STORE):
            return target
        path, repl = targets[target[len(STORE) : len(STORE) + 32].encode()]
        new = repl.decode() + target[len(path) :]  # unpadded
        if not args.relative_links:
            return new
        inside = os.path.join(args.out, os.path.relpath(new, prefix))
        return os.path.relpath(inside, os.path.dirname(dest))

    copier = Copier(relink)
    for path in args.merge:
        copier.copy(path, args.out)
    for path in closure:
        if path not in flat:
            copier.copy(path, os.path.join(args.out, "s", names[path]))

    unknown = {}
    for dest in copier.files:
        rewrite(dest, targets, unknown)

    for (kept, skipped), files in sorted(copier.conflicts.items()):
        print(f"warning: {len(files)} files of {skipped} lost to {kept}, e.g. {files[0]}")
    for ref, files in sorted(unknown.items()):
        print(f"warning: unknown reference {ref} in {len(files)} files, e.g. {files[0]}")


class Copier:
    def __init__(self, relink):
        self.relink = relink
        self.files = []  # regular files to rewrite, once per inode
        self.copies = {}  # (mode, digest) of a file -> its first copy
        self.owner = {}  # merged destination -> store path it came from
        self.conflicts = {}

    def copy(self, src, dest, origin=None, rel=""):
        origin = origin or src
        if os.path.islink(src) or not os.path.isdir(src):
            self.file(src, dest, origin)
            return
        if os.path.lexists(dest) and not (
            os.path.isdir(dest) and not os.path.islink(dest)
        ):
            # Never write through a symlink, which may point out of OUT.
            self.conflict(dest, origin)
            return
        os.makedirs(dest, exist_ok=True)
        self.owner.setdefault(dest, origin)
        for name in sorted(os.listdir(src)):
            sub = os.path.join(rel, name)
            if sub not in SKIP:
                self.copy(os.path.join(src, name), os.path.join(dest, name), origin, sub)

    def conflict(self, dest, origin):
        key = (self.owner.get(dest, "?"), origin)
        self.conflicts.setdefault(key, []).append(dest)

    def file(self, src, dest, origin):
        if os.path.lexists(dest):
            if not same(src, dest, lambda t: self.relink(t, dest)):
                self.conflict(dest, origin)
            return
        self.owner[dest] = origin
        st = os.lstat(src)
        if stat.S_ISLNK(st.st_mode):
            os.symlink(self.relink(os.readlink(src), dest), dest)
            return
        # Files with the same bytes stay the same after rewriting, so they
        # can share one inode.
        mode = (st.st_mode & 0o555) | 0o200
        with open(src, "rb") as f:
            key = (mode, hashlib.file_digest(f, "sha256").digest())
        if key in self.copies:
            os.link(self.copies[key], dest)
            return
        shutil.copyfile(src, dest)
        os.chmod(dest, mode)
        self.copies[key] = dest
        self.files.append(dest)


def same(src, dest, relink):
    if os.path.islink(src) or os.path.islink(dest):
        return (
            os.path.islink(src)
            and os.path.islink(dest)
            and relink(os.readlink(src)) == os.readlink(dest)
        )
    # Files are rewritten only after everything is copied.
    return not os.path.isdir(dest) and filecmp.cmp(src, dest, shallow=False)


def rewrite(dest, targets, unknown):
    with open(dest, "rb") as f:
        data = f.read()
    if b"/nix/store/" not in data:
        return
    out = bytearray()
    pos = 0
    for m in REF.finditer(data):
        if m.start() < pos:
            continue
        found = targets.get(m.group(1))
        if found is None or not data.startswith(found[0], m.start()):
            unknown.setdefault(data[m.start() : m.end() + 16].decode(errors="replace"), []).append(dest)
            continue
        path, repl = found
        out += data[pos : m.start()]
        out += repl.ljust(len(path), b"/") if len(repl) < len(path) else repl[: len(path)]
        pos = m.start() + len(path)
    if pos:
        out += data[pos:]
        assert len(out) == len(data)
        with open(dest, "wb") as f:
            f.write(out)


main()
