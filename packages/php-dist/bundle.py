"""Copy Fil-C ELF programs and modules into a relocatable tree.

usage: bundle.py OUT LOADER [DEST=SOURCE]...

Each DEST is relative to OUT and lands in libexec/ (programs) or under lib/
(modules). Every shared library they need, resolved through the RUNPATHs
recorded in the Nix store, is copied flat into OUT/lib, and all RUNPATHs
are rewritten relative to $ORIGIN so the tree can live anywhere.
"""

import filecmp
import os
import shutil
import subprocess
import sys


def patchelf(*args):
    return subprocess.run(
        ["patchelf", *args], check=True, capture_output=True, text=True
    ).stdout.split()


def deps(path):
    """Yield (soname, resolved path) for each DT_NEEDED entry of path."""
    origin = os.path.dirname(os.path.realpath(path))
    (rpath,) = patchelf("--print-rpath", path) or [""]
    dirs = [d.replace("$ORIGIN", origin) for d in rpath.split(":") if d]
    for soname in patchelf("--print-needed", path):
        for d in dirs:
            candidate = os.path.join(d, soname)
            if os.path.exists(candidate):
                yield soname, os.path.realpath(candidate)
                break
        else:
            # Some runtime libraries have no RUNPATH and rely on the
            # program having loaded the library already; main checks that.
            yield soname, None


def main():
    out, loader, *items = sys.argv[1:]
    lib = os.path.join(out, "lib")
    os.makedirs(lib, exist_ok=True)

    sources = {}  # soname -> store path, to catch two libraries sharing one
    todo = []
    for item in items:
        dest, src = item.split("=", 1)
        dest = os.path.join(out, dest)
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        shutil.copyfile(src, dest)
        todo.append((dest, src))

    copied = []
    unresolved = []
    while todo:
        dest, src = todo.pop()
        copied.append(dest)
        for soname, real in deps(src):
            if real is None:
                unresolved.append((src, soname))
                continue
            if soname in sources:
                # The loader also keeps one library per soname in a process,
                # so a closure with two builds of one library already ran
                # with whichever loaded first.
                if not filecmp.cmp(sources[soname], real, shallow=False):
                    print(f"warning: {soname}: using {sources[soname]}, not {real}")
                continue
            sources[soname] = real
            target = os.path.join(lib, soname)
            shutil.copyfile(real, target)
            todo.append((target, real))

    for src, soname in unresolved:
        if soname not in sources:
            sys.exit(f"{src}: cannot resolve {soname}")

    loader_copy = os.path.join(lib, os.path.basename(loader))
    shutil.copyfile(loader, loader_copy)

    for path in copied:
        os.chmod(path, 0o755)
        # The loader relocates itself and must not be rewritten.
        if path == loader_copy:
            continue
        rel = os.path.relpath(lib, os.path.dirname(path))
        patchelf("--set-rpath", "$ORIGIN" if rel == "." else f"$ORIGIN/{rel}", path)
        # The bundled loader is started explicitly, but keep PT_INTERP
        # pointing at a name that cannot accidentally resolve to /nix.
        if path.startswith(os.path.join(out, "libexec")):
            patchelf("--set-interpreter", "/lib64/ld-fil1-x86_64.so", path)

    for soname, real in sorted(sources.items()):
        print(f"{soname} <- {real}")


main()
