"""Build just the interfaces imported by an rq session, using Rocq's dependency rules."""
import fcntl
import hashlib
import os
import re
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time


def prepare(tree, file, model):
    tree, file, model = map(Path, (tree, file, model))
    model = model.resolve()
    namespace = "Nanofil" if tree == model else "Glibc"
    # Keep interfaces separate from full objects and from other toolchains.
    binary = shutil.which("rocq")
    if binary is None:
        raise FileNotFoundError("rocq is missing from PATH")
    compiler = Path(binary).resolve()
    identity = (tree, model, compiler, os.environ.get("ROCQPATH", ""))
    key = hashlib.sha256(os.fsencode(repr(identity))).hexdigest()[:24]
    cache = Path(os.environ["PE_CACHE"]).resolve() / "rq-interfaces"
    work = cache / key
    work.mkdir(parents=True, exist_ok=True)
    roots = {"Nanofil": model}
    if namespace == "Glibc":
        roots["Glibc"] = tree
    build_flags = []
    worker_flags = ["-q"]
    sources = []
    with (work / "build.lock").open("a") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print(f"rq: waiting for the interface build in {work}", file=sys.stderr)
            fcntl.flock(lock, fcntl.LOCK_EX)
        for name, root in roots.items():
            if root.is_relative_to("/nix/store"):
                build_flags.extend(["-R", str(root), name])
                worker_flags.extend(["-R", str(root), name])
                continue
            mirror = work / name
            mirror.mkdir(exist_ok=True)
            build_flags.extend(["-R", name, name])
            worker_flags.extend(["-R", str(mirror), name])
            for src in root.rglob("*.v"):
                if src.is_relative_to(cache):
                    continue
                dest = mirror / src.relative_to(root)
                if not dest.is_symlink():
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    dest.symlink_to(src)
                sources.append(str(dest.relative_to(work)))
            for dest in mirror.rglob("*.v"):
                if not dest.exists():
                    dest.unlink()
                    dest.with_suffix(".vos").unlink(missing_ok=True)
        deps = subprocess.run(["rocq", "dep", "-vos", *build_flags, *sources],
                              cwd=work, check=True, stdout=subprocess.PIPE, text=True)
        # The pinned model ships full .vo files. Its inputs are immutable
        # and its store path is part of the cache key.
        rules = [re.sub(r"(/nix/store/[^ ]+)\.vos(?= |$)", r"\1.vo", line)
                 for line in deps.stdout.splitlines() if line.split(" ", 1)[0].endswith(".vos")]
        target = Path(namespace) / file.relative_to(tree).with_suffix(".required_vos")
        compile_vos = shlex.join(["rocq", "c", "-q", "-vos", *build_flags])
        recipe = f'\t@{compile_vos} "$<" > "$@.log" 2>&1 || {{ cat "$@.log" >&2; exit 1; }}'
        makefile = "\n".join([".DELETE_ON_ERROR:", "%.vos: %.v", recipe, *rules, ""])
        (work / "Makefile").write_text(makefile)
        command = ["make", "--no-print-directory", "-s", "-j", os.getenv("RQ_JOBS", "8"), str(target)]
        start = time.monotonic()
        with subprocess.Popen(command, cwd=work, stdout=sys.stderr) as build:
            while True:
                try:
                    status = build.wait(timeout=15)
                    break
                except subprocess.TimeoutExpired:
                    logs = work.rglob("*.vos.log")
                    latest = max(logs, key=lambda p: p.stat().st_mtime_ns, default=None)
                    detail = f"; latest compiler log {latest.relative_to(work)}" if latest else ""
                    print(f"rq: building imports for {file.name} ({time.monotonic() - start:.0f}s){detail}",
                          file=sys.stderr, flush=True)
        if status:
            raise subprocess.CalledProcessError(status, command)
    return worker_flags
