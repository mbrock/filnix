"""Build just the interfaces imported by an rq session, using Rocq's dependency rules."""
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import fcntl
import heapq
import hashlib
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


# The in-process worker needs the same warning policy as the Nanofil Rocq CLI.
SESSION_FLAGS = ("-q", "-w", "-rewrite-rw")


def build_imports(work, rules, target, flags, lock):
    # Make decides freshness, including loaded source files and external objects.
    # Each dry-run recipe lists one stale interface and its direct interfaces.
    makefile = "\n".join(["%.vos: %.v", "\t@$@ : $(filter %.vos,$^)", *rules, ""])
    plan = subprocess.run(["make", "-ns", "-j1", "--no-print-directory", "-f", "-", str(target)],
                          cwd=work, input=makefile, check=True,
                          stdout=subprocess.PIPE, text=True)
    graph = {}
    for line in plan.stdout.splitlines():
        name, _, inputs = line.partition(" :")
        graph[name] = inputs.split()
    if not graph:
        return

    # Make prints prerequisites before dependents. Walking its plan backwards
    # gives each job the length of the longest unfinished chain it can unblock.
    users = {name: [] for name in graph}
    remaining = dict.fromkeys(graph, 0)
    depth = dict.fromkeys(graph, 1)
    for name in reversed(graph):
        for dep in graph[name]:
            if dep in graph:
                users[dep].append(name)
                remaining[name] += 1
                depth[dep] = max(depth[dep], depth[name] + 1)

    def compile_one(name):
        dest = work / name
        log = work / (name + ".log")
        # Publish only complete objects. Inherit the build lock in case rq
        # exits while a compiler is still using this mirror.
        with tempfile.TemporaryDirectory(dir=work) as tmp:
            staged = Path(tmp) / dest.name
            logical_parent = ".".join(Path(name).parent.parts)
            args = ["rocq", "c", "-q", "-vos", *flags, "-Q", tmp, logical_parent, "-o", str(staged),
                    str(Path(name).with_suffix(".v"))]
            with log.open("wb") as stream:
                result = subprocess.run(args, cwd=work, stdout=stream, stderr=subprocess.STDOUT,
                                        pass_fds=(lock.fileno(),))
            if result.returncode:
                sys.stderr.write(log.read_text(errors="replace"))
                result.check_returncode()
            staged.replace(dest)

    try:
        jobs = int(os.getenv("RQ_JOBS", "8"))
        if jobs < 1:
            raise ValueError()
    except ValueError:
        raise OSError("RQ_JOBS must be a positive integer") from None
    ready = [(-depth[name], name) for name in graph if not remaining[name]]
    heapq.heapify(ready)
    active = {}
    start = time.monotonic()
    report = start + 15
    with ThreadPoolExecutor(max_workers=min(jobs, len(graph))) as pool:
        while ready or active:
            while ready and len(active) < jobs:
                _, name = heapq.heappop(ready)
                active[pool.submit(compile_one, name)] = name
            done, _ = wait(active, timeout=max(0, report - time.monotonic()),
                           return_when=FIRST_COMPLETED)
            for task in done:
                name = active.pop(task)
                task.result()
                for user in users[name]:
                    remaining[user] -= 1
                    if not remaining[user]:
                        heapq.heappush(ready, (-depth[user], user))
            now = time.monotonic()
            if now >= report and active:
                print(f"rq: building imports for {target.stem}.v ({now - start:.0f}s); "
                      f"compiling {next(iter(active.values()))}", file=sys.stderr, flush=True)
                report = now + 15


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
    worker_flags = list(SESSION_FLAGS)
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
        build_imports(work, rules, target, build_flags, lock)
    return worker_flags
