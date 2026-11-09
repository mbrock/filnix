#!/usr/bin/env python3
"""Capture real Rocq states for dterm; no browser prover or inferred goals.

python3 capture.py PROJECT OUTPUT.json [--replay PREFIX]
Needs coqc, coqidetop, swipl and the project's Stdlib on ROCQPATH.
Compiles dependencies and replays commands in an isolated writable copy,
as a dependency graph over the available cores: a file's replay starts as
soon as its imports are compiled, and only imported files are compiled at
all, since a replay already executes and checks every command of its file.
The bundled RocqIDE XML protocol is pinned by the site's Rocq package.
Run under tests/watch.py for deadlines and 15-second progress reporting.
--replay replays only the files under PREFIX (the logic spikes), and
compiles the rest of the project only as they import it.
"""
import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import tempfile
import time
import xml.etree.ElementTree as ET
from xml.sax.saxutils import escape


def stamp(message):
    print(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), message, flush=True)


def pair(a, b):
    return f"<pair>{a}{b}</pair>"


def integer(n):
    return f"<int>{n}</int>"


def plain(node):
    return "".join(node.itertext())


class Prover:
    def __init__(self, cwd, flags, log):
        self.proc = subprocess.Popen(
            ["coqidetop", "-main-channel", "stdfds", "-async-proofs", "off", *flags],
            cwd=cwd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=log,
        )
        self.parser = ET.XMLPullParser(events=("end",))
        # Rocq's richpp uses &nbsp; for an ordinary pretty-printer space.
        self.parser.feed('<!DOCTYPE stream [<!ENTITY nbsp " ">]><stream>')
        self.state = self.call("Init", '<option val="none"/>')[0].attrib["val"]

    def call(self, name, body):
        self.proc.stdin.write(f'<call val="{name}">{body}</call>\n'.encode())
        self.proc.stdin.flush()
        while True:
            chunk = os.read(self.proc.stdout.fileno(), 65536)
            if not chunk:
                raise RuntimeError(f"RocqIDE exited during {name}")
            self.parser.feed(chunk)
            for _, node in self.parser.read_events():
                if node.tag == "value":
                    if node.attrib["val"] != "good":
                        raise RuntimeError(f"Rocq {name}: {plain(node)}")
                    # Detach the response; discard processed feedback too.
                    result = ET.fromstring(ET.tostring(node))
                    node.clear()
                    return result
                if node.tag == "feedback":
                    node.clear()

    def add(self, command):
        text = f"<string>{escape(command)}</string>"
        sid = f'<state_id val="{self.state}"/>'
        body = pair(pair(pair(pair(text, integer(-1)), pair(sid, '<bool val="false"/>')),
                         integer(0)), pair(integer(1), integer(0)))
        response = self.call("Add", body)
        self.state = response.find("./pair/state_id").attrib["val"]
        # Status forces execution, including commands outside proof mode
        # and Qed; an accepted Add alone does not establish success.
        self.call("Status", '<bool val="true"/>')

    def goals(self):
        response = self.call("Goal", "<unit/>")
        goals = response.find("./option/goals")
        if goals is None:
            return None

        def goal(g, role):
            return {"id": plain(g[0]), "hypotheses": [plain(h) for h in g[1]],
                    "conclusion": plain(g[2]), "role": role}

        result = [goal(g, "focused") for g in goals[0]]
        for frame in goals[1]:
            for side in frame:
                result.extend(goal(g, "deferred") for g in side)
        result.extend(goal(g, "shelved") for g in goals[2])
        result.extend(goal(g, "given up") for g in goals[3])
        return result

    def close(self):
        self.proc.stdin.close()
        self.proc.terminate()
        self.proc.wait()


def capture_file(work, flags, plan):
    """Replay one file after all its checked dependencies are available."""
    file = plan["file"]
    text = (work / file).read_text()
    stamp(f"proof capture: replay {file}")
    proofs = plan["proofs"]
    endpoints = {p["start"] for p in proofs} | {p["end"] for p in proofs}
    endpoints.update(e for p in proofs for e in p["steps"])
    states = {}
    if proofs:
        with tempfile.TemporaryFile() as log:
            prover = Prover(work, flags, log)
            try:
                last = time.monotonic()
                for command in plan["commands"]:
                    start, end = command["start"], command["end"]
                    try:
                        prover.add(text[start:end])
                        if end in endpoints:
                            states[str(end)] = prover.goals()
                    except Exception as exc:
                        raise RuntimeError(f"{file}:{text[:start].count(chr(10)) + 1}: {text[start:end]}\n{exc}") from exc
                    if time.monotonic() - last >= 10:
                        stamp(f"proof capture: {file} line {text[:end].count(chr(10)) + 1}")
                        last = time.monotonic()
            finally:
                prover.close()
        if set(map(int, states)) != endpoints:
            raise RuntimeError(f"Missing proof endpoints in {file}")
        for p in proofs:
            if states[str(p["start"])] is None or any(states[str(e)] is None for e in p["steps"]):
                raise RuntimeError(f"Missing active proof state in {file}: {p}")
            if p["kind"] in ("Qed", "Defined") and states[str(p["end"])] is not None:
                raise RuntimeError(f"Proof did not close in {file}: {p}")
    stamp(f"proof capture: {file}: {len(proofs)} proofs, {len(states)} snapshots")
    return file, {"sha256": hashlib.sha256(text.encode()).hexdigest(), "states": states}


# The site inlines every captured state into its page, and GitHub Pages
# publishes at most 1 GB, so the states have a budget, in bytes of their
# JSON: per file, so that a page stays light enough for a phone, and per
# capture. Past it, the largest proofs lose their states first and keep
# their source view, without the explorer (rocq_draw.pl's proof_//2).
# A page's HTML grows by about 16 times its states' JSON (Hi.v: 0.51 MB
# of states, an 8 MB page); a few huge states render more compactly
# (ExternalCalls.v: 46.5 MB, 239 MB).
FILE_BUDGET = 1_000_000
TOTAL_BUDGET = 16_000_000


def proof_keys(proof):
    """The snapshot keys of one proof: its start, its steps and its end."""
    return {str(proof["start"]), str(proof["end"]), *(str(e) for e in proof["steps"])}


def fit_budget(files, plans, file_budget=FILE_BUDGET, total_budget=TOTAL_BUDGET):
    """Drop the states of the largest proofs until every file and the whole
    capture fit their budgets; report what each file lost."""
    proofs = []
    for file, entry in files.items():
        for proof in plans[file]["proofs"]:
            keys = proof_keys(proof)
            size = sum(len(json.dumps(entry["states"][k], ensure_ascii=False)) for k in keys)
            proofs.append((size, file, keys))
    per_file = dict.fromkeys(files, 0)
    for size, file, _ in proofs:
        per_file[file] += size
    total = sum(per_file.values())
    dropped = dict.fromkeys(files, 0)
    for size, file, keys in sorted(proofs, key=lambda p: -p[0]):
        if per_file[file] > file_budget or total > total_budget:
            for k in keys:
                files[file]["states"].pop(k, None)
            per_file[file] -= size
            total -= size
            dropped[file] += 1
    for file in files:
        if dropped[file]:
            stamp(f"proof capture: {file}: over budget, {dropped[file]} proofs without states")
    stamp(f"proof capture: {total} bytes of states")


def dependencies(work, flags, files):
    """Each file's imports among files, as rocq dep (coqdep) reads them."""
    out = subprocess.run(["coqdep", *flags, *files], cwd=work, check=True,
                         stdin=subprocess.DEVNULL, capture_output=True, text=True).stdout
    vo = {f[:-2] + ".vo": f for f in files}
    deps = {f: set() for f in files}
    for line in out.splitlines():
        targets, _, sources = line.partition(":")
        target = targets.split()[0] if targets.split() else ""
        if target in vo:
            deps[vo[target]] |= {vo[s] for s in sources.split() if s in vo}
    return deps


def workers():
    cores = int(os.environ.get("NIX_BUILD_CORES") or 0)
    return cores if cores > 0 else len(os.sched_getaffinity(0))


def capture(project, output, replay=""):
    project = project.resolve()
    project_file = next(p for p in [project / "_RocqProject", project / "_CoqProject"] if p.exists())
    flags, files = [], []
    for line in project_file.read_text().splitlines():
        words = shlex.split(line, comments=True)
        if words and words[0] in ("-R", "-Q"):
            flags.extend(words)
        elif len(words) == 1 and words[0].endswith(".v"):
            files.append(words[0])
        elif words:
            raise ValueError(f"Unsupported project option: {line}")
    here = Path(__file__).resolve().parent
    plans = json.loads(subprocess.check_output(
        ["swipl", str(here / "capture_plan.pl"), *files], cwd=project, stdin=subprocess.DEVNULL,
    ))
    version = subprocess.check_output(["coqc", "--version"], text=True).strip()
    data = {"version": 1, "prover": version, "files": {}}
    with tempfile.TemporaryDirectory(prefix="dterm-rocq-") as tmp:
        work = Path(tmp) / "project"
        shutil.copytree(project, work, ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux"))
        by_file = {plan["file"]: plan for plan in plans}
        deps = dependencies(work, flags, files)
        users = {f: {g for g in files if f in deps[g]} for f in files}

        def compile_file(file):
            stamp(f"proof capture: compile {file}")
            subprocess.run(["coqc", *flags, file], cwd=work, check=True, stdin=subprocess.DEVNULL)

        # Jobs: compile an imported file, replay every file. Either may
        # start once the file's imports are compiled. The longest chain of
        # compiles still waiting on a job goes first; costs are unknown,
        # so each job counts one.
        replayed = [f for f in files if f.startswith(replay)]
        needed = set()

        def need(f):
            for g in deps[f] - needed:
                needed.add(g)
                need(g)
        for f in replayed:
            need(f)
        users = {f: users[f] & (needed | set(replayed)) for f in files}
        jobs = [("compile", f) for f in files if f in needed] + [("replay", f) for f in replayed]
        depth = {}

        def chain(job):
            if job not in depth:
                kind, f = job
                depth[job] = 1 if kind == "replay" else 1 + max(
                    [chain(("replay", g)) for g in users[f]] +
                    [chain(("compile", g)) for g in users[f] if users[g]])
            return depth[job]

        order = sorted(jobs, key=lambda job: (-chain(job), files.index(job[1]), job[0]))
        compiled, waiting, running = set(), list(order), {}
        n = workers()
        stamp(f"proof capture: {len(jobs) - len(replayed)} compiles and {len(replayed)} replays on {n} workers")
        with concurrent.futures.ThreadPoolExecutor(n) as pool:
            while waiting or running:
                for job in [j for j in waiting if deps[j[1]] <= compiled][:n - len(running)]:
                    waiting.remove(job)
                    kind, f = job
                    running[pool.submit(compile_file, f) if kind == "compile"
                            else pool.submit(capture_file, work, flags, by_file[f])] = job
                finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in finished:
                    kind, f = running.pop(future)
                    try:
                        result = future.result()
                    except BaseException:
                        for other in running:
                            other.cancel()
                        raise
                    if kind == "compile":
                        compiled.add(f)
                    else:
                        data["files"][result[0]] = result[1]
        data["files"] = {f: data["files"][f] for f in replayed}
        fit_budget(data["files"], by_file)
    output.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--replay", default="", metavar="PREFIX")
    args = parser.parse_args()
    capture(args.project, args.output, args.replay)
