#!/usr/bin/env python3
"""Capture real Rocq states for dterm; no browser prover or inferred goals.

python3 capture.py PROJECT OUTPUT.json
Needs coqc, coqidetop, swipl and the project's Stdlib on ROCQPATH.
Compiles dependencies and replays commands in an isolated writable copy.
The bundled RocqIDE XML protocol is pinned by the site's Rocq package.
Run under tests/watch.py for deadlines and 15-second progress reporting.
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


def capture(project, output):
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
        for plan in plans:
            file = plan["file"]
            stamp(f"proof capture: compile {file}")
            subprocess.run(["coqc", *flags, file], cwd=work, check=True, stdin=subprocess.DEVNULL)
        # Prover instances and their XML streams are per file. Only replay
        # independent files in parallel, never the dependency compilation.
        stamp(f"proof capture: replay {len(plans)} files, fanout=4")
        with concurrent.futures.ThreadPoolExecutor(4) as pool:
            for file, entry in pool.map(lambda plan: capture_file(work, flags, plan), plans):
                data["files"][file] = entry
    output.write_text(json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    capture(args.project, args.output)
