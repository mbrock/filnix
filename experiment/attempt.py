"""An independent systemd unit owns each attempt and its durable files."""

import fcntl
import json
import os
from pathlib import Path
import resource
import selectors
import signal
import subprocess
import sys
import time
import uuid

from . import nix
from .capture import BuildLogFilter
from .model import atomic_json, encode, stamp
from .timing import BuildTimes


def directory(state, aid):
    if str(uuid.UUID(aid)) != aid:
        raise ValueError("invalid attempt UUID")
    return Path(state) / "attempts" / aid


def limited_eval(policy):
    resource.setrlimit(
        resource.RLIMIT_AS, (policy["eval_memory"], policy["eval_memory"])
    )
    os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])


def plan(folder, spec):
    policy = spec["policy"]
    rows = folder / "plan.jsonl"
    with (
        rows.open("w") as output,
        (folder / "stderr.log").open("ab", buffering=0) as log,
    ):
        for target in spec["targets"]:
            row = {"id": target["id"]}

            def literal(value):
                return encode(encode(value)).replace("${", "\\${")

            expr = f"import {Path(__file__).with_name('planner.nix')} {{ source = builtins.fromJSON {literal(spec['source'])}; attrPath = builtins.fromJSON {literal(target['attr'])}; }}"
            try:
                # The worker is single threaded; limits are applied only to its evaluator child.
                r = subprocess.run(
                    nix.command(
                        "eval",
                        "--impure",
                        "--json",
                        "--offline",
                        "--no-write-lock-file",
                        "--option",
                        "allow-import-from-derivation",
                        "false",
                        "--option",
                        "max-jobs",
                        "0",
                        "--option",
                        "builders",
                        "",
                        "--expr",
                        expr,
                    ),
                    capture_output=True,
                    timeout=policy["eval_seconds"],
                    preexec_fn=lambda: limited_eval(policy),
                )
                log.write(r.stderr[: 1024 * 1024])
                if r.returncode:
                    raise ValueError(r.stderr.decode(errors="replace")[-8000:])
                recipe = json.loads(r.stdout)
                graph = nix.graph([recipe["drv"]])
                nix.normalize_graph(graph)
                graph_file = f"graph-{target['id']}.json"
                atomic_json(folder / graph_file, graph)
                row.update(recipe=recipe, graph=graph_file)
            except (ValueError, subprocess.SubprocessError, OSError) as e:
                row["error"] = str(e)[-8000:]
            output.write(encode(row) + "\n")
            output.flush()
            os.fsync(output.fileno())
    return {"exit_code": 0, "reason": "completed"}


def build(folder, spec):
    policy = spec["policy"]
    limits = nix.resources(policy)
    if not limits["verified"]:
        return {
            "exit_code": None,
            "reason": "resource-policy",
            "error": limits["reason"],
        }
    cmd = nix.command(
        "build",
        "--no-link",
        "--json",
        "--keep-going",
        "--log-format",
        "internal-json",
        "-L",
        "--max-jobs",
        str(policy["max_jobs"]),
        "--cores",
        str(policy["cores"]),
        "--timeout",
        str(policy["wall_seconds"]),
        "--max-silent-time",
        str(policy["silent_seconds"]),
        "--option",
        "builders",
        "",
        *[t + "^*" for t in spec["targets"]],
    )
    # Store this independently of controller state, including interrupted launches.
    before = sorted(nix.valid(set(spec["output_paths"])))
    atomic_json(folder / "before.json", before)
    initial_resources = nix.resources(policy)
    times = BuildTimes(folder)
    capture = BuildLogFilter()
    proc = subprocess.Popen(
        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True
    )
    start = last = time.monotonic()
    reason, signalled, written = None, None, 0

    def stop(sig, _frame=None):
        nonlocal reason, signalled
        if signalled is None:
            reason = "cancelled" if sig == signal.SIGTERM else "interrupted"
            signalled = time.monotonic()
            os.killpg(proc.pid, signal.SIGINT)

    old = signal.signal(signal.SIGTERM, stop)
    selector = selectors.DefaultSelector()
    with (
        (folder / "stdout.log").open("wb", buffering=0) as out,
        (folder / "stderr.log").open("wb", buffering=0) as err,
    ):
        selector.register(proc.stdout, selectors.EVENT_READ, out)
        selector.register(proc.stderr, selectors.EVENT_READ, err)
        while selector.get_map() or proc.poll() is None:
            now = time.monotonic()
            if not signalled and (
                now - start > policy["wall_seconds"]
                or now - last > policy["silent_seconds"]
            ):
                stop(signal.SIGINT)
                reason = "timeout"
            if signalled and now - signalled > 15 and proc.poll() is None:
                os.killpg(proc.pid, signal.SIGKILL)
            for key, _ in selector.select(0.25):
                data = os.read(key.fileobj.fileno(), 65536)
                if not data:
                    selector.unregister(key.fileobj)
                    key.fileobj.close()
                    data = capture.finish() if key.data is err else b""
                else:
                    last = now
                    if key.data is err:
                        data = capture.feed(data)
                remaining = max(0, policy["log_bytes"] - written)
                key.data.write(data[:remaining])
                if key.data is err:
                    times.feed(data[:remaining])
                written += min(len(data), remaining)
                if len(data) > remaining and not signalled:
                    stop(signal.SIGINT)
                    reason = "log-limit"
        code = proc.wait()
        os.fsync(out.fileno())
        os.fsync(err.fileno())
    selector.close()
    signal.signal(signal.SIGTERM, old)
    after = nix.resources(policy)
    if initial_resources.get("events") != after.get(
        "events"
    ) and "oom_kill" in after.get("events", ""):

        def kills(r):
            return int(
                dict(line.split() for line in r.get("events", "").splitlines()).get(
                    "oom_kill", 0
                )
            )

        if kills(after) > kills(initial_resources):
            reason = "resource-interruption"
    return dict(
        exit_code=code,
        reason=reason or ("completed" if code == 0 else "build-error"),
        resources_before=initial_resources,
        resources_after=after,
        truncated=reason == "log-limit",
        omitted_progress_records=capture.omitted_records,
        omitted_progress_bytes=capture.omitted_bytes,
        command=cmd,
    )


def run(state, aid):
    folder = directory(state, aid)
    # Never repeat an executed UUID, even if systemctl start is retried after a crash.
    with (folder / "worker.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        if (folder / "started.json").exists():
            return
        spec = json.loads((folder / "spec.json").read_text())
        atomic_json(
            folder / "started.json",
            {
                "time": stamp(),
                "pid": os.getpid(),
                "worker": str(Path(__file__).resolve()),
            },
        )
        try:
            actual_nix = subprocess.check_output(
                [nix.NIX, "--version"], text=True, timeout=10
            ).strip()
            if spec.get("nix_version") and spec["nix_version"] != actual_nix:
                raise ValueError(
                    "Nix version changed since campaign import; create a new campaign"
                )
            result = (
                plan(folder, spec) if spec["kind"] == "plan" else build(folder, spec)
            )
        except Exception as e:
            result = {"exit_code": 1, "reason": "worker-error", "error": str(e)}
        result["finished"] = stamp()
        atomic_json(folder / "exit.json", result)


if __name__ == "__main__":
    run(sys.argv[1], sys.argv[2])
