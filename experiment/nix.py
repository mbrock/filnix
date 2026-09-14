"""Nix 2.32 adapter. Unknown events stay in raw logs, never imply success."""

import json
import os
from pathlib import Path
import re
import subprocess

from .model import encode, stamp
from .scope import REASON, kernel_derivation

NIX = os.environ.get("FILNIX_NIX", "nix")
DRV = re.compile(r"/nix/store/[a-z0-9]{32}-[^\s'\";]+\.drv")
DEFAULT_POLICY = dict(
    max_jobs=4,
    cores=7,
    batch_size=8,
    build_lanes=1,  # Two bounded clients require explicit opt-in and lookahead.
    plan_ahead=0,  # Explicit opt-in; old campaigns retain serial admission.
    wall_seconds=7200,
    silent_seconds=900,
    log_bytes=128 * 1024**2,
    eval_seconds=90,
    eval_memory=4 * 1024**3,
    min_free_bytes=50 * 1024**3,
    retained_log_bytes=20 * 1024**3,
    slice="/sys/fs/cgroup/filnix.slice/filnix-workload.slice",
    cpus="1-15,17-31",
    memory_fraction=0.80,
)


def command(*args):
    return [NIX, "--extra-experimental-features", "nix-command flakes", *args]


def query(*args, timeout=60):
    r = subprocess.run(command(*args), capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise ValueError(r.stderr[-8000:])
    return json.loads(r.stdout)


def valid(paths):
    if not paths:
        return set()
    if len(paths) > 128:
        ordered = sorted(paths)
        return set().union(
            *(valid(ordered[i : i + 128]) for i in range(0, len(ordered), 128))
        )
    r = subprocess.run(
        command("path-info", "--json", *sorted(paths)),
        capture_output=True,
        text=True,
        timeout=60,
    )
    try:
        data = json.loads(r.stdout)
    except ValueError:
        raise ValueError(
            "Nix store validity query failed: " + r.stderr[-2000:]
        ) from None
    if isinstance(data, dict):
        return {
            p
            for p, info in data.items()
            if info is not None and info.get("valid", True)
        }
    return {info["path"] for info in data if info.get("valid", True)}


def graph(drvs):
    return query("derivation", "show", "--recursive", *drvs)


def normalize_graph(data):
    # Newer Nix may wrap its versioned JSON. Refuse an unknown schema.
    if "derivations" in data:
        data = data["derivations"]
    result = {}
    for drv, info in data.items():
        # Nix 2.32 / Determinate 3.12 emits schema v4 store-relative names.
        drv = drv if drv.startswith("/") else "/nix/store/" + drv
        if not DRV.fullmatch(drv) or "outputs" not in info or "inputDrvs" not in info:
            raise ValueError(
                "unsupported derivation JSON; retain raw output and update adapter"
            )
        info = dict(info)
        info["outputs"] = {
            k: dict(
                v,
                path=(
                    v["path"]
                    if v["path"].startswith("/")
                    else "/nix/store/" + v["path"]
                ),
            )
            if v.get("path")
            else v
            for k, v in info["outputs"].items()
        }
        info["inputDrvs"] = {
            (k if k.startswith("/") else "/nix/store/" + k): v
            for k, v in info["inputDrvs"].items()
        }
        result[drv] = info
    return result


def add_graph(db, data):
    for drv, info in normalize_graph(data).items():
        outputs = {k: v.get("path") for k, v in info["outputs"].items()}
        db.execute(
            "INSERT OR IGNORE INTO derivations(drv,name,outputs) VALUES(?,?,?)",
            (
                drv,
                info.get(
                    "name", info.get("env", {}).get("name", Path(drv).name[33:-4])
                ),
                encode(outputs),
            ),
        )
        if kernel_derivation(info):
            db.execute("UPDATE derivations SET exclusion=? WHERE drv=?", (REASON, drv))
        for child, required in info["inputDrvs"].items():
            db.execute(
                "INSERT OR IGNORE INTO edges VALUES(?,?,?)",
                (drv, child, encode(required)),
            )


def observe(db, aid, raw):
    if not raw.startswith(b"@nix "):
        return
    try:
        e = json.loads(raw[5:])
    except (ValueError, UnicodeDecodeError):
        return
    if not isinstance(e, dict):
        return
    action, fields = e.get("action"), e.get("fields", [])
    act = str(e.get("id", ""))
    if not isinstance(fields, list):
        return
    if (
        action == "start"
        and e.get("type") == 105
        and fields
        and isinstance(fields[0], str)
    ):
        if DRV.fullmatch(fields[0]):
            db.execute(
                "INSERT OR IGNORE INTO activities(attempt,activity,drv,kind) VALUES(?,?,?,'build')",
                (aid, act, fields[0]),
            )
    elif (
        action == "result"
        and e.get("type") == 104
        and fields
        and isinstance(fields[0], str)
    ):
        row = db.execute(
            "SELECT phase,checks FROM activities WHERE attempt=? AND activity=?",
            (aid, act),
        ).fetchone()
        if row:
            checks = json.loads(row["checks"])
            if fields[0] in ("checkPhase", "installCheckPhase"):
                checks.append(fields[0])
            db.execute(
                "UPDATE activities SET phase=?,checks=? WHERE attempt=? AND activity=?",
                (fields[0], encode(checks), aid, act),
            )
    elif action == "stop":
        # Stop is not a success signal.
        db.execute(
            "UPDATE activities SET stopped=1 WHERE attempt=? AND activity=?", (aid, act)
        )


def failure_messages(raw):
    """Only Nix's root builder-failed diagnostic, never its dependent-failed line."""
    failures = set()
    for line in raw.splitlines():
        if not line.startswith(b"@nix "):
            continue
        try:
            e = json.loads(line[5:])
            msg = e.get("msg", "")
            msg = re.sub(r"\x1b\[[0-9;]*m", "", msg)
            root_failure = ("builder for" in msg and "failed" in msg) or (
                msg.startswith("error: Cannot build '")
                and "Reason: builder failed with exit code" in msg
            )
            if e.get("action") == "msg" and root_failure:
                match = DRV.search(msg)
                if match:
                    failures.add(match.group())
        except (ValueError, TypeError, AttributeError):
            pass
    return failures


def cpu_set(value):
    result = set()
    for item in value.split(","):
        if not item.strip():
            continue
        bits = item.strip().split("-")
        result.update(range(int(bits[0]), int(bits[-1]) + 1))
    return result


def resources(policy):
    root = Path(policy["slice"])
    result = {"verified": False, "reason": "workload slice absent", "observed": stamp()}
    try:
        memory = int((root / "memory.current").read_text())
        maximum = int((root / "memory.max").read_text())
        high = int((root / "memory.high").read_text())
        cpus = (root / "cpuset.cpus.effective").read_text().strip()
        total = (
            int(
                next(
                    x.split()[1]
                    for x in Path("/proc/meminfo").read_text().splitlines()
                    if x.startswith("MemTotal:")
                )
            )
            * 1024
        )
        daemon = subprocess.check_output(
            [
                "systemctl",
                "show",
                "nix-daemon.service",
                "--value",
                "-p",
                "ControlGroup",
            ],
            text=True,
            timeout=5,
        ).strip()
        relative = "/" + str(root.relative_to("/sys/fs/cgroup"))
        configured = cpu_set(cpus) <= cpu_set(policy["cpus"]) and bool(cpus)
        bounded = maximum <= total * policy["memory_fraction"] * 1.001
        contained = daemon.startswith(relative + "/")
        result.update(
            memory=memory,
            maximum=maximum,
            high=high,
            cpus=cpus,
            pressure=(root / "memory.pressure").read_text().strip(),
            events=(root / "memory.events").read_text().strip(),
            daemon=daemon,
            verified=configured and bounded and contained,
            reason=""
            if configured and bounded and contained
            else "daemon containment or resource limits do not match policy",
        )
    except (OSError, ValueError, subprocess.SubprocessError) as e:
        result["reason"] = str(e)
    return result
