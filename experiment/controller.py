"""Single writer, explicit admission, durable intent before independent execution."""

import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import uuid

from . import VERSION, nix
from .attempt import directory
from .model import atomic_json, closure, encode, event, refresh_candidates, stamp
from .scheduling import build_policy, reservations
from .scope import REASON, kernel_metadata
from .timing import ingest_times


class Units:
    def __init__(self, state, launcher="/usr/local/libexec/filnix-attempt-unit"):
        self.state, self.launcher = Path(state), launcher

    def start(self, aid):
        subprocess.run(
            [self.launcher, "start", aid], check=True, timeout=20, capture_output=True
        )

    def stop(self, aid):
        subprocess.run(
            [self.launcher, "stop", aid], check=True, timeout=30, capture_output=True
        )

    def active(self, aid):
        r = subprocess.run(
            [
                "systemctl",
                "show",
                f"filnix-attempt@{aid}.service",
                "--value",
                "-p",
                "ActiveState",
            ],
            capture_output=True,
            text=True,
            timeout=10,
            check=True,
        )
        return r.stdout.strip() in ("active", "activating", "deactivating", "reloading")


class Controller:
    def __init__(self, db, state, units=None):
        self.db, self.state = db, Path(state)
        self.units = units or Units(state)
        (self.state / "attempts").mkdir(exist_ok=True)
        (self.state / "roots").mkdir(exist_ok=True)

    def campaign(self, cid):
        row = self.db.execute("SELECT * FROM campaigns WHERE id=?", (cid,)).fetchone()
        if not row:
            raise ValueError("unknown campaign")
        return row

    def root(self, path):
        # Deployment registers this directory under /nix/var/nix/gcroots.
        if path and Path(path).exists():
            link = self.state / "roots" / Path(path).name
            if not link.is_symlink():
                link.symlink_to(path)

    def active_attempts(self):
        return self.db.execute(
            "SELECT * FROM attempts WHERE state IN ('intended','running') ORDER BY rowid"
        ).fetchall()

    def intent(self, campaign, kind, targets, **extra):
        if kind not in ("plan", "build"):
            raise ValueError("unknown attempt kind")
        active = self.active_attempts()
        policy = json.loads(campaign["policy"])
        ahead = policy.get("plan_ahead", 0)
        builds = [r for r in active if r["kind"] == "build"]
        if any(r["campaign"] != campaign["id"] for r in active):
            raise ValueError("another campaign is active")
        if kind == "plan" and any(r["kind"] == "plan" for r in active):
            raise ValueError("planner already occupied")
        if active and not ahead:
            raise ValueError("an attempt is already active; planning ahead is disabled")
        if kind == "build":
            self.check_scope(targets)
            effective = build_policy(policy, builds)
            if not effective:
                raise ValueError("build lanes or requested CPU budget occupied")
            if policy.get("build_lanes", 1) > 1 or builds:
                graph, held, available = reservations(self.db, self.state, builds)
                needed = graph.needed(targets, available, held)
                if needed & held or graph.paths(needed) & graph.paths(held):
                    raise ValueError("build dependencies are owned by another attempt")
                extra["admission_available"] = sorted(available)
            policy = effective
        aid = str(uuid.uuid4())
        spec = dict(
            kind=kind,
            runner_version=VERSION,
            targets=targets,
            policy=policy,
            source=campaign["source"],
            nix_version=campaign["nix_version"],
            **extra,
        )
        # Files can be orphaned before the transaction; DB intent can always recreate them.
        folder = directory(self.state, aid)
        folder.mkdir()
        atomic_json(folder / "spec.json", spec)
        with self.db:
            self.db.execute(
                "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec) VALUES(?,?,?,?,'intended',?,?)",
                (aid, campaign["id"], kind, encode(targets), stamp(), encode(spec)),
            )
            if kind == "build":
                self.db.executemany(
                    "UPDATE candidates SET state='running' WHERE campaign=? AND drv=?",
                    [(campaign["id"], t) for t in targets],
                )
            event(
                self.db,
                campaign["id"],
                "attempt-intended",
                {"id": aid, "kind": kind, "count": len(targets)},
            )
        return aid

    def plan(self, cid, ids):
        campaign = self.campaign(cid)
        if not ids or len(ids) > 64:
            raise ValueError("plan requires 1–64 candidate IDs")
        targets = []
        for i in ids:
            row = self.db.execute(
                "SELECT * FROM candidates WHERE id=? AND campaign=?", (int(i), cid)
            ).fetchone()
            if not row or row["drv"] or row["state"] == "excluded":
                raise ValueError("candidate absent or already planned")
            targets.append({"id": row["id"], "attr": json.loads(row["attr"])})
        return self.intent(campaign, "plan", targets)

    def ingest(self, attempt):
        folder = directory(self.state, attempt["id"])
        log = folder / "stderr.log"
        if not log.exists():
            return
        with log.open("rb") as f:
            f.seek(attempt["offset"])
            data = f.read(4 * 1024**2)
        # Only commit complete lines; a torn final line remains raw evidence.
        end = data.rfind(b"\n") + 1
        if not end and len(data) == 4 * 1024**2:
            # A compiler can emit a single enormous line. Keep it on disk, but
            # skip it without unbounded allocation or wedging reconciliation.
            with log.open("rb") as f:
                f.seek(attempt["offset"])
                while True:
                    fragment = f.readline(1024**2)
                    if fragment.endswith(b"\n"):
                        break
                    if not fragment:
                        if not (folder / "exit.json").exists():
                            return
                        break
                end = f.tell() - attempt["offset"]
            with self.db:
                self.db.execute(
                    "UPDATE attempts SET offset=? WHERE id=? AND offset=?",
                    (attempt["offset"] + end, attempt["id"], attempt["offset"]),
                )
                event(
                    self.db,
                    attempt["campaign"],
                    "oversized-log-line",
                    {
                        "attempt": attempt["id"],
                        "offset": attempt["offset"],
                        "bytes": end,
                    },
                )
            return
        if end:
            with self.db:
                actual = self.db.execute(
                    "SELECT offset FROM attempts WHERE id=?", (attempt["id"],)
                ).fetchone()[0]
                if actual != attempt["offset"]:
                    return
                for line in data[:end].splitlines():
                    nix.observe(self.db, attempt["id"], line)
                self.db.execute(
                    "UPDATE attempts SET offset=offset+? WHERE id=?",
                    (end, attempt["id"]),
                )

    def finish_plan(self, attempt, result):
        folder = directory(self.state, attempt["id"])
        seen = set()
        rows = folder / "plan.jsonl"
        if rows.exists():
            for line in rows.read_bytes().splitlines(keepends=True):
                if not line.endswith(b"\n"):
                    continue
                row = json.loads(line)
                seen.add(row["id"])
                if "error" in row:
                    self.db.execute(
                        "UPDATE candidates SET state='evaluation-error',error=? WHERE id=?",
                        (row["error"], row["id"]),
                    )
                    continue
                recipe = row["recipe"]
                nix.add_graph(self.db, json.loads((folder / row["graph"]).read_text()))
                self.root(recipe["drv"])
                held = self.db.execute(
                    "SELECT error FROM candidates WHERE campaign=? AND drv=? AND state='inconclusive' LIMIT 1",
                    (attempt["campaign"], recipe["drv"]),
                ).fetchone()
                self.db.execute(
                    "UPDATE candidates SET state=?,drv=?,recipe=?,error=? WHERE id=?",
                    (
                        "inconclusive" if held else "queued",
                        recipe["drv"],
                        encode(recipe),
                        held["error"] if held else None,
                        row["id"],
                    ),
                )
                for role in recipe["roles"]:
                    self.db.execute(
                        "INSERT OR IGNORE INTO roles VALUES(?,?,?,?)",
                        (attempt["campaign"], recipe["drv"], role["drv"], role["role"]),
                    )
        for target in json.loads(attempt["targets"]):
            if target["id"] not in seen:
                self.db.execute(
                    "UPDATE candidates SET state='evaluation-error',error=? WHERE id=?",
                    ("planning interrupted; no completed observation", target["id"]),
                )

        refresh_candidates(self.db, attempt["campaign"])
        # An alias discovered by the planner may name an active build root.
        self.db.execute(
            """UPDATE candidates SET state='running' WHERE campaign=? AND drv IN (
              SELECT j.value FROM attempts a,json_each(a.targets) j
              WHERE a.campaign=? AND a.kind='build' AND a.state IN ('intended','running'))""",
            (attempt["campaign"], attempt["campaign"]),
        )

    def finish_build(self, attempt, result):
        folder = directory(self.state, attempt["id"])
        spec = json.loads(attempt["spec"])
        paths = set(spec["output_paths"])
        available = nix.valid(paths)
        before_file = folder / "before.json"
        before = (
            set(json.loads(before_file.read_text())) if before_file.exists() else set()
        )
        activities = {
            r["drv"]: r
            for r in self.db.execute(
                "SELECT * FROM activities WHERE attempt=? AND drv IS NOT NULL",
                (attempt["id"],),
            )
        }
        raw = (
            (folder / "stderr.log").read_bytes()
            if (folder / "stderr.log").exists()
            else b""
        )
        # Resource/cancel failures do not diagnose package compatibility.
        failures = (
            nix.failure_messages(raw) if result["reason"] == "build-error" else set()
        )
        for drv in spec["derivations"]:
            row = self.db.execute(
                "SELECT * FROM derivations WHERE drv=?", (drv,)
            ).fetchone()
            outputs = set(json.loads(row["outputs"]).values())
            complete = bool(outputs) and None not in outputs and outputs <= available
            activity = activities.get(drv)
            if complete:
                origin = (
                    "pre-existing"
                    if outputs <= before
                    else "local"
                    if activity
                    else "unknown"
                )
                # If absent before, successful realization plus its build activity establishes
                # successful observed phases; batch exit status alone does not.
                # A cached dependency reused by another lane must not erase the
                # original build/test provenance when that lane finishes later.
                if origin == "local" or not row["available"]:
                    self.db.execute(
                        "UPDATE derivations SET available=1,origin=?,failure=NULL,evidence_attempt=? WHERE drv=?",
                        (origin, attempt["id"], drv),
                    )
                for output in outputs:
                    self.root(output)
                if origin == "local" and activity and not result.get("truncated"):
                    for phase in set(json.loads(activity["checks"])):
                        self.db.execute(
                            "INSERT OR IGNORE INTO tests VALUES(?,?,?,?)",
                            (
                                attempt["id"],
                                drv,
                                phase,
                                "phase observed in local build; outputs realized after attempt",
                            ),
                        )
            elif drv in failures:
                phase = activity["phase"] if activity else None
                failure = {
                    "configurePhase": "configure",
                    "buildPhase": "compile-or-link",
                    "checkPhase": "check",
                    "installCheckPhase": "check",
                }.get(phase, "build")
                self.db.execute(
                    "UPDATE derivations SET available=0,failure=?,evidence_attempt=? WHERE drv=?",
                    (failure, attempt["id"], drv),
                )
        self.db.executemany(
            "UPDATE candidates SET state='queued' WHERE campaign=? AND drv=? AND state='running'",
            [(attempt["campaign"], drv) for drv in json.loads(attempt["targets"])],
        )
        refresh_candidates(self.db, attempt["campaign"])
        # Inconclusive roots require an explicit retry, never an automatic failure loop.
        for drv in json.loads(attempt["targets"]):
            self.db.execute(
                "UPDATE candidates SET state='inconclusive',error=? WHERE campaign=? AND drv=? AND state='queued'",
                (result["reason"], attempt["campaign"], drv),
            )

    def reconcile(self):
        for row in self.db.execute(
            "SELECT * FROM attempts WHERE state IN ('intended','running')"
        ).fetchall():
            folder = directory(self.state, row["id"])
            folder.mkdir(exist_ok=True)
            if not (folder / "spec.json").exists():
                atomic_json(folder / "spec.json", json.loads(row["spec"]))
            self.ingest(row)
            with self.db:
                ingest_times(self.db, folder, row["id"])
            completion = folder / "exit.json"
            if completion.exists():
                # Drain the bounded raw log before terminal reconciliation.
                current = self.db.execute(
                    "SELECT * FROM attempts WHERE id=?", (row["id"],)
                ).fetchone()
                size = (
                    (folder / "stderr.log").stat().st_size
                    if (folder / "stderr.log").exists()
                    else 0
                )
                if size - current["offset"] > 4 * 1024**2:
                    continue
                self.ingest(current)
                with self.db:
                    ingest_times(self.db, folder, row["id"])
                result = json.loads(completion.read_text())
            elif self.units.active(row["id"]):
                if row["cancel_requested"]:
                    self.units.stop(row["id"])
                with self.db:
                    self.db.execute(
                        "UPDATE attempts SET state='running' WHERE id=?", (row["id"],)
                    )
                continue
            elif not (folder / "started.json").exists() and row["state"] == "intended":
                if row["cancel_requested"]:
                    result = {
                        "reason": "cancelled",
                        "exit_code": None,
                        "finished": stamp(),
                    }
                else:
                    self.units.start(row["id"])
                    continue
            else:
                result = {
                    "reason": "cancelled" if row["cancel_requested"] else "interrupted",
                    "exit_code": None,
                    "finished": stamp(),
                }
            with self.db:
                if row["kind"] == "plan":
                    self.finish_plan(row, result)
                else:
                    self.finish_build(row, result)
                self.db.execute(
                    "UPDATE attempts SET state='finished',finished=?,result=? WHERE id=?",
                    (result["finished"], encode(result), row["id"]),
                )
                event(
                    self.db,
                    row["campaign"],
                    "attempt-finished",
                    {"id": row["id"], "reason": result["reason"]},
                )

    def admission_reason(self, policy):
        resources = nix.resources(policy)
        reason = resources["reason"] if not resources["verified"] else ""
        if resources.get("memory", 0) >= resources.get("high", float("inf")):
            reason = "memory pressure: waiting below MemoryHigh"
        if shutil.disk_usage(self.state).free < policy["min_free_bytes"]:
            reason = "disk reserve reached"
        log_size = sum(
            p.stat().st_size for p in (self.state / "attempts").glob("*/*.log")
        )
        if log_size >= policy["retained_log_bytes"]:
            reason = "retained log budget reached; archive attempts before continuing"
        return reason

    def admit(self, campaign):
        policy = json.loads(campaign["policy"])
        active = self.active_attempts()
        if any(r["campaign"] != campaign["id"] for r in active):
            return
        ahead = policy.get("plan_ahead", 0)
        lanes = {r["kind"] for r in active}
        builds = [r for r in active if r["kind"] == "build"]
        can_build = build_policy(policy, builds) is not None
        if active and (not ahead or (not can_build and "plan" in lanes)):
            return
        reason = self.admission_reason(policy)
        with self.db:
            self.db.execute(
                "UPDATE campaigns SET hold=? WHERE id=?", (reason, campaign["id"])
            )
        if reason:
            return
        if can_build:
            candidates = [
                r[0]
                for r in self.db.execute(
                    """SELECT drv FROM candidates WHERE campaign=? AND state='queued'
                       GROUP BY drv ORDER BY min(label) LIMIT ?""",
                    (campaign["id"], max(policy["batch_size"], min(256, ahead))),
                )
            ]
            targets = []
            graph, held, available = reservations(self.db, self.state, builds)
            held_paths = graph.paths(held)
            for drv in candidates:
                needed = graph.needed([drv], available, held) if builds else set()
                if needed & held or graph.paths(needed) & held_paths:
                    continue
                targets.append(drv)
                if len(targets) >= policy["batch_size"]:
                    break
            if targets:
                self.build_targets(campaign, targets)
                lanes.add("build")
        if "plan" in lanes or ("build" in lanes and not ahead):
            return
        queued = self.db.execute(
            "SELECT count(DISTINCT drv) FROM candidates WHERE campaign=? AND state='queued'",
            (campaign["id"],),
        ).fetchone()[0]
        quota = min(32, max(0, ahead - queued)) if ahead else 32
        if not quota:
            return
        unplanned = [
            r[0]
            for r in self.db.execute(
                "SELECT id FROM candidates WHERE campaign=? AND state='unplanned' ORDER BY label LIMIT ?",
                (campaign["id"], quota),
            )
        ]
        if unplanned:
            self.plan(campaign["id"], unplanned)

    def check_scope(self, targets):
        for target in targets:
            row = self.db.execute(
                """WITH RECURSIVE deps(drv) AS (
                  VALUES(?) UNION SELECT child FROM edges JOIN deps ON parent=deps.drv)
                  SELECT name,exclusion FROM derivations JOIN deps USING(drv)
                  WHERE exclusion IS NOT NULL LIMIT 1""",
                (target,),
            ).fetchone()
            if row:
                raise ValueError(f"excluded: {row['name']}: {row['exclusion']}")

    def exclude_kernels(self, cid, aid=None):
        campaign = self.campaign(cid)
        if campaign["mode"] != "paused":
            raise ValueError("pause the campaign before reclassifying its scope")
        attempt = None
        if aid:
            attempt = self.db.execute(
                "SELECT * FROM attempts WHERE id=? AND campaign=?", (aid, cid)
            ).fetchone()
            if (
                not attempt
                or attempt["kind"] != "build"
                or attempt["state"] != "finished"
                or json.loads(attempt["result"] or "{}").get("reason")
                not in ("cancelled", "excluded")
            ):
                raise ValueError("attempt must be a cancelled build in this campaign")
        selected = []
        for row in self.db.execute(
            "SELECT id,drv,selection FROM candidates WHERE campaign=?", (cid,)
        ):
            selection = json.loads(row["selection"])
            if kernel_metadata(
                selection.get("metadata", {}), selection.get("sourceFile")
            ):
                selected.append(row)
        # Backfill old records, which did not retain kernel builder metadata.
        # Inspect definitions only; no evaluation or realization. New planning
        # detects the builder from its flags, even when an overlay renames it.
        suspects = {
            r[0]
            for r in self.db.execute(
                "SELECT drv FROM derivations WHERE lower(name) LIKE 'linux-%'"
            )
        }
        suspects.update(r["drv"] for r in selected if r["drv"])
        definitions = []
        ordered = sorted(suspects)
        for i in range(0, len(ordered), 64):
            definitions.append(nix.query("derivation", "show", *ordered[i : i + 64]))
        with self.db:
            for data in definitions:
                nix.add_graph(self.db, data)
            for row in selected:
                self.db.execute(
                    "UPDATE candidates SET state='excluded',error=? WHERE id=?",
                    (REASON, row["id"]),
                )
                if row["drv"]:
                    self.db.execute(
                        "UPDATE derivations SET exclusion=? WHERE drv=?",
                        (REASON, row["drv"]),
                    )
            if attempt:
                targets = json.loads(attempt["targets"])
                if not any(
                    self.db.execute(
                        "SELECT 1 FROM derivations WHERE drv=? AND exclusion IS NOT NULL",
                        (t,),
                    ).fetchone()
                    for t in targets
                ):
                    raise ValueError("cancelled batch has no excluded kernel root")
                result = json.loads(attempt["result"])
                result.update(
                    reason="excluded",
                    worker_reason=result.get("worker_reason", result["reason"]),
                    error=REASON,
                )
                self.db.execute(
                    "UPDATE attempts SET result=? WHERE id=?", (encode(result), aid)
                )
                # Only this explicit cancellation's inconclusive collateral is
                # retried. Preserve independent failures and older interruptions.
                self.db.executemany(
                    "UPDATE candidates SET state='queued',error=NULL WHERE campaign=? AND drv=? AND state='inconclusive' AND error='cancelled'",
                    [(cid, t) for t in targets],
                )
            refresh_candidates(self.db, cid)
            report = dict(
                reason=REASON,
                attempt=aid,
                runner_version=VERSION,
                excluded=[
                    dict(r)
                    for r in self.db.execute(
                        "SELECT id,label,drv,error FROM candidates WHERE campaign=? AND state='excluded' ORDER BY label",
                        (cid,),
                    )
                ],
            )
            event(self.db, cid, "kernels-excluded", report)
        return report

    def build_targets(self, campaign, targets):
        drvs = set(d for target in targets for d in closure(self.db, target))
        outputs = set()
        for drv in drvs:
            r = self.db.execute(
                "SELECT outputs FROM derivations WHERE drv=?", (drv,)
            ).fetchone()
            if r:
                outputs.update(p for p in json.loads(r[0]).values() if p)
        return self.intent(
            campaign,
            "build",
            targets,
            output_paths=sorted(outputs),
            derivations=sorted(drvs),
        )

    def tick(self):
        self.reconcile()
        for c in self.db.execute("SELECT * FROM campaigns ORDER BY created").fetchall():
            if c["mode"] == "running":
                self.admit(c)
            with self.db:
                self.db.execute(
                    "UPDATE campaigns SET heartbeat=? WHERE id=?", (stamp(), c["id"])
                )

    def dispatch(self, request):
        op, cid = request["op"], request.get("campaign")
        if op == "exclude-kernels":
            return self.exclude_kernels(cid, request.get("attempt"))
        if op == "schedule":
            campaign = self.campaign(cid)
            policy = json.loads(campaign["policy"])
            before = {
                "batch_size": policy["batch_size"],
                "plan_ahead": policy.get("plan_ahead", 0),
                "build_lanes": policy.get("build_lanes", 1),
            }
            after = dict(before)
            for key, low, high in (
                ("batch_size", 1, 64),
                ("plan_ahead", 0, 256),
                ("build_lanes", 1, 2),
            ):
                value = request.get(key)
                if value is not None:
                    if type(value) is not int or not low <= value <= high:
                        raise ValueError(
                            f"{key} must be an integer from {low} to {high}"
                        )
                    after[key] = value
            if after != before:
                # Historical attempt specs stay immutable, including their policy.
                # Only admission settings change; limits, recipes, pins and checks do not.
                policy.update(after)
                with self.db:
                    self.db.execute(
                        "UPDATE campaigns SET policy=? WHERE id=?",
                        (encode(policy), cid),
                    )
                    event(
                        self.db,
                        cid,
                        "scheduling-updated",
                        {"before": before, "after": after, "runner_version": VERSION},
                    )
            return after
        if op == "plan":
            return self.plan(cid, request["ids"])
        if op == "build-once":
            campaign = self.campaign(cid)
            policy = json.loads(campaign["policy"])
            reason = self.admission_reason(policy)
            if reason:
                raise ValueError(reason)
            if campaign["mode"] != "paused":
                raise ValueError("pause the campaign before submitting a bounded batch")
            ids = request["ids"]
            if not ids or len(ids) > policy["batch_size"]:
                raise ValueError("batch exceeds campaign size budget")
            targets = []
            for i in ids:
                row = self.db.execute(
                    "SELECT drv,state FROM candidates WHERE campaign=? AND id=?",
                    (cid, i),
                ).fetchone()
                if (
                    not row
                    or not row["drv"]
                    or row["state"] not in ("queued", "available")
                ):
                    raise ValueError(
                        "candidate must be planned and ready; explicitly retry failures first"
                    )
                targets.append(row["drv"])
            return self.build_targets(campaign, sorted(set(targets)))
        if op == "retry-derivation":
            self.campaign(cid)
            drv = request["drv"]
            belongs = self.db.execute(
                """WITH RECURSIVE deps(drv) AS (
              SELECT drv FROM candidates WHERE campaign=? AND drv IS NOT NULL
              UNION SELECT child FROM edges JOIN deps ON parent=deps.drv)
              SELECT 1 FROM deps WHERE drv=?""",
                (cid, drv),
            ).fetchone()
            if not belongs:
                raise ValueError(
                    "derivation does not belong to the planned campaign graph"
                )
            self.check_scope([drv])
            with self.db:
                self.db.execute(
                    "UPDATE derivations SET failure=NULL WHERE drv=?", (drv,)
                )
                refresh_candidates(self.db, cid)
                event(self.db, cid, op, {"drv": drv})
            return "failure cleared for explicit retry"
        if op in ("run", "pause"):
            self.campaign(cid)
            with self.db:
                self.db.execute(
                    "UPDATE campaigns SET mode=?,hold='' WHERE id=?",
                    ("running" if op == "run" else "paused", cid),
                )
                event(self.db, cid, op, {})
            return op
        if op == "cancel":
            aid = request["attempt"]
            row = self.db.execute(
                "SELECT * FROM attempts WHERE id=? AND state IN ('intended','running')",
                (aid,),
            ).fetchone()
            if not row:
                raise ValueError("attempt is not active")
            with self.db:
                self.db.execute(
                    "UPDATE attempts SET cancel_requested=1 WHERE id=?", (aid,)
                )
                self.db.execute(
                    "UPDATE campaigns SET mode='paused' WHERE id=?", (row["campaign"],)
                )
            if self.units.active(aid):
                self.units.stop(aid)
            return "cancellation requested; campaign paused"
        if op == "retry":
            self.campaign(cid)
            ids = request["ids"]
            with self.db:
                for i in ids:
                    r = self.db.execute(
                        "SELECT drv,state FROM candidates WHERE campaign=? AND id=?",
                        (cid, i),
                    ).fetchone()
                    if not r or not r["drv"] or r["state"] in ("running", "excluded"):
                        raise ValueError("retry requires a planned, inactive candidate")
                    self.check_scope([r["drv"]])
                    self.db.execute(
                        "UPDATE derivations SET failure=NULL WHERE drv=?", (r["drv"],)
                    )
                    self.db.execute(
                        "UPDATE candidates SET state='queued',error=NULL WHERE campaign=? AND drv=?",
                        (cid, r["drv"]),
                    )
                refresh_candidates(self.db, cid)
                event(self.db, cid, "retry", {"ids": ids})
            return "queued; retry failed dependencies explicitly if still blocked"
        raise ValueError("unknown command")

    def serve(self):
        path = self.state / "control.sock"
        path.unlink(missing_ok=True)
        with socket.socket(socket.AF_UNIX) as server:
            server.bind(str(path))
            os.chmod(path, 0o600)
            server.listen(8)
            server.settimeout(1)
            while True:
                self.tick()
                try:
                    client, _ = server.accept()
                except socket.timeout:
                    continue
                with client:
                    client.settimeout(5)
                    try:
                        raw = b""
                        while b"\n" not in raw and len(raw) < 65536:
                            block = client.recv(4096)
                            if not block:
                                break
                            raw += block
                        response = {"ok": self.dispatch(json.loads(raw))}
                    except (
                        ValueError,
                        KeyError,
                        OSError,
                        subprocess.SubprocessError,
                    ) as e:
                        response = {"error": str(e)}
                    client.sendall((encode(response) + "\n").encode())
