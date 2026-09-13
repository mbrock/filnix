"""Bounded build clients and conservative ownership of unrealized dependencies."""

import json

from . import nix
from .attempt import directory


def build_policy(policy, active):
    """Reserve requested threads, including immutable limits of older workers.

    Nix's cores setting is a hint, so the workload cgroup remains the hard limit.
    Normally two clients split four jobs; a draining legacy client may leave room
    for only one smaller job. Never infer free slots from momentary CPU activity.
    """
    lanes = policy.get("build_lanes", 1) if policy.get("plan_ahead", 0) else 1
    if len(active) >= lanes:
        return None
    jobs, cores = max(1, policy["max_jobs"] // lanes), policy["cores"]
    remaining = len(nix.cpu_set(policy["cpus"]))
    for row in active:
        limits = json.loads(row["spec"])["policy"]
        if limits["max_jobs"] <= 0 or limits["cores"] <= 0:
            return None
        remaining -= limits["max_jobs"] * limits["cores"]
    if remaining < 1 or cores < 1:
        return None
    jobs = min(jobs, max(1, remaining // cores))
    cores = min(cores, remaining // jobs)
    return dict(policy, max_jobs=jobs, cores=cores)


class BuildGraph:
    def __init__(self, db):
        self.db = db
        self.cache = {}

    def outputs(self, drv):
        if drv not in self.cache:
            row = self.db.execute(
                "SELECT outputs FROM derivations WHERE drv=?", (drv,)
            ).fetchone()
            self.cache[drv] = json.loads(row[0]) if row else {}
        return self.cache[drv]

    def paths(self, drvs):
        return {p for d in drvs for p in self.outputs(d).values() if p}

    def needed(self, targets, available, held=()):
        """Stop at available required outputs, not at the full derivation closure.

        A held derivation is included even if a later observer saw its outputs:
        ownership lasts until reconciliation. Unknown output requirements retain
        the dependency conservatively. Iteration also handles deep graphs/cycles.
        """
        needed = set()
        todo = [(d, list(self.outputs(d))) for d in targets]
        while todo:
            drv, required = todo.pop()
            paths = {self.outputs(drv).get(k) for k in required}
            if drv not in held and paths and None not in paths and paths <= available:
                continue
            if drv in needed:
                continue
            needed.add(drv)
            for row in self.db.execute(
                "SELECT child,outputs FROM edges WHERE parent=?", (drv,)
            ):
                required = json.loads(row["outputs"])
                if isinstance(required, dict):
                    required = required.get("outputs", [])
                todo.append((row["child"], required))
        return needed


def reservations(db, state, active):
    graph = BuildGraph(db)
    held, available = set(), set()
    for row in db.execute("SELECT outputs FROM derivations WHERE available=1"):
        available.update(p for p in json.loads(row[0]).values() if p)
    for row in active:
        spec = json.loads(row["spec"])
        before_file = directory(state, row["id"]) / "before.json"
        before = (
            json.loads(before_file.read_text())
            if before_file.exists()
            else spec.get("admission_available", [])
        )
        available.update(before)
        held.update(graph.needed(spec["targets"], set(before)))
    return graph, held, available
