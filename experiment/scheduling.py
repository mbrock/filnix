"""Bounded build clients and conservative ownership of unrealized dependencies."""

import json

from . import nix
from .attempt import directory


def build_policy(policy, active, location="local", machines=()):
    """Reserve requested threads, including immutable limits of older workers.

    Nix's cores setting is a hint, so the workload cgroup remains the hard limit.
    Normally two clients split four jobs; a draining legacy client may leave room
    for only one smaller job. Never infer free slots from momentary CPU activity.
    """
    rolling = policy.get("scheduling") == "rolling"
    if rolling and location == "remote":
        occupied = sum(
            json.loads(r["spec"]).get("build_location") == "remote" for r in active
        )
        if occupied >= sum(m["max_jobs"] for m in machines):
            return None
        return dict(policy, max_jobs=0)
    if rolling:
        active = [
            r for r in active if json.loads(r["spec"]).get("build_location") != "remote"
        ]
    lanes = (
        policy["max_jobs"]
        if rolling
        else policy.get("build_lanes", 1)
        if policy.get("plan_ahead", 0)
        else 1
    )
    if len(active) >= lanes:
        return None
    jobs, cores = 1 if rolling else max(1, policy["max_jobs"] // lanes), policy["cores"]
    remaining = len(nix.cpu_set(policy["cpus"]))
    remaining_jobs = policy["max_jobs"]
    for row in active:
        limits = json.loads(row["spec"])["policy"]
        if limits["max_jobs"] <= 0 or limits["cores"] <= 0:
            return None
        remaining -= limits["max_jobs"] * limits["cores"]
        remaining_jobs -= limits["max_jobs"]
    if rolling and (remaining_jobs < 1 or remaining < cores):
        return None
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

    def needed(self, targets, available):
        """Stop at available required outputs, not at the full derivation closure.

        Store-verified outputs release dependency reservations immediately.
        Unknown output requirements retain the dependency conservatively.
        Iteration also handles deep graphs/cycles and unions output requirements
        when different branches need different outputs of the same derivation.
        """
        needed = set()
        todo = [(d, list(self.outputs(d))) for d in targets]
        while todo:
            drv, required = todo.pop()
            paths = {self.outputs(drv).get(k) for k in required}
            if paths and None not in paths and paths <= available:
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

    def remote_eligible(self, drvs, machines):
        for drv in drvs:
            row = self.db.execute(
                "SELECT metadata FROM derivations WHERE drv=?", (drv,)
            ).fetchone()
            info = json.loads(row[0]) if row and row[0] else {}
            required = set(info.get("features", []))
            if info.get("local_only") or not any(
                info.get("system") in m["systems"]
                and required <= set(m["supported"])
                and set(m["mandatory"]) <= required
                for m in machines
            ):
                return False
        return True


def reservations(db, state, active, observed=()):
    graph = BuildGraph(db)
    held, available = set(), set(observed)
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
    # Only realized outputs, not activity-stop events, release ownership. This
    # changes scheduling observations, not persisted build or check evidence.
    available.update(nix.valid(graph.paths(held)))
    held = set().union(
        *(graph.needed(json.loads(row["spec"])["targets"], available) for row in active)
    )
    return graph, held, available
