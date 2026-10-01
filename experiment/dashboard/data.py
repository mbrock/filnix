"""One SQLite read transaction per representation; no Nix work or viewer state."""

import json
import threading
from collections import deque
from contextlib import contextmanager

from starlette.exceptions import HTTPException

from ..batches import batches
from ..blockers import ranking
from ..catalog import catalog
from ..graph import live_graph as live_graph
from ..evidence import attempt_evidence, failure_evidence
from ..history import COLUMNS, attempt_detail, item
from ..logs import build_log
from ..model import connect, stamp
from ..web import detail


_locations = {}
_location_lock = threading.Lock()


def build_location(db, aid):
    # Specs are immutable and can contain megabytes of admission observations.
    # SQLite parses the whole JSON even to extract one small field. Share that
    # allocation across readers, and retain only bounded placement metadata.
    with _location_lock:
        if aid not in _locations:
            location = db.execute(
                "SELECT json_extract(spec,'$.build_location') FROM attempts WHERE id=?",
                (aid,),
            ).fetchone()[0]
            if len(_locations) >= 128:
                del _locations[next(iter(_locations))]
            _locations[aid] = location or "mixed"
        return _locations[aid]


@contextmanager
def read(state):
    db = connect(state, readonly=True)
    try:
        db.execute("BEGIN")
        yield db
    finally:
        db.close()


def campaigns(db):
    return [
        dict(r)
        for r in db.execute(
            "SELECT id,name,mode,revision,created FROM campaigns ORDER BY created DESC"
        )
    ]


def default_campaign(db):
    rows = campaigns(db)
    if not rows:
        raise HTTPException(404, "No campaigns have been imported")
    return next((r for r in rows if r["mode"] == "running"), rows[0])["id"]


def campaign(db, cid):
    row = db.execute("SELECT * FROM campaigns WHERE id=?", (cid,)).fetchone()
    if not row:
        raise HTTPException(404, "Campaign not found")
    result = dict(row)
    for key in ("manifest", "policy"):
        result[key] = json.loads(result[key])
    return result


def revision(db, cid):
    return db.execute(
        "SELECT coalesce(max(seq),0) FROM events WHERE campaign=?", (cid,)
    ).fetchone()[0]


def finished(db, cid):
    return (
        not db.execute(
            "SELECT 1 FROM candidates WHERE campaign=? AND state IN ('unplanned','queued','running') LIMIT 1",
            (cid,),
        ).fetchone()
        and not db.execute(
            "SELECT 1 FROM attempts WHERE campaign=? AND state!='finished' LIMIT 1",
            (cid,),
        ).fetchone()
    )


def summary(db, cid):
    c = campaign(db, cid)
    counts = dict(
        db.execute(
            "SELECT state,count(*) FROM candidates WHERE campaign=? GROUP BY state",
            (cid,),
        )
    )
    tested = db.execute(
        """SELECT count(DISTINCT c.drv) FROM candidates c
        WHERE c.campaign=? AND c.state='available' AND EXISTS (
            SELECT 1 FROM tests t JOIN attempts a ON a.id=t.attempt
            WHERE t.drv=c.drv AND a.campaign=?)""",
        (cid, cid),
    ).fetchone()[0]
    active = [
        dict(
            item(db, row),
            location=build_location(db, row["id"]) if row["kind"] == "build" else None,
        )
        for row in db.execute(
            f"SELECT {COLUMNS} FROM attempts WHERE campaign=? AND state!='finished' ORDER BY created",
            (cid,),
        )
    ]
    now, walk = stamp(), ranking(db, cid)
    done = not active and not any(
        counts.get(s, 0) for s in ("unplanned", "queued", "running")
    )
    return dict(
        campaign=c,
        counts=counts,
        tested=tested,
        active=active,
        monitor=build_forest(db, active, walk["scope"], now),
        total=sum(counts.values()),
        done=done,
        now=now,
        revision=revision(db, cid),
        blockers=walk["rows"][:5],
    )


def build_forest(db, active, scope, now):
    """Bounded paths from observed build activities to their request roots.

    This is a partial observation, not a scheduler or a full closure walk. A
    shared dependency appears once per request; unconnected activities remain
    visible without inventing an edge. No store queries happen on HTML reads.
    """
    groups, parents, records = [], {}, {}
    budget = 256
    for request in (a for a in active if a["kind"] == "build"):
        roots = {t["drv"]: t["label"] for t in request["targets"]}
        observed = {}
        for row in db.execute(
            """SELECT a.drv,a.phase,a.stopped,b.started,b.finished
            FROM activities a LEFT JOIN build_times b
              ON b.attempt=a.attempt AND b.activity=a.activity
            WHERE a.attempt=? AND a.kind='build' AND a.drv IS NOT NULL
            ORDER BY a.stopped,a.rowid DESC LIMIT 25""",
            (request["id"],),
        ):
            observed.setdefault(row["drv"], dict(row))
        tree, detached, nodes, placed = {}, [], {}, {}

        def node(drv):
            if drv not in nodes:
                if drv not in records:
                    row = db.execute(
                        "SELECT name,available,failure,exclusion FROM derivations WHERE drv=?",
                        (drv,),
                    ).fetchone()
                    records[drv] = dict(row) if row else {}
                record, activity = records[drv], observed.get(drv)
                state = (
                    "awaiting-result"
                    if activity
                    and (activity["stopped"] or activity["finished"] is not None)
                    else "building"
                    if activity
                    else "excluded"
                    if record.get("exclusion")
                    else "available"
                    if record.get("available")
                    else "failed"
                    if record.get("failure")
                    else "waiting"
                )
                elapsed = None
                if activity and activity["started"] is not None:
                    end = (
                        activity["finished"]
                        if activity["finished"] is not None
                        else now
                    )
                    elapsed = max(0, end - activity["started"])
                nodes[drv] = dict(
                    drv=drv,
                    name=roots.get(drv)
                    or record.get("name")
                    or drv.rsplit("/", 1)[-1][33:-4],
                    state=state,
                    phase=activity["phase"] if activity else None,
                    elapsed=elapsed,
                )
            return nodes[drv]

        # Paths are chosen deterministically, with a depth and query budget.
        # This avoids walking every cached compiler/tool ancestor on each tick.
        for drv in list(observed)[:24]:
            if observed[drv]["stopped"] or observed[drv]["finished"] is not None:
                continue
            todo, seen, path = deque([(drv, [drv])]), {drv}, None
            while todo:
                current, chain = todo.popleft()
                if current in placed:
                    path = placed[current] + list(reversed(chain[:-1]))
                    break
                if current in roots:
                    path = list(reversed(chain))
                    break
                if len(chain) >= 8:
                    continue
                if current not in parents:
                    if not budget:
                        break
                    parents[current] = [
                        r[0]
                        for r in db.execute(
                            "SELECT parent FROM edges WHERE child=? ORDER BY parent LIMIT 33",
                            (current,),
                        )
                        if r[0] in scope
                    ]
                    budget -= 1
                for parent in parents[current][:32]:
                    if parent not in seen:
                        seen.add(parent)
                        todo.append((parent, chain + [parent]))
            if path and len(path) <= 8:
                branch = tree
                for depth, ancestor in enumerate(path):
                    node(ancestor)
                    placed[ancestor] = path[: depth + 1]
                    branch = branch.setdefault(ancestor, {})
            else:
                detached.append(node(drv))
        if len(roots) == 1:
            node(next(iter(roots)))
        settling = [
            node(d)
            for d in list(observed)[:24]
            if d not in nodes
            and (observed[d]["stopped"] or observed[d]["finished"] is not None)
        ]
        groups.append(
            dict(
                request=request,
                tree=tree,
                detached=detached,
                settling=settling,
                nodes=nodes,
                hidden_roots=[
                    dict(drv=d, name=name) for d, name in roots.items() if d not in tree
                ],
                partial=len(observed) > 24 or bool(detached),
            )
        )
    return groups


def selected(row, state):
    return {
        "all": True,
        "available": row["state"] == "available",
        "tested": row["state"] == "available" and bool(row["checks"]),
        "failed": row["state"] == "failed",
        "failures": row["state"] in ("failed", "evaluation-error", "inconclusive"),
        "blocked": row["state"] == "blocked",
        "evaluation-error": row["state"] == "evaluation-error",
        "tried": row["state"] not in ("unplanned", "queued"),
    }[state]


def packages(db, cid, view):
    result = catalog(db, cid)
    result["rows"] = [r for r in result["rows"] if selected(r, view.state)]
    result["revision"] = revision(db, cid)
    result["sampled"] = int(stamp())
    result["done"] = finished(db, cid)
    return result


def ledger(db, cid, view, *, recent=False):
    result = batches(db, cid, recent=recent)
    rows = result["rows"]
    if view.kind:
        rows = [r for r in rows if r["kind"] == view.kind]
    if view.outcome:
        rows = [r for r in rows if r["outcome"] == view.outcome]
    if view.q:
        q = view.q.lower()
        rows = [
            r
            for r in rows
            if q in r["id"] or any(q in name.lower() for name in r["names"])
        ]
    if view.sort == "longest":
        rows.sort(
            key=lambda r: (
                r["duration"] if r["duration"] is not None else -1,
                r["created"],
            ),
            reverse=True,
        )
    else:
        rows.sort(key=lambda r: (r["created"], r["id"]), reverse=view.sort != "oldest")
    result["rows"] = rows
    result["done"] = finished(db, cid)
    return result


def batch(db, cid, aid):
    if not db.execute(
        "SELECT 1 FROM attempts WHERE campaign=? AND id=?", (cid, aid)
    ).fetchone():
        raise HTTPException(404, "Batch not found in this campaign")
    return attempt_detail(db, cid, aid)


def package(db, cid, pid):
    if not db.execute(
        "SELECT 1 FROM candidates WHERE campaign=? AND id=?", (cid, pid)
    ).fetchone():
        raise HTTPException(404, "Package not found in this campaign")
    result = detail(db, pid)
    result["done"] = finished(db, cid)
    result["sampled"] = stamp()
    build = db.execute(
        """SELECT a.attempt FROM activities a JOIN attempts t ON t.id=a.attempt
        WHERE a.drv=? AND a.kind='build' AND t.campaign=?
        ORDER BY t.created DESC LIMIT 1""",
        (result["drv"], cid),
    ).fetchone()
    result["log"] = attempt_evidence(db, build[0], result["drv"]) if build else None
    if result["state"] == "failed":
        result["log"] = failure_evidence(db, result["drv"]) or result["log"]
    plan = db.execute(
        """SELECT id FROM attempts WHERE campaign=? AND kind='plan' AND EXISTS (
        SELECT 1 FROM json_each(targets) WHERE json_extract(value,'$.id')=?)
        ORDER BY created DESC LIMIT 1""",
        (cid, pid),
    ).fetchone()
    result["plan"] = attempt_evidence(db, plan[0], "") if plan else None
    result["blockers"] = [b for b in result["blockers"] if b["drv"] != result["drv"]]
    for blocker in result["blockers"]:
        blocker["evidence"] = failure_evidence(db, blocker["drv"])
    return result


def log(db, state, cid, aid, view, direction="tail", cursor=0):
    if not db.execute(
        "SELECT 1 FROM attempts WHERE campaign=? AND id=?", (cid, aid)
    ).fetchone():
        raise HTTPException(404, "Log not found in this campaign")
    result = build_log(db, state, aid, direction, cursor, view.drv)
    # Seek backwards in bounded requests, including for explicit Earlier output.
    # Large batches can have hundreds of megabytes after a dependency failed.
    result["searching"] = False
    if direction in ("tail", "before") and view.drv and not result["reset"]:
        observed = any(s["drv"] == view.drv for s in result["sources"])
        if observed:
            for _ in range(7):
                if result["entries"] or not result["before"]:
                    break
                result = build_log(db, state, aid, "before", result["start"], view.drv)
        result["searching"] = bool(
            observed and not result["entries"] and result["before"]
        )

    return result


def latest_build(db, cid):
    return db.execute(
        """SELECT id FROM attempts WHERE campaign=?
        ORDER BY kind='build' DESC,state!='finished' DESC,created DESC LIMIT 1""",
        (cid,),
    ).fetchone()


def blockers(db, cid, view, size=50):
    result = dict(ranking(db, cid))
    rows = result["rows"]
    result["total"] = len(rows)
    result["page"] = view.page
    result["size"] = size
    result["rows"] = rows[view.page * size : (view.page + 1) * size]
    result["most"] = max((r["blocks"] for r in rows), default=0)
    for row in result["rows"]:
        row["evidence"] = failure_evidence(db, row["drv"])
    return result
