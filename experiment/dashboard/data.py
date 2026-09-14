"""One SQLite read transaction per representation; no Nix work or viewer state."""

import json
from contextlib import contextmanager

from starlette.exceptions import HTTPException

from ..batches import batches
from ..catalog import catalog
from ..graph import live_graph as live_graph
from ..history import COLUMNS, attempt_detail, item
from ..logs import build_log
from ..model import connect, stamp
from ..web import detail


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
        item(db, row)
        for row in db.execute(
            f"SELECT {COLUMNS} FROM attempts WHERE campaign=? AND state!='finished' ORDER BY created",
            (cid,),
        )
    ]
    builds = [
        dict(row)
        for row in db.execute(
            """SELECT a.attempt,a.drv,a.phase,d.name
        FROM activities a JOIN attempts t ON t.id=a.attempt
        LEFT JOIN derivations d ON d.drv=a.drv
        WHERE t.campaign=? AND t.state='running' AND a.kind='build' AND a.stopped=0
        ORDER BY a.rowid DESC LIMIT 24""",
            (cid,),
        )
    ]
    done = not active and not any(
        counts.get(s, 0) for s in ("unplanned", "queued", "running")
    )
    return dict(
        campaign=c,
        counts=counts,
        tested=tested,
        active=active,
        builds=builds,
        total=sum(counts.values()),
        done=done,
        now=stamp(),
        revision=revision(db, cid),
    )


def selected(row, state):
    return {
        "all": True,
        "available": row["state"] == "available",
        "tested": row["state"] == "available" and bool(row["checks"]),
        "failed": row["state"] in ("failed", "evaluation-error", "inconclusive"),
        "blocked": row["state"] == "blocked",
        "evaluation-error": row["state"] == "evaluation-error",
        "tried": row["state"] not in ("unplanned", "queued"),
    }[state]


def packages(db, cid, view):
    result = catalog(db, cid)
    result["rows"] = [r for r in result["rows"] if selected(r, view.state)]
    result["revision"] = revision(db, cid)
    result["done"] = finished(db, cid)
    return result


def ledger(db, cid, view):
    result = batches(db, cid)
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
    # Restrict direct check evidence to this campaign, as in the package list.
    result["tests"] = [
        dict(r)
        for r in db.execute(
            """SELECT t.* FROM tests t
        JOIN attempts a ON a.id=t.attempt WHERE t.drv=? AND a.campaign=?""",
            (result["drv"], cid),
        )
    ]
    result["log"] = db.execute(
        """SELECT a.attempt FROM activities a
        JOIN attempts t ON t.id=a.attempt WHERE a.drv=? AND t.campaign=?
        ORDER BY t.created DESC LIMIT 1""",
        (result["drv"], cid),
    ).fetchone()
    if result["log"] is None:
        result["log"] = db.execute(
            """SELECT id FROM attempts
            WHERE campaign=? AND kind='plan' AND EXISTS (
                SELECT 1 FROM json_each(targets) WHERE json_extract(value,'$.id')=?)
            ORDER BY created DESC LIMIT 1""",
            (cid, pid),
        ).fetchone()
    return result


def log(db, state, cid, aid, view, direction="tail", cursor=0):
    if not db.execute(
        "SELECT 1 FROM attempts WHERE campaign=? AND id=?", (cid, aid)
    ).fetchone():
        raise HTTPException(404, "Log not found in this campaign")
    result = build_log(db, state, aid, direction, cursor, view.drv)
    # Quiet scoped logs scan a bounded number of older windows on initial load.
    if direction == "tail" and view.drv:
        for _ in range(7):
            if result["entries"] or not result["before"]:
                break
            result = build_log(db, state, aid, "before", result["start"], view.drv)
    return result


def latest_build(db, cid):
    return db.execute(
        """SELECT id FROM attempts WHERE campaign=?
        ORDER BY kind='build' DESC,state!='finished' DESC,created DESC LIMIT 1""",
        (cid,),
    ).fetchone()
