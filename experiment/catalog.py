"""Compact, complete package inventory. No evaluation or log scanning on reads."""

import json
import re
from urllib.parse import quote

from .model import stamp


def source_link(manifest, selection):
    pin = manifest.get("nixpkgs", {})
    path = selection.get("sourceFile") or ""
    if (
        not isinstance(path, str)
        or not path.startswith("pkgs/")
        or ".." in path.split("/")
    ):
        return None
    if pin.get("type") != "github" or not all(
        re.fullmatch(r"[A-Za-z0-9_.-]+", str(pin.get(k, "")))
        for k in ("owner", "repo", "rev")
    ):
        return None
    position = (selection.get("metadata") or {}).get("position") or ""
    line = re.search(r":(\d+)$", position)
    return (
        f"https://github.com/{pin['owner']}/{pin['repo']}/blob/{pin['rev']}/"
        + quote(path, safe="/")
        + ("#L" + line[1] if line else "")
    )


def catalog(db, campaign):
    c = db.execute("SELECT manifest FROM campaigns WHERE id=?", (campaign,)).fetchone()
    if not c:
        raise ValueError("unknown campaign")
    manifest = json.loads(c[0])
    now = stamp()
    attempts, roots, plans = {}, {}, {}
    for r in db.execute(
        "SELECT id,kind,targets,state,created,finished FROM attempts WHERE campaign=? ORDER BY created,id",
        (campaign,),
    ):
        a = dict(r)
        targets = json.loads(a.pop("targets"))
        attempts[a["id"]] = a
        for target in targets:
            if a["kind"] == "build" and isinstance(target, str):
                roots[target] = a
            elif a["kind"] == "plan" and isinstance(target, dict):
                plans[target.get("id")] = a
    activities = {}
    for r in db.execute(
        """SELECT a.*,b.started,b.finished FROM activities a
        JOIN attempts t ON t.id=a.attempt
        LEFT JOIN build_times b ON b.attempt=a.attempt AND b.activity=a.activity
        WHERE t.campaign=? ORDER BY t.created,t.id,a.rowid""",
        (campaign,),
    ):
        activities[r["drv"]] = dict(r)
    checks = {}
    for r in db.execute(
        """SELECT t.drv,t.phase FROM tests t JOIN attempts a ON a.id=t.attempt
        WHERE a.campaign=?""",
        (campaign,),
    ):
        checks.setdefault(r["drv"], set()).add(r["phase"])
    rows = []
    for r in db.execute(
        """SELECT c.id,c.label,c.state,c.drv,c.selection,c.error,d.failure
        FROM candidates c LEFT JOIN derivations d ON d.drv=c.drv
        WHERE c.campaign=? ORDER BY c.label""",
        (campaign,),
    ):
        p = dict(r)
        selection = json.loads(p.pop("selection"))
        meta = selection.get("metadata") or {}
        activity = activities.get(p["drv"])
        a = roots.get(p["drv"])
        observed = attempts[activity["attempt"]] if activity else None
        if observed and (not a or observed["created"] > a["created"]):
            a = observed
        a = a or plans.get(p["id"])
        duration, timing, time_attempt = None, None, None
        if activity and activity["started"] is not None:
            if activity["finished"] is not None:
                duration = activity["finished"] - activity["started"]
                timing = "build"
            elif observed["state"] == "running" and not activity["stopped"]:
                duration, timing = max(0, now - activity["started"]), "building"
            time_attempt = observed["id"]
        # Older workers recorded batch times only. Never present them as build times.
        if duration is None and a and a["finished"] is not None:
            duration = max(0, a["finished"] - a["created"])
            timing = "eval-batch" if a["kind"] == "plan" else "batch"
            time_attempt = a["id"]
        error = p.pop("error") or p.pop("failure") or ""
        p.pop("failure", None)
        p.update(
            description=meta.get("description") or "",
            version=meta.get("version") or "",
            source=selection.get("sourceFile") or "",
            source_url=source_link(manifest, selection),
            reason=error[:500],
            checks=sorted(checks.get(p["drv"], [])) if p["state"] != "excluded" else [],
            phase=activity["phase"] if activity else None,
            duration=duration,
            timing=timing,
            time_attempt=time_attempt,
            attempt=a["id"] if a else None,
            log_drv=p["drv"]
            if a
            and a["kind"] == "build"
            and activity
            and a["id"] == activity["attempt"]
            else None,
            last=a["finished"] or a["created"] if a else None,
        )
        rows.append(p)
    return dict(
        campaign=campaign,
        rows=rows,
        now=now,
        cursor=db.execute("SELECT coalesce(max(seq),0) FROM events").fetchone()[0],
    )
