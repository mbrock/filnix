"""Discard consumed planner scratch graphs, never retained build evidence."""

from contextlib import closing
import re

from .attempt import directory
from .model import connect, stamp


def prune_plans(state, apply=False):
    cutoff = stamp() - 86400
    # A separate read-only connection sees only committed terminal attempts.
    # Finish/recovery consumes graphs before that terminal transaction commits.
    with closing(connect(state, readonly=True)) as db:
        attempts = db.execute(
            "SELECT id FROM attempts WHERE kind='plan' AND state='finished' AND finished<=?",
            (cutoff,),
        ).fetchall()
    files = total = affected = 0
    for attempt in attempts:
        found = False
        for path in directory(state, attempt["id"]).glob("graph-*"):
            if not re.fullmatch(r"graph-\d+\.(json(?:\.gz|\.tmp)?|tmp)", path.name):
                continue
            if path.is_symlink() or not path.is_file():
                continue
            size = path.stat().st_size
            if apply:
                path.unlink()
            files += 1
            total += size
            found = True
        affected += found
    return dict(
        dry_run=not apply,
        cutoff=cutoff,
        attempts=affected,
        files=files,
        logical_bytes=total,
    )
