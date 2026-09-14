"""Worker-observed activity times. Historical untimed logs stay untimed."""

import json
import math

from .model import atomic_json, stamp
from .nix import DRV

LIMIT = 4 * 1024**2


class BuildTimes:
    def __init__(self, folder):
        self.path = folder / "build-times.json"
        self.rows, self.pending = {}, b""
        self.skipping = False

    def feed(self, data):
        self.pending += data
        changed = False
        while b"\n" in self.pending:
            line, self.pending = self.pending.split(b"\n", 1)
            if self.skipping:
                self.skipping = False
                continue
            if not line.startswith(b"@nix "):
                continue
            try:
                e = json.loads(line[5:])
                key = str(e.get("id", ""))
                fields = e.get("fields", [])
                if (
                    e.get("action") == "start"
                    and e.get("type") == 105
                    and isinstance(fields, list)
                    and fields
                    and isinstance(fields[0], str)
                    and DRV.fullmatch(fields[0])
                    and key not in self.rows
                    and len(self.rows) < 10000
                ):
                    self.rows[key] = dict(drv=fields[0], started=stamp(), finished=None)
                    changed = True
                elif (
                    e.get("action") == "stop"
                    and key in self.rows
                    and self.rows[key]["finished"] is None
                ):
                    self.rows[key]["finished"] = stamp()
                    changed = True
            except (ValueError, TypeError, AttributeError):
                pass
        if len(self.pending) > 1024**2:
            self.pending, self.skipping = b"", True
        if changed:
            atomic_json(self.path, self.rows)


def ingest_times(db, folder, aid):
    try:
        with (folder / "build-times.json").open("rb") as f:
            raw = f.read(LIMIT + 1)
        if len(raw) > LIMIT:
            return
        rows = json.loads(raw)
        if not isinstance(rows, dict):
            return
    except (OSError, ValueError):
        return
    for activity, row in rows.items():
        if not isinstance(row, dict):
            continue
        if not isinstance(row.get("drv"), str):
            continue
        start, end = row.get("started"), row.get("finished")
        if type(start) not in (int, float) or not math.isfinite(start):
            continue
        if end is not None and (
            type(end) not in (int, float) or not math.isfinite(end) or end < start
        ):
            end = None
        if not db.execute(
            "SELECT 1 FROM activities WHERE attempt=? AND activity=? AND drv=?",
            (aid, activity, row.get("drv")),
        ).fetchone():
            continue
        db.execute(
            "INSERT OR IGNORE INTO build_times VALUES(?,?,?,?)",
            (aid, activity, start, end),
        )
        if end is not None:
            db.execute(
                "UPDATE build_times SET finished=? WHERE attempt=? AND activity=? AND finished IS NULL",
                (end, aid, activity),
            )
