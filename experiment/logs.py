"""Read-only, bounded windows into captured Nix logs. Cursors are raw byte offsets."""

import json
import re

from .attempt import directory
from .nix import DRV

PAGE = 256 * 1024
MAX_LINE = 1024 * 1024
ANSI = re.compile(
    r"\x1b\][^\x07\x1b]*(?:\x07|\x1b\\)|\x1b\[[0-?]*[ -/]*[@-~]|\x1b[@-_]"
)
CONTROL = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")
ERROR = re.compile(r"\b(?:error:|fatal:|FAILED|FAIL:|panic:|safety error)", re.I)


def clean(text):
    text = CONTROL.sub("", ANSI.sub("", text))
    # A carriage return replaces a terminal progress line, not the whole entry.
    return "\n".join(line.split("\r")[-1] for line in text.split("\n"))


def decode(raw, offset, activities):
    text, drv, kind = raw.decode(errors="replace").rstrip("\n"), None, "output"
    if text.startswith("@nix "):
        try:
            e = json.loads(text[5:])
        except ValueError:
            e = None
        if isinstance(e, dict):
            action, fields = e.get("action"), e.get("fields", [])
            if not isinstance(fields, list):
                return None
            drv = activities.get(str(e.get("id")))
            if action == "start" and e.get("type") == 105 and fields:
                if not isinstance(fields[0], str) or not DRV.fullmatch(fields[0]):
                    return None
                drv = fields[0]
                activities[str(e.get("id"))] = drv
                text, kind = "Build started", "phase"
            elif action == "result" and e.get("type") in (101, 104) and fields:
                if not isinstance(fields[0], str):
                    return None
                text = fields[0]
                if e["type"] == 104:
                    text, kind = "→ " + text, "phase"
                elif text.startswith("Running phase: "):
                    return None  # The explicit phase event carries this too.
            elif action == "msg" and isinstance(e.get("msg"), str):
                text = e["msg"]
                kind = "error" if e.get("level") == 0 else "message"
                match = DRV.search(clean(text))
                drv = match.group() if match else None
            else:
                return None  # Progress counters and cache queries are not build output.
    text = clean(text)
    if not text.strip():
        return None
    if ERROR.search(text):
        kind = "error"
    return dict(offset=offset, drv=drv, kind=kind, text=text)


def window(path, size, direction, cursor, finished):
    """Return aligned records; never consume a torn live line or split UTF-8."""
    if direction not in ("tail", "before", "after"):
        raise ValueError("invalid log direction")
    cursor = max(0, min(cursor, size))
    end = cursor if direction == "before" else size
    start = cursor if direction == "after" else max(0, end - PAGE)
    records, skipped = [], False
    if not path.exists():
        return 0, 0, records, skipped
    with path.open("rb") as f:
        # Both directions start at a record boundary, including user-supplied cursors.
        if start:
            f.seek(start - 1)
            if f.read(1) != b"\n":
                fragment = f.readline(min(MAX_LINE, end - start))
                aligned = f.tell()
                if not fragment.endswith(b"\n") or aligned >= end:
                    return start, aligned, [], True
                start = aligned
        f.seek(start)
        stop = min(end, start + PAGE) if direction == "after" else end
        pos = start
        while pos < stop:
            raw = f.readline(min(MAX_LINE, end - pos))
            if not raw:
                break
            complete = raw.endswith(b"\n")
            if not complete and f.tell() == end and not finished:
                break
            if not complete and len(raw) == MAX_LINE:
                # Bound memory/work even for pathological records; keep raw evidence.
                skipped = True
            else:
                records.append((pos, raw))
            pos = f.tell()
            if skipped:
                break
    return start, pos, records, skipped


def build_log(db, state, aid, direction="tail", cursor=0, drv=""):
    attempt = db.execute(
        "SELECT id,campaign,kind,state,created,finished,result,offset FROM attempts WHERE id=?",
        (aid,),
    ).fetchone()
    if not attempt:
        raise ValueError("unknown attempt")
    if drv and not DRV.fullmatch(drv):
        raise ValueError("invalid derivation")
    info = dict(attempt)
    info["result"] = json.loads(info["result"]) if info["result"] else None
    sources = [
        dict(r)
        for r in db.execute(
            """SELECT a.activity,a.drv,a.phase,a.stopped,d.name FROM activities a
        LEFT JOIN derivations d ON d.drv=a.drv WHERE a.attempt=? ORDER BY a.stopped,a.drv""",
            (aid,),
        )
    ]
    activities = {a["activity"]: a["drv"] for a in sources}
    path = directory(state, aid) / "stderr.log"
    captured = path.stat().st_size if path.exists() else 0
    finished = info["state"] not in ("running", "intended")
    # Wait for the controller's atomic activity/offset commit, so a new line is
    # never consumed before its owning build is known. Terminal fragments stay visible.
    indexed = info.pop("offset")
    size = captured if finished else min(captured, indexed)
    reset = cursor > size
    if direction == "status":
        start, end, raw, skipped = cursor, cursor, [], False
    else:
        start, end, raw, skipped = window(path, size, direction, cursor, finished)
    entries = []
    for pos, line in raw:
        entry = decode(line, pos, activities)
        if entry and (not drv or entry["drv"] == drv):
            entries.append(entry)
    return dict(
        attempt=info,
        sources=sources,
        entries=entries,
        start=start,
        end=end,
        size=size,
        captured=captured,
        before=start > 0,
        more=end < size,
        reset=reset,
        skipped=skipped,
        finished=finished,
    )
