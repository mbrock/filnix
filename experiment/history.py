"""Read-only attempt history. Outcomes belong to attempts, never to today's outputs."""

import json

from .model import stamp

PAGE_SIZE = 24
TIMELINE_LIMIT = 400
BUCKETS = 160
COLUMNS = "id,campaign,kind,targets,state,created,finished,result,cancel_requested"
# Attempts are ordered by their immutable admission row, including tied timestamps.
OUTCOME = """CASE WHEN state!='finished' THEN 'active'
 WHEN json_extract(result,'$.reason')='completed' THEN 'complete'
 WHEN result IS NULL THEN 'unknown' ELSE 'error' END"""


def campaign_row(db, campaign):
    row = db.execute("SELECT * FROM campaigns WHERE id=?", (campaign,)).fetchone()
    if not row:
        raise ValueError("unknown campaign")
    return row


def reference(db, campaign, aid):
    row = db.execute(
        "SELECT rowid FROM attempts WHERE campaign=? AND id=?", (campaign, aid)
    ).fetchone()
    if not row:
        raise ValueError("unknown campaign attempt")
    return row[0]


def item(db, row):
    result = json.loads(row["result"]) if row["result"] else {}
    targets = []
    for target in json.loads(row["targets"]):
        if isinstance(target, dict):
            targets.append(dict(id=target["id"], label=".".join(target["attr"])))
        else:
            aliases = [
                dict(r)
                for r in db.execute(
                    "SELECT id,label FROM candidates WHERE campaign=? AND drv=? ORDER BY label LIMIT 8",
                    (row["campaign"], target),
                )
            ]
            targets.append(
                dict(
                    drv=target,
                    label=aliases[0]["label"]
                    if aliases
                    else target.split("/")[-1][33:-4],
                    aliases=aliases,
                )
            )
    builds = db.execute(
        "SELECT count(DISTINCT drv) FROM activities WHERE attempt=? AND kind='build'",
        (row["id"],),
    ).fetchone()[0]
    checks = db.execute(
        "SELECT count(DISTINCT drv) FROM tests WHERE attempt=?", (row["id"],)
    ).fetchone()[0]
    return dict(
        id=row["id"],
        kind=row["kind"],
        state=row["state"],
        created=row["created"],
        finished=row["finished"],
        reason=result.get("reason"),
        exit_code=result.get("exit_code"),
        error=str(result.get("error", ""))[:2000],
        cancel_requested=bool(row["cancel_requested"]),
        targets=targets,
        builds=builds,
        checks=checks,
    )


def overview(db, campaign, now, window=0):
    c = campaign_row(db, campaign)
    totals = dict(
        db.execute(
            f"SELECT {OUTCOME},count(*) FROM attempts WHERE campaign=? GROUP BY 1",
            (campaign,),
        )
    )
    bounds = db.execute(
        """SELECT min(created),max(CASE WHEN state!='finished' THEN ?
        ELSE coalesce(finished,created) END) FROM attempts WHERE campaign=?""",
        (now, campaign),
    ).fetchone()
    end = max(bounds[1] or now, c["created"] + 1)
    start = max(c["created"], end - window) if window else c["created"]
    width = max(1, end - start)
    counts = dict(
        db.execute(
            "SELECT kind,count(*) FROM attempts WHERE campaign=? GROUP BY kind",
            (campaign,),
        )
    )
    intervals = [
        dict(r)
        for r in db.execute(
            f"""SELECT id,kind,state,created,finished,{OUTCOME} AS outcome,
            json_extract(result,'$.reason') AS reason,json_array_length(targets) AS targets
            FROM attempts WHERE campaign=? AND created<=?
            AND coalesce(finished,?)>=? ORDER BY created,id LIMIT ?""",
            (campaign, end, now, start, TIMELINE_LIMIT + 1),
        )
    ]
    buckets = []
    if len(intervals) > TIMELINE_LIMIT:
        # Fixed-size duration occupancy, not a sample of recent attempts. An attempt
        # can touch several buckets; their counts must never be added as a total.
        buckets = [
            dict(r)
            for r in db.execute(
                f"""WITH RECURSIVE bins(n) AS (
                VALUES(0) UNION ALL SELECT n+1 FROM bins WHERE n<?)
                SELECT n,kind,{OUTCOME} AS outcome,count(*) AS count
                FROM bins JOIN attempts ON campaign=?
                  AND created < ?+(n+1)*?
                  AND coalesce(finished,?) >= ?+n*?
                GROUP BY n,kind,outcome ORDER BY n,kind,outcome""",
                (
                    BUCKETS - 1,
                    campaign,
                    start,
                    width / BUCKETS,
                    now,
                    start,
                    width / BUCKETS,
                ),
            )
        ]
        intervals = []
    return dict(
        start=start,
        end=end,
        created=c["created"],
        totals=totals,
        kinds=counts,
        intervals=intervals,
        buckets=buckets,
        bucket_count=BUCKETS,
    )


def history(
    db, campaign, anchor="", before="", kind="", outcome="", search="", window=0
):
    campaign_row(db, campaign)
    now = stamp()
    latest = db.execute(
        "SELECT id,rowid FROM attempts WHERE campaign=? ORDER BY rowid DESC LIMIT 1",
        (campaign,),
    ).fetchone()
    anchor_id = anchor or (latest["id"] if latest else "")
    anchor_row = reference(db, campaign, anchor_id) if anchor_id else 0
    params = [campaign, anchor_row]
    where = "t.campaign=? AND t.rowid<=?"
    if kind:
        if kind not in ("plan", "build"):
            raise ValueError("unknown attempt kind")
        where += " AND kind=?"
        params.append(kind)
    if outcome:
        if outcome not in ("active", "complete", "error", "unknown"):
            raise ValueError("unknown outcome")
        where += f" AND ({OUTCOME})=?"
        params.append(outcome)
    if search:
        where += """ AND (instr(lower(targets),lower(?))>0 OR instr(id,?)>0 OR EXISTS (
          SELECT 1 FROM candidates c WHERE c.campaign=t.campaign AND instr(lower(c.label),lower(?))>0
          AND EXISTS (SELECT 1 FROM json_each(t.targets) j
            WHERE CASE WHEN j.type='object' THEN json_extract(j.value,'$.id')=c.id
            ELSE j.value=c.drv END)))"""
        params.extend([search[:200]] * 3)
    total = db.execute(
        f"SELECT count(*) FROM attempts t WHERE {where}", params
    ).fetchone()[0]
    if before:
        where += " AND t.rowid<?"
        params.append(reference(db, campaign, before))
    rows = list(
        db.execute(
            f"SELECT {COLUMNS} FROM attempts t WHERE {where} ORDER BY rowid DESC LIMIT ?",
            (*params, PAGE_SIZE + 1),
        )
    )
    return dict(
        campaign=campaign,
        now=now,
        anchor=anchor_id,
        newer=db.execute(
            "SELECT count(*) FROM attempts WHERE campaign=? AND rowid>?",
            (campaign, anchor_row),
        ).fetchone()[0],
        total=total,
        more=len(rows) > PAGE_SIZE,
        rows=[item(db, r) for r in rows[:PAGE_SIZE]],
        overview=overview(db, campaign, now, window),
    )


def attempt_detail(db, campaign, aid):
    campaign_row(db, campaign)
    row = db.execute(
        f"SELECT {COLUMNS} FROM attempts WHERE campaign=? AND id=?", (campaign, aid)
    ).fetchone()
    if not row:
        raise ValueError("unknown campaign attempt")
    result = item(db, row)
    result["activities"] = [
        dict(r)
        for r in db.execute(
            """SELECT a.drv,coalesce(d.name,a.drv) AS name,a.phase,a.stopped,
            EXISTS(SELECT 1 FROM tests t WHERE t.attempt=a.attempt AND t.drv=a.drv) AS checked
            FROM activities a LEFT JOIN derivations d ON d.drv=a.drv
            WHERE a.attempt=? AND a.kind='build' ORDER BY a.stopped,a.rowid LIMIT 100""",
            (aid,),
        )
    ]
    return result
