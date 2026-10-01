"""Complete, read-only batch ledger. Wall times belong to jobs, not packages."""

from collections import defaultdict
import json

from .history import batch_status, campaign_row, OUTCOME
from .model import stamp


def batches(db, campaign, *, recent=False):
    campaign_row(db, campaign)
    now = stamp()
    where, params = "campaign=?", (campaign,)
    if recent:
        # The live overview needs a small history window and eight completed
        # builds even when many planning requests finished between builds.
        ids = [
            r[0]
            for r in db.execute(
                """WITH latest AS (SELECT id FROM attempts WHERE campaign=?
                    ORDER BY created DESC,id DESC LIMIT 40),
                completed AS (SELECT id FROM attempts WHERE campaign=?
                    AND kind='build' AND state='finished'
                    ORDER BY created DESC,id DESC LIMIT 8)
                SELECT id FROM latest UNION SELECT id FROM completed""",
                (campaign, campaign),
            )
        ]
        where += " AND id IN (" + ",".join("?" for _ in ids) + ")"
        params += tuple(ids)
    aliases = defaultdict(list)
    for row in db.execute(
        "SELECT drv,label FROM candidates WHERE campaign=? AND drv IS NOT NULL ORDER BY label",
        (campaign,),
    ):
        aliases[row["drv"]].append(row["label"])
    observed = defaultdict(dict)
    for row in db.execute(
        f"""SELECT DISTINCT a.attempt,a.drv,coalesce(d.name,a.drv) AS name
        FROM activities a
        LEFT JOIN derivations d ON d.drv=a.drv
        WHERE a.attempt IN (SELECT id FROM attempts WHERE {where})
        AND a.kind='build' AND a.drv IS NOT NULL""",
        params,
    ):
        observed[row["attempt"]][row["drv"]] = row["name"]
    tested = dict(
        db.execute(
            f"""SELECT t.attempt,count(DISTINCT t.drv) FROM tests t
            WHERE t.attempt IN (SELECT id FROM attempts WHERE {where})
            GROUP BY t.attempt""",
            params,
        )
    )
    rows = []
    for row in db.execute(
        f"""SELECT id,kind,state,created,finished,targets,{OUTCOME} AS outcome,
        json_extract(result,'$.reason') AS reason FROM attempts
        WHERE {where} ORDER BY created,id""",
        params,
    ):
        r = dict(row)
        roots = []
        names = set()
        for target in json.loads(r.pop("targets")):
            if isinstance(target, dict):
                label = ".".join(target["attr"])
                roots.append(label)
                names.add(label)
            else:
                labels = aliases.get(target) or [target.rsplit("/", 1)[-1][33:-4]]
                roots.append(labels[0])
                names.update(labels)
        builds = observed[r["id"]]
        names.update(builds.values())
        # A terminal job without a finish timestamp has an unknown duration.
        # In-flight durations are elapsed observations, frozen with this snapshot.
        end = now if r["state"] != "finished" else r["finished"]
        duration = max(0, end - r["created"]) if end is not None else None
        r.update(
            status=batch_status(r["state"], r["reason"]),
            duration=duration,
            roots=roots,
            names=sorted(names),
            builds=len(builds),
            tested=tested.get(r["id"], 0),
        )
        rows.append(r)
    cursor = db.execute(
        "SELECT coalesce(max(seq),0) FROM events WHERE campaign=?", (campaign,)
    ).fetchone()[0]
    total = (
        db.execute(
            "SELECT count(*) FROM attempts WHERE campaign=?", (campaign,)
        ).fetchone()[0]
        if recent
        else len(rows)
    )
    return dict(campaign=campaign, now=now, cursor=cursor, rows=rows, total=total)
