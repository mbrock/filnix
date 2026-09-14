"""Complete, read-only batch ledger. Wall times belong to jobs, not packages."""

from collections import defaultdict
import json

from .history import campaign_row, OUTCOME
from .model import stamp


def batches(db, campaign):
    campaign_row(db, campaign)
    now = stamp()
    aliases = defaultdict(list)
    for row in db.execute(
        "SELECT drv,label FROM candidates WHERE campaign=? AND drv IS NOT NULL ORDER BY label",
        (campaign,),
    ):
        aliases[row["drv"]].append(row["label"])
    observed = defaultdict(dict)
    for row in db.execute(
        """SELECT DISTINCT a.attempt,a.drv,coalesce(d.name,a.drv) AS name
        FROM activities a JOIN attempts t ON t.id=a.attempt
        LEFT JOIN derivations d ON d.drv=a.drv
        WHERE t.campaign=? AND a.kind='build' AND a.drv IS NOT NULL""",
        (campaign,),
    ):
        observed[row["attempt"]][row["drv"]] = row["name"]
    tested = dict(
        db.execute(
            """SELECT t.attempt,count(DISTINCT t.drv) FROM tests t
            JOIN attempts a ON a.id=t.attempt WHERE a.campaign=? GROUP BY t.attempt""",
            (campaign,),
        )
    )
    rows = []
    for row in db.execute(
        f"""SELECT id,kind,state,created,finished,targets,{OUTCOME} AS outcome,
        json_extract(result,'$.reason') AS reason FROM attempts
        WHERE campaign=? ORDER BY created,id""",
        (campaign,),
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
    return dict(campaign=campaign, now=now, cursor=cursor, rows=rows)
