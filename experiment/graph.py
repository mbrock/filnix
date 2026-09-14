"""A bounded, live neighborhood of the recorded build graph.

This is an observation layer, not another scheduler. A stopped Nix activity does
not imply success, and edges describe required outputs rather than every output
the dependency can produce. No Nix subprocesses or database writes happen here.
"""

from collections import Counter
import json

from .attempt import directory
from .model import stamp


SCOPE = """WITH RECURSIVE scope(drv) AS (
  SELECT drv FROM candidates WHERE campaign=? AND drv IS NOT NULL
  UNION SELECT child FROM edges JOIN scope ON parent=scope.drv)
"""


def attempt_file(state, aid, name):
    path = directory(state, aid) / name
    try:
        with path.open("rb") as f:
            data = f.read(8 * 1024**2 + 1)
        if len(data) > 8 * 1024**2:
            return None
        return json.loads(data)
    except (OSError, ValueError):
        return None


def live_graph(db, state, campaign, focus=None, show_available=False, page=0):
    c = db.execute(
        "SELECT mode,heartbeat FROM campaigns WHERE id=?", (campaign,)
    ).fetchone()
    if not c:
        raise ValueError("unknown campaign")
    active_rows = db.execute(
        "SELECT * FROM attempts WHERE campaign=? AND state IN ('intended','running') ORDER BY kind='build' DESC,created DESC",
        (campaign,),
    ).fetchall()
    active = active_rows[0] if active_rows else None
    planner = next((r for r in active_rows if r["kind"] == "plan"), None)
    batch = db.execute(
        "SELECT * FROM attempts WHERE campaign=? AND kind='build' ORDER BY created DESC LIMIT 1",
        (campaign,),
    ).fetchone()
    builds = [r for r in active_rows if r["kind"] == "build"]
    batches = builds or ([batch] if batch else [])
    if builds:
        batch = builds[0]
    targets = list(dict.fromkeys(d for r in batches for d in json.loads(r["targets"])))
    in_flight = bool(builds)
    observations = [attempt_file(state, r["id"], "before.json") for r in builds]
    before = next((v for v in observations if v is not None), None)
    existing = set(p for v in observations for p in (v or []))
    activities = {}
    provided, requested = set(), set()
    for current in builds:
        activities.update(
            {
                r["drv"]: dict(r)
                for r in db.execute(
                    "SELECT * FROM activities WHERE attempt=? ORDER BY rowid",
                    (current["id"],),
                )
            }
        )
        # A consumer's build phase establishes availability of its required
        # input outputs, without claiming local builds or successful checks.
        for r in db.execute(
            """SELECT e.outputs AS required,d.outputs FROM edges e
          JOIN activities a ON a.drv=e.parent JOIN derivations d ON d.drv=e.child
          WHERE a.attempt=? AND a.phase IS NOT NULL""",
            (current["id"],),
        ):
            required = json.loads(r["required"])
            if isinstance(required, dict):
                required = required.get("outputs", [])
            outputs = json.loads(r["outputs"])
            provided.update(outputs[k] for k in required if outputs.get(k))
        requested.update(json.loads(current["spec"]).get("derivations", []))
    # Restrict blockers and reverse edges to this campaign, including its native tools.
    scope = {r[0] for r in db.execute(SCOPE + "SELECT drv FROM scope", (campaign,))}
    bad = {
        r[0]
        for r in db.execute("""WITH RECURSIVE bad(drv) AS (
      SELECT drv FROM derivations WHERE failure IS NOT NULL OR exclusion IS NOT NULL
      UNION SELECT parent FROM edges JOIN bad ON child=bad.drv) SELECT drv FROM bad""")
    }
    cache = {}
    labels_by_drv = {}
    for r in db.execute(
        "SELECT id,label,drv FROM candidates WHERE campaign=? AND drv IS NOT NULL ORDER BY label",
        (campaign,),
    ):
        labels_by_drv.setdefault(r["drv"], []).append(
            dict(id=r["id"], label=r["label"])
        )

    def node(drv, required=None):
        if drv not in cache:
            row = db.execute("SELECT * FROM derivations WHERE drv=?", (drv,)).fetchone()
            cache[drv] = (
                dict(row)
                if row
                else dict(
                    drv=drv,
                    name=drv.rsplit("/", 1)[-1][33:-4],
                    outputs="{}",
                    available=0,
                    failure=None,
                    origin="unknown",
                )
            )
        record = cache[drv]
        outputs = json.loads(record["outputs"])
        wanted = required if required is not None else list(outputs)
        paths = [outputs.get(k) for k in wanted]
        present = bool(paths) and None not in paths and set(paths) <= existing
        consumed = (
            bool(paths) and None not in paths and set(paths) <= existing | provided
        )
        activity = activities.get(drv) if in_flight else None
        if activity and not activity["stopped"]:
            status = "building"
        elif record.get("exclusion"):
            status = "excluded"
        elif consumed:
            status = "available"
        elif activity:
            status = "settling"
        elif record["available"] or present:
            status = "available"
        elif record["failure"]:
            status = "failed"
        elif drv in bad:
            status = "blocked"
        elif drv in requested:
            status = "waiting"
        else:
            status = "unknown"
        labels = labels_by_drv.get(drv, [])[:8]
        return dict(
            drv=drv,
            name=record["name"],
            state=status,
            phase=activity["phase"] if activity else None,
            failure=record.get("exclusion") or record["failure"],
            origin="pre-existing" if present else record["origin"],
            availability_evidence="consumer-phase"
            if consumed and not present and not record["available"]
            else "store-observation"
            if status == "available"
            else None,
            labels=labels,
            required_outputs=wanted,
            attempt=activity["attempt"] if activity else record.get("evidence_attempt"),
        )

    roots = [node(d) for d in targets]
    building = [
        node(d)
        for d, a in activities.items()
        if in_flight and not a["stopped"] and d in scope
    ]
    if focus is None:
        focus = next((n["drv"] for n in building), None)
        focus = focus or next(
            (n["drv"] for n in roots if n["state"] in ("failed", "blocked")), None
        )
        focus = focus or next(
            (n["drv"] for n in roots if n["state"] != "available"), None
        )
        focus = focus or (targets[0] if targets else next(iter(sorted(scope)), None))
    elif focus not in scope:
        raise ValueError("derivation is outside this campaign's evaluated graph")

    work = dict(
        kind=active["kind"] if active else "idle",
        attempt=active["id"] if active else None,
        started=active["created"] if active else None,
    )
    planning = None
    if planner:
        total = len(json.loads(planner["targets"]))
        completed = 0
        try:
            with (directory(state, planner["id"]) / "plan.jsonl").open("rb") as f:
                completed = f.read(8 * 1024**2).count(b"\n")
        except OSError:
            pass
        planning = dict(
            attempt=planner["id"], completed=min(completed, total), total=total
        )
        if active["kind"] == "plan":
            work.update(completed=planning["completed"], total=total)
    if in_flight:
        work["stage"] = (
            "building" if building else "preflight" if before is None else "resolving"
        )
    result = dict(
        campaign=campaign,
        mode=c["mode"],
        heartbeat=c["heartbeat"],
        now=stamp(),
        work=work,
        planning=planning,
        batch=dict(id=batch["id"], state=batch["state"], created=batch["created"])
        if batch
        else None,
        batches=[
            dict(id=r["id"], state=r["state"], created=r["created"]) for r in batches
        ],
        roots=roots,
        building=building[:30],
        focus=None,
        inputs=[],
        consumers=[],
        totals={},
        selected_dependents=0,
        affected_roots=[],
        edges=[],
        page=page,
    )
    if focus is None:
        return result
    result["focus"] = node(focus)
    # Hubs can have thousands of consumers. Fetch their records in one indexed
    # query rather than issuing two SQL queries for every displayed/hidden node.
    for r in db.execute(
        """SELECT * FROM derivations WHERE drv IN (
      SELECT child FROM edges WHERE parent=? UNION SELECT parent FROM edges WHERE child=?)""",
        (focus, focus),
    ):
        cache[r["drv"]] = dict(r)
    input_roles = {}
    for r in db.execute(
        "SELECT child,role FROM roles WHERE campaign=? AND parent=? ORDER BY role",
        (campaign, focus),
    ):
        input_roles.setdefault(r["child"], []).append(r["role"])
    inputs, consumers = [], []
    for e in db.execute(
        "SELECT child,outputs FROM edges WHERE parent=? ORDER BY child", (focus,)
    ):
        required = json.loads(e["outputs"])
        if isinstance(required, dict):
            required = required.get("outputs", [])
        n = node(e["child"], required)
        n["roles"] = input_roles.get(e["child"], [])
        inputs.append(n)
    for e in db.execute(
        "SELECT parent FROM edges WHERE child=? ORDER BY parent", (focus,)
    ):
        if e[0] in scope:
            consumers.append(node(e[0]))
    priority = {
        "building": 0,
        "excluded": 1,
        "failed": 1,
        "blocked": 2,
        "settling": 3,
        "waiting": 4,
        "unknown": 5,
        "available": 6,
    }

    def order(n):
        return (priority[n["state"]], n["name"], n["drv"])

    inputs.sort(key=order)
    consumers.sort(key=order)
    hidden = 0 if show_available else sum(n["state"] == "available" for n in inputs)
    visible = (
        inputs if show_available else [n for n in inputs if n["state"] != "available"]
    )
    page = max(0, min(page, max(0, (max(len(visible), len(consumers)) - 1) // 6)))
    result["page"] = page
    result["inputs"] = visible[page * 6 : page * 6 + 6]
    result["consumers"] = consumers[page * 6 : page * 6 + 6]
    result["totals"] = dict(
        inputs=len(inputs),
        consumers=len(consumers),
        hidden_available=hidden,
        input_states=dict(Counter(n["state"] for n in inputs)),
        more=(page + 1) * 6 < max(len(visible), len(consumers)),
    )
    result["edges"] = [
        dict(source=n["drv"], target=focus) for n in result["inputs"]
    ] + [dict(source=focus, target=n["drv"]) for n in result["consumers"]]
    up = {
        r[0]
        for r in db.execute(
            """WITH RECURSIVE up(drv) AS (
      VALUES(?) UNION SELECT parent FROM edges JOIN up ON child=up.drv) SELECT drv FROM up""",
            (focus,),
        )
    }
    result["affected_roots"] = [
        n for n in roots if n["drv"] in up and n["drv"] != focus
    ]
    result["selected_dependents"] = sum(
        1
        for r in db.execute(
            "SELECT drv FROM candidates WHERE campaign=? AND drv IS NOT NULL",
            (campaign,),
        )
        if r[0] in up and r[0] != focus
    )
    return result
