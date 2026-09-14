"""Read-only WSGI application; bounded queries and no administrative endpoints."""

from contextlib import closing
import gzip
import json
from pathlib import Path
import sqlite3
from urllib.parse import parse_qs
from wsgiref.util import FileWrapper

from . import VERSION, nix
from .attempt import directory
from .model import blockers, connect, stamp
from .graph import live_graph
from .logs import build_log
from .history import history, attempt_detail
from .catalog import catalog, source_link


def snapshot(db, campaign=None, search="", state="", offset=0):
    campaigns = [
        dict(r)
        for r in db.execute(
            "SELECT id,name,created,mode,revision,heartbeat,hold FROM campaigns ORDER BY created"
        )
    ]
    if not campaigns:
        return dict(campaigns=[], candidates=[], counts={}, cursor=0)
    cid = campaign or campaigns[0]["id"]
    row = db.execute("SELECT * FROM campaigns WHERE id=?", (cid,)).fetchone()
    if not row:
        raise ValueError("unknown campaign")
    counts = dict(
        db.execute(
            "SELECT state,count(*) FROM candidates WHERE campaign=? GROUP BY state",
            (cid,),
        )
    )
    params = [cid]
    where = "campaign=?"
    if search:
        where += " AND instr(lower(label),lower(?))>0"
        params.append(search[:200])
    if state:
        where += " AND state=?"
        params.append(state)
    filtered = db.execute(
        f"SELECT count(*) FROM candidates WHERE {where}", params
    ).fetchone()[0]
    rows = [
        dict(r)
        for r in db.execute(
            f"SELECT id,label,state,drv,selection FROM candidates WHERE {where} ORDER BY label LIMIT 50 OFFSET ?",
            (*params, offset),
        )
    ]
    for r in rows:
        selection = json.loads(r.pop("selection"))
        r["tags"] = selection.get("tags", [])
        r["decision"] = selection.get("decision", "selected")
    attempts = [
        dict(r)
        for r in db.execute(
            "SELECT id,kind,state,created,finished,result,cancel_requested FROM attempts WHERE campaign=? ORDER BY state IN ('intended','running') DESC, created DESC LIMIT 12",
            (cid,),
        )
    ]
    active = [
        dict(r)
        for r in db.execute(
            """SELECT a.attempt,a.drv,a.phase FROM activities a
      JOIN attempts t ON t.id=a.attempt WHERE t.campaign=? AND t.state='running' AND a.stopped=0 LIMIT 30""",
            (cid,),
        )
    ]
    failures = [
        dict(r)
        for r in db.execute(
            """WITH RECURSIVE impacted(root,drv) AS (
      SELECT drv,drv FROM derivations WHERE failure IS NOT NULL
      UNION SELECT impacted.root,edges.parent FROM impacted JOIN edges ON edges.child=impacted.drv)
      SELECT d.drv,d.name,d.failure,count(DISTINCT c.id) AS affected FROM impacted i
      JOIN derivations d ON d.drv=i.root JOIN candidates c ON c.drv=i.drv
      WHERE c.campaign=? GROUP BY d.drv ORDER BY affected DESC LIMIT 10""",
            (cid,),
        )
    ]
    tests = db.execute(
        "SELECT count(DISTINCT t.drv) FROM tests t JOIN candidates c ON c.drv=t.drv WHERE c.campaign=? AND c.state!='excluded'",
        (cid,),
    ).fetchone()[0]
    return dict(
        campaigns=campaigns,
        campaign=dict(
            id=cid,
            name=row["name"],
            created=row["created"],
            mode=row["mode"],
            revision=row["revision"],
            heartbeat=row["heartbeat"],
            hold=row["hold"],
            source=row["source"],
            manifest={
                k: v for k, v in json.loads(row["manifest"]).items() if k != "attrPaths"
            },
            nix_version=row["nix_version"],
        ),
        counts=counts,
        candidates=rows,
        filtered=filtered,
        offset=offset,
        unique_derivations=db.execute(
            "SELECT count(DISTINCT drv) FROM candidates WHERE campaign=?", (cid,)
        ).fetchone()[0],
        attempts=attempts,
        active=active,
        blockers=failures,
        tested=tests,
        resources=nix.resources(json.loads(row["policy"])),
        now=stamp(),
        cursor=db.execute("SELECT coalesce(max(seq),0) FROM events").fetchone()[0],
        version=VERSION,
    )


def detail(db, candidate):
    row = db.execute("SELECT * FROM candidates WHERE id=?", (candidate,)).fetchone()
    if not row:
        raise ValueError("unknown candidate")
    result = dict(row)
    for key in ("attr", "selection", "recipe"):
        result[key] = json.loads(result[key]) if result[key] else None
    manifest = json.loads(
        db.execute(
            "SELECT manifest FROM campaigns WHERE id=?", (row["campaign"],)
        ).fetchone()[0]
    )
    result["source_url"] = source_link(manifest, result["selection"])
    drv = result["drv"]
    result["blockers"] = blockers(db, drv) if drv else []
    result["tests"] = [
        dict(r) for r in db.execute("SELECT * FROM tests WHERE drv=?", (drv,))
    ]
    d = db.execute("SELECT * FROM derivations WHERE drv=?", (drv,)).fetchone()
    result["realization"] = dict(d) if d else None
    result["dependencies"] = [
        dict(r)
        for r in db.execute(
            """SELECT e.child AS drv,d.name,
      group_concat(DISTINCT roles.role) AS roles FROM edges e LEFT JOIN derivations d ON d.drv=e.child
      LEFT JOIN roles ON roles.parent=e.parent AND roles.child=e.child AND roles.campaign=?
      WHERE e.parent=? GROUP BY e.child ORDER BY d.name LIMIT 100""",
            (row["campaign"], drv),
        )
    ]
    result["dependents"] = [
        dict(r)
        for r in db.execute(
            """WITH RECURSIVE up(drv) AS (
      SELECT parent FROM edges WHERE child=? UNION SELECT parent FROM edges JOIN up ON child=up.drv)
      SELECT id,label,state FROM candidates WHERE campaign=? AND drv IN up ORDER BY label LIMIT 100""",
            (drv, row["campaign"]),
        )
    ]
    # Positive host-role edges only; do not walk unknown/native edges for test claims.
    result["downstream_tests"] = [
        dict(r)
        for r in db.execute(
            """WITH RECURSIVE up(drv) AS (
      SELECT parent FROM roles WHERE child=? AND campaign=? AND role='host'
      UNION SELECT parent FROM roles JOIN up ON child=up.drv WHERE campaign=? AND role='host')
      SELECT DISTINCT c.id,c.label,t.phase,t.attempt FROM tests t JOIN candidates c ON c.drv=t.drv
      WHERE c.campaign=? AND c.drv IN up LIMIT 100""",
            (drv, row["campaign"], row["campaign"], row["campaign"]),
        )
    ]
    return result


def derivation_detail(db, drv, campaign, offset=0):
    row = db.execute("SELECT * FROM derivations WHERE drv=?", (drv,)).fetchone()
    if not row:
        raise ValueError("unknown derivation")
    dependencies = [
        dict(r)
        for r in db.execute(
            """SELECT child AS drv,d.name,group_concat(DISTINCT roles.role) AS roles
      FROM edges e JOIN derivations d ON d.drv=e.child LEFT JOIN roles ON roles.parent=e.parent
      AND roles.child=e.child AND roles.campaign=? WHERE e.parent=? GROUP BY e.child LIMIT 100""",
            (campaign, drv),
        )
    ]
    dependents = [
        dict(r)
        for r in db.execute(
            """WITH RECURSIVE up(drv) AS (
      VALUES(?) UNION SELECT parent FROM edges JOIN up ON child=up.drv)
      SELECT id,label,state FROM candidates WHERE campaign=? AND drv IN up ORDER BY label LIMIT 50 OFFSET ?""",
            (drv, campaign, offset),
        )
    ]
    return dict(
        derivation=dict(row),
        dependencies=dependencies,
        dependents=dependents,
        tests=[dict(r) for r in db.execute("SELECT * FROM tests WHERE drv=?", (drv,))],
        blockers=blockers(db, drv),
        offset=offset,
    )


def application(state):
    static = Path(__file__).with_name("static")

    def app(environ, start_response):
        status, mime = "200 OK", "application/json; charset=utf-8"
        try:
            if environ["REQUEST_METHOD"] not in ("GET", "HEAD"):
                status, payload = (
                    "405 Method Not Allowed",
                    {"error": "read-only dashboard"},
                )
            else:
                path = environ.get("PATH_INFO", "/")
                args = parse_qs(environ.get("QUERY_STRING", ""))

                def get(key, default=""):
                    return args.get(key, [default])[0]

                if path == "/":
                    with closing(connect(state, readonly=True)) as db:
                        initial = snapshot(db, get("campaign") or None)
                    # Embedded JSON escapes '<' to prevent closing its script element.
                    initial_json = json.dumps(initial).replace("<", "\\u003c")
                    payload = (
                        (static / "index.html")
                        .read_text()
                        .replace("__INITIAL__", initial_json)
                        .encode()
                    )
                    mime = "text/html; charset=utf-8"
                elif path in (
                    "/app.js",
                    "/packages.js",
                    "/packages.css",
                    "/graph.js",
                    "/logs.js",
                    "/logs.css",
                    "/history.js",
                    "/history.css",
                    "/style.css",
                    "/theme.css",
                ):
                    payload = (static / path[1:]).read_bytes()
                    mime = (
                        "text/javascript; charset=utf-8"
                        if path.endswith(".js")
                        else "text/css; charset=utf-8"
                    )
                elif path == "/api/snapshot":
                    with closing(connect(state, readonly=True)) as db:
                        payload = snapshot(
                            db,
                            get("campaign") or None,
                            get("q"),
                            get("state"),
                            max(0, min(int(get("offset", "0")), 1000000)),
                        )
                elif path == "/api/packages":
                    with closing(connect(state, readonly=True)) as db:
                        db.execute("BEGIN")
                        payload = catalog(db, get("campaign"))
                elif path == "/api/package":
                    with closing(connect(state, readonly=True)) as db:
                        payload = detail(db, int(get("id")))
                elif path == "/api/derivation":
                    with closing(connect(state, readonly=True)) as db:
                        payload = derivation_detail(
                            db,
                            get("drv"),
                            get("campaign"),
                            max(0, min(int(get("offset", "0")), 1000000)),
                        )
                elif path == "/api/graph":
                    with closing(connect(state, readonly=True)) as db:
                        db.execute("BEGIN")
                        payload = live_graph(
                            db,
                            state,
                            get("campaign"),
                            get("focus") or None,
                            get("available") == "1",
                            max(0, min(int(get("page", "0")), 1000000)),
                        )
                elif path == "/api/history":
                    with closing(connect(state, readonly=True)) as db:
                        db.execute("BEGIN")
                        payload = history(
                            db,
                            get("campaign"),
                            get("anchor"),
                            get("before"),
                            get("kind"),
                            get("outcome"),
                            get("q"),
                            max(0, min(int(get("window", "0")), 86400)),
                        )
                elif path == "/api/history/attempt":
                    with closing(connect(state, readonly=True)) as db:
                        db.execute("BEGIN")
                        payload = attempt_detail(db, get("campaign"), get("id"))
                elif path == "/api/events":
                    with closing(connect(state, readonly=True)) as db:
                        rows = [
                            dict(r)
                            for r in db.execute(
                                "SELECT * FROM events WHERE seq>? ORDER BY seq LIMIT 100",
                                (max(0, int(get("after", "0"))),),
                            )
                        ]
                        payload = {
                            "events": rows,
                            "cursor": rows[-1]["seq"]
                            if rows
                            else int(get("after", "0")),
                        }
                elif path == "/api/manifest":
                    with closing(connect(state, readonly=True)) as db:
                        row = db.execute(
                            "SELECT manifest FROM campaigns WHERE id=?",
                            (get("campaign"),),
                        ).fetchone()
                        if not row:
                            raise ValueError("unknown campaign")
                        payload = json.loads(row[0])
                elif path == "/api/log":
                    aid = get("attempt")
                    with closing(connect(state, readonly=True)) as db:
                        if not db.execute(
                            "SELECT 1 FROM attempts WHERE id=?", (aid,)
                        ).fetchone():
                            raise ValueError("unknown attempt")
                    offset = max(0, int(get("offset", "0")))
                    log = directory(state, aid) / "stderr.log"
                    data = b""
                    if log.exists():
                        with log.open("rb") as f:
                            f.seek(offset)
                            data = f.read(65536)
                    payload = {
                        "text": data.decode(errors="replace"),
                        "offset": offset + len(data),
                    }
                elif path == "/api/build-log":
                    with closing(connect(state, readonly=True)) as db:
                        db.execute("BEGIN")
                        payload = build_log(
                            db,
                            state,
                            get("attempt"),
                            get("direction", "tail"),
                            int(get("cursor", "0")),
                            get("drv"),
                        )
                elif path == "/api/log/download":
                    aid = get("attempt")
                    with closing(connect(state, readonly=True)) as db:
                        if not db.execute(
                            "SELECT 1 FROM attempts WHERE id=?", (aid,)
                        ).fetchone():
                            raise ValueError("unknown attempt")
                    log = directory(state, aid) / "stderr.log"
                    stream = log.open("rb")
                    start_response(
                        "200 OK",
                        [
                            ("Content-Type", "text/plain; charset=utf-8"),
                            (
                                "Content-Disposition",
                                f'attachment; filename="filnix-{aid}.log"',
                            ),
                            ("Cache-Control", "no-store"),
                            ("X-Content-Type-Options", "nosniff"),
                        ],
                    )
                    if environ["REQUEST_METHOD"] == "HEAD":
                        stream.close()
                        return []
                    return FileWrapper(stream, 65536)
                elif path == "/healthz":
                    with closing(connect(state, readonly=True)) as db:
                        heartbeat = db.execute(
                            "SELECT max(heartbeat) FROM campaigns"
                        ).fetchone()[0]
                    fresh = heartbeat is not None and stamp() - heartbeat < 30
                    status = "200 OK" if fresh else "503 Service Unavailable"
                    payload = {
                        "version": VERSION,
                        "controller_fresh": fresh,
                        "heartbeat": heartbeat,
                    }
                else:
                    status, payload = "404 Not Found", {"error": "not found"}
        except (ValueError, KeyError) as e:
            status, payload = "400 Bad Request", {"error": str(e)}
        except (OSError, sqlite3.Error):
            status, payload = (
                "503 Service Unavailable",
                {"error": "state temporarily unavailable"},
            )
        if not isinstance(payload, bytes):
            payload = json.dumps(payload).encode()
        encoding_headers = []
        if environ.get("PATH_INFO") == "/api/packages":
            encoding_headers.append(("Vary", "Accept-Encoding"))
            for encoding in environ.get("HTTP_ACCEPT_ENCODING", "").lower().split(","):
                parts = encoding.strip().split(";")
                quality = 1.0
                try:
                    for param in parts[1:]:
                        key, sep, value = param.strip().partition("=")
                        if key.strip() == "q" and sep:
                            quality = float(value)
                except ValueError:
                    quality = 0.0
                if parts[0] == "gzip" and 0 < quality <= 1:
                    payload = gzip.compress(payload, compresslevel=3)
                    encoding_headers.append(("Content-Encoding", "gzip"))
                    break
        start_response(
            status,
            [
                *encoding_headers,
                ("Content-Type", mime),
                ("Content-Length", str(len(payload))),
                ("Cache-Control", "no-store"),
                ("X-Content-Type-Options", "nosniff"),
                (
                    "Content-Security-Policy",
                    "default-src 'self'; script-src 'self'; style-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'none'",
                ),
            ],
        )
        return [] if environ["REQUEST_METHOD"] == "HEAD" else [payload]

    return app
