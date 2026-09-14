"""Persistent facts. Only the controller (or offline CLI with its lock) writes."""

import contextlib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import time
import uuid

from .scope import REASON, kernel_metadata


def stamp():
    return time.time()


def encode(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def identity(value):
    return hashlib.sha256(encode(value).encode()).hexdigest()


def atomic_json(path, value):
    path = Path(path)
    tmp = path.with_suffix(".tmp")
    with tmp.open("w") as f:
        json.dump(value, f, sort_keys=True)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)
    fd = os.open(path.parent, os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


@contextlib.contextmanager
def writer_lock(state):
    Path(state).mkdir(parents=True, exist_ok=True)
    with (Path(state) / "writer.lock").open("a") as f:
        try:
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise ValueError(
                "controller owns the database; use the local command socket"
            ) from None
        yield


SCHEMA = """
CREATE TABLE IF NOT EXISTS campaigns (
 id TEXT PRIMARY KEY, name TEXT NOT NULL, created REAL NOT NULL,
 mode TEXT NOT NULL DEFAULT 'paused', manifest TEXT NOT NULL, source TEXT NOT NULL,
 revision TEXT NOT NULL, policy TEXT NOT NULL, nix_version TEXT NOT NULL,
 hold TEXT NOT NULL DEFAULT '', heartbeat REAL);
CREATE TABLE IF NOT EXISTS candidates (
 id INTEGER PRIMARY KEY, campaign TEXT NOT NULL REFERENCES campaigns(id),
 attr TEXT NOT NULL, label TEXT NOT NULL, selection TEXT NOT NULL,
 state TEXT NOT NULL DEFAULT 'unplanned', drv TEXT, recipe TEXT,
 error TEXT, UNIQUE(campaign,attr));
CREATE INDEX IF NOT EXISTS candidates_campaign ON candidates(campaign,state,label);
CREATE INDEX IF NOT EXISTS candidates_drv ON candidates(drv);
CREATE TABLE IF NOT EXISTS derivations (
 drv TEXT PRIMARY KEY, name TEXT NOT NULL, outputs TEXT NOT NULL,
 available INTEGER NOT NULL DEFAULT 0, origin TEXT NOT NULL DEFAULT 'unknown',
 failure TEXT, evidence_attempt TEXT, exclusion TEXT);
CREATE TABLE IF NOT EXISTS edges (
 parent TEXT NOT NULL, child TEXT NOT NULL, outputs TEXT NOT NULL,
 PRIMARY KEY(parent,child));
CREATE INDEX IF NOT EXISTS edges_child ON edges(child);
CREATE TABLE IF NOT EXISTS roles (
 campaign TEXT NOT NULL, parent TEXT NOT NULL, child TEXT NOT NULL,
 role TEXT NOT NULL, PRIMARY KEY(campaign,parent,child,role));
CREATE TABLE IF NOT EXISTS attempts (
 id TEXT PRIMARY KEY, campaign TEXT NOT NULL, kind TEXT NOT NULL,
 targets TEXT NOT NULL, state TEXT NOT NULL, created REAL NOT NULL,
 finished REAL, spec TEXT NOT NULL, offset INTEGER NOT NULL DEFAULT 0,
 result TEXT, cancel_requested INTEGER NOT NULL DEFAULT 0);
CREATE TABLE IF NOT EXISTS activities (
 attempt TEXT NOT NULL, activity TEXT NOT NULL, drv TEXT, kind TEXT,
 phase TEXT, checks TEXT NOT NULL DEFAULT '[]', stopped INTEGER DEFAULT 0,
 PRIMARY KEY(attempt,activity));
CREATE TABLE IF NOT EXISTS tests (
 attempt TEXT NOT NULL, drv TEXT NOT NULL, phase TEXT NOT NULL,
 evidence TEXT NOT NULL, PRIMARY KEY(attempt,drv,phase));
CREATE TABLE IF NOT EXISTS events (
 seq INTEGER PRIMARY KEY AUTOINCREMENT, time REAL NOT NULL,
 campaign TEXT, kind TEXT NOT NULL, payload TEXT NOT NULL);
PRAGMA user_version=2;
"""


def connect(state, readonly=False):
    path = Path(state) / "experiment.sqlite"
    if not readonly:
        path.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(
        f"file:{path}?mode=ro" if readonly else str(path), uri=readonly, timeout=10
    )
    db.row_factory = sqlite3.Row
    db.execute("PRAGMA foreign_keys=ON")
    if readonly:
        db.execute("PRAGMA query_only=ON")
    else:
        version = db.execute("PRAGMA user_version").fetchone()[0]
        if version not in (0, 1, 2):
            raise ValueError(f"unsupported database version {version}")
        db.execute("PRAGMA journal_mode=WAL")
        db.execute("PRAGMA synchronous=FULL")
        db.execute("PRAGMA wal_autocheckpoint=1000")
        if version == 1:
            db.executescript(
                "BEGIN IMMEDIATE; ALTER TABLE derivations ADD COLUMN exclusion TEXT; PRAGMA user_version=2; COMMIT;"
            )
        db.executescript(SCHEMA)
    return db


def event(db, campaign, kind, payload):
    db.execute(
        "INSERT INTO events(time,campaign,kind,payload) VALUES(?,?,?,?)",
        (stamp(), campaign, kind, encode(payload)),
    )


def import_campaign(
    db, name, manifest, source, revision, policy, nix_version, selections=()
):
    paths = manifest["attrPaths"]
    if len(paths) != len({encode(p) for p in paths}):
        raise ValueError("duplicate input attributes")
    if not paths or any(
        not isinstance(p, list)
        or not p
        or any(not isinstance(s, str) or not s for s in p)
        for p in paths
    ):
        raise ValueError("attrPaths must contain nonempty arrays of attribute names")
    cid = str(uuid.uuid4())
    selected = {encode(s["attrPath"]): s for s in selections}
    with db:
        db.execute(
            "INSERT INTO campaigns(id,name,created,manifest,source,revision,policy,nix_version) VALUES(?,?,?,?,?,?,?,?)",
            (
                cid,
                name,
                stamp(),
                encode(manifest),
                source,
                revision,
                encode(policy),
                nix_version,
            ),
        )
        db.executemany(
            "INSERT INTO candidates(campaign,attr,label,selection) VALUES(?,?,?,?)",
            [
                (cid, encode(p), ".".join(p), encode(selected.get(encode(p), {})))
                for p in paths
            ],
        )
        for selection in selections:
            if kernel_metadata(
                selection.get("metadata", {}), selection.get("sourceFile")
            ):
                db.execute(
                    "UPDATE candidates SET state='excluded',error=? WHERE campaign=? AND attr=?",
                    (REASON, cid, encode(selection["attrPath"])),
                )
        event(
            db,
            cid,
            "imported",
            {"count": len(paths), "manifestSha256": identity(manifest)},
        )
    return cid


def closure(db, drv):
    return [
        r[0]
        for r in db.execute(
            """WITH RECURSIVE deps(drv) AS (
      VALUES(?) UNION SELECT child FROM edges JOIN deps ON parent=deps.drv)
      SELECT drv FROM deps""",
            (drv,),
        )
    ]


def blockers(db, drv):
    # One shortest explaining chain per proven failing dependency; cycle-safe.
    queue = [(drv, [drv])]
    seen, found = set(), []
    for node, chain in queue:
        if node in seen:
            continue
        seen.add(node)
        row = db.execute(
            "SELECT coalesce(exclusion,failure) FROM derivations WHERE drv=?", (node,)
        ).fetchone()
        if row and row[0]:
            found.append({"drv": node, "failure": row[0], "chain": chain})
        queue.extend(
            (r[0], chain + [r[0]])
            for r in db.execute("SELECT child FROM edges WHERE parent=?", (node,))
            if r[0] not in seen
        )
    return found


def refresh_candidates(db, campaign):
    db.execute(
        """UPDATE candidates SET state=CASE
      WHEN EXISTS(SELECT 1 FROM derivations d WHERE d.drv=candidates.drv AND d.available=1) THEN 'available'
      WHEN EXISTS(SELECT 1 FROM derivations d WHERE d.drv=candidates.drv AND d.failure IS NOT NULL) THEN 'failed'
      ELSE 'queued' END WHERE campaign=? AND drv IS NOT NULL AND state NOT IN ('running','inconclusive','excluded')""",
        (campaign,),
    )
    db.execute(
        """WITH RECURSIVE bad(drv) AS (
      SELECT drv FROM derivations WHERE failure IS NOT NULL
      UNION SELECT parent FROM edges JOIN bad ON child=bad.drv)
      UPDATE candidates SET state='blocked' WHERE campaign=? AND state='queued' AND drv IN bad""",
        (campaign,),
    )

    # Preserve observed outputs and checks; exclusion changes eligibility, not
    # the historical realization facts. Direct kernels include cached successes.
    db.execute(
        """UPDATE candidates SET state='excluded',error=(
          SELECT exclusion FROM derivations WHERE drv=candidates.drv)
          WHERE campaign=? AND drv IN (SELECT drv FROM derivations WHERE exclusion IS NOT NULL)""",
        (campaign,),
    )
    db.execute(
        """WITH RECURSIVE outside(drv) AS (
          SELECT drv FROM derivations WHERE exclusion IS NOT NULL
          UNION SELECT parent FROM edges JOIN outside ON child=outside.drv)
          UPDATE candidates SET state='excluded',error=?
          WHERE campaign=? AND state='queued' AND drv IN outside""",
        (
            "Requires a Linux kernel build; outside the Fil-C userspace experiment",
            campaign,
        ),
    )
