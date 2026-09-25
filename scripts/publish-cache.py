#!/usr/bin/env python3
"""Publish observed campaign outputs without joining the build/controller loop."""

import argparse
import contextlib
import fcntl
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import time

STORE_PATH = re.compile(r"/nix/store/[0-9a-z]{32}-[^/\s]+\Z")


def discover(database, campaign):
    # A failed batch can contain successful dependencies. Only positive output
    # evidence qualifies; merely entering a build/check phase does not.
    with contextlib.closing(sqlite3.connect(
        f"file:{database}?mode=ro", uri=True, timeout=10
    )) as db:
        if not db.execute("SELECT 1 FROM campaigns WHERE id=?", (campaign,)).fetchone():
            raise ValueError(f"unknown campaign: {campaign}")
        rows = db.execute("""
            SELECT d.outputs FROM derivations d WHERE d.available=1 AND (
                EXISTS (SELECT 1 FROM candidates c
                        WHERE c.drv=d.drv AND c.campaign=?) OR
                EXISTS (SELECT 1 FROM activities a JOIN attempts t ON t.id=a.attempt
                        WHERE a.drv=d.drv AND t.campaign=?))
            """, (campaign, campaign))
        paths = {p for (outputs,) in rows for p in json.loads(outputs).values() if p}
    if any(not STORE_PATH.fullmatch(p) or p.endswith(".drv") for p in paths):
        raise ValueError("invalid output path in campaign observations")
    return sorted(paths)


def connect(path):
    db = sqlite3.connect(path, timeout=10)
    db.row_factory = sqlite3.Row
    db.executescript("""
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous=FULL;
        CREATE TABLE IF NOT EXISTS destination (identity TEXT NOT NULL);
        CREATE TABLE IF NOT EXISTS outputs (
            path TEXT PRIMARY KEY, discovered REAL NOT NULL,
            published REAL, attempts INTEGER NOT NULL DEFAULT 0,
            retry_after REAL NOT NULL DEFAULT 0, error TEXT);
    """)
    return db


def enqueue(db, paths, now):
    with db:
        db.executemany("INSERT OR IGNORE INTO outputs(path,discovered) VALUES(?,?)",
                       [(p, now) for p in paths])


def record(db, paths, error, now):
    with db:
        for path in paths:
            if error is None:
                db.execute("""UPDATE outputs SET published=?,attempts=attempts+1,
                              error=NULL,retry_after=0 WHERE path=?""", (now, path))
            else:
                attempts = db.execute("SELECT attempts FROM outputs WHERE path=?",
                                      (path,)).fetchone()[0]
                delay = min(3600, 60 * 2 ** min(attempts, 6))
                db.execute("""UPDATE outputs SET attempts=attempts+1,error=?,
                              retry_after=? WHERE path=?""", (error, now + delay, path))


def report(db):
    result = dict(db.execute("""SELECT count(*) AS discovered,
        count(published) AS published,
        count(*)-count(published) AS pending,
        coalesce(sum(CASE WHEN error IS NOT NULL THEN 1 ELSE 0 END),0) AS retrying
        FROM outputs""").fetchone())
    result["errors"] = [dict(r) for r in db.execute("""SELECT path,attempts,error,retry_after
        FROM outputs WHERE error IS NOT NULL ORDER BY retry_after LIMIT 5""")]
    return result


def command(config, target):
    if target == "local":
        # Nix copies the complete reference closure and signs each narinfo.
        destination = Path(config["directory"]).as_uri()
        destination += ("?compression=zstd&compression-level=3"
                        "&parallel-compression=true&secret-key=" + config["secret_key"])
        return ["nix", "copy", "--stdin", "--to", destination]
    return ["cachix", "--config", str(Path(os.environ["CREDENTIALS_DIRECTORY"]) / "cachix.dhall"),
            "push", "--jobs", "4", "--num-concurrent-chunks", "2", config["cache"]]


def publish(db, config, target, count, run=subprocess.run):
    now = time.time()
    rows = db.execute("""SELECT path,attempts FROM outputs
        WHERE published IS NULL AND retry_after<=?
        ORDER BY attempts,discovered,path LIMIT ?""", (now, count)).fetchall()
    # Retry failed batches one root at a time so a missing path cannot keep
    # otherwise publishable neighbors permanently behind it.
    paths = [r["path"] for r in (rows[:1] if rows and rows[0]["attempts"] else rows)]
    if not paths:
        return False
    try:
        if target == "local":
            directory = Path(config["directory"])
            directory.mkdir(parents=True, exist_ok=True)
            if shutil.disk_usage(directory).free < config.get("min_free_bytes", 100 * 1024**3):
                raise RuntimeError("local cache paused: less than reserved free disk space")
        # A timeout/termination never records success. Copies are idempotent,
        # including when killed after upload but before committing the receipt.
        run(command(config, target), input="\n".join(paths) + "\n", text=True,
            check=True, timeout=config.get("timeout", 1800))
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        record(db, paths, str(exc), time.time())
        print(json.dumps({"target": target, "failed_roots": len(paths), "error": str(exc)}), flush=True)
    else:
        record(db, paths, None, time.time())
        print(json.dumps({"target": target, "published_roots": len(paths)}), flush=True)
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target", choices=["local", "cachix"])
    parser.add_argument("--config", default="/etc/filnix-cache/config.json")
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--batch-size", type=int, default=64)
    parser.add_argument("--batches", type=int, default=8)
    # Campaign outputs never reference the compiler at run time, so their
    # closures omit it. The deployed application names the toolchain here.
    parser.add_argument("--extra-root", action="append", default=[],
                        help="store path to publish in addition to campaign outputs")
    args = parser.parse_args()
    if args.batch_size < 1 or args.batches < 1:
        parser.error("batch sizes must be positive")
    for root in args.extra_root:
        if not STORE_PATH.fullmatch(root) or root.endswith(".drv"):
            parser.error(f"invalid extra root: {root}")
    config = json.loads(Path(args.config).read_text())
    state = Path(config["state"])
    if args.status:
        with contextlib.closing(sqlite3.connect(
            f"file:{state / (args.target + '.sqlite')}?mode=ro", uri=True
        )) as db:
            db.row_factory = sqlite3.Row
            print(json.dumps({"target": args.target, **report(db)}), flush=True)
        return
    state.mkdir(parents=True, exist_ok=True)
    with (state / f"{args.target}.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        with contextlib.closing(connect(state / f"{args.target}.sqlite")) as db:
            identity = json.dumps(config[args.target], sort_keys=True)
            previous = db.execute("SELECT identity FROM destination").fetchone()
            if previous and previous[0] != identity:
                raise ValueError("cache destination changed; use a fresh publisher state directory")
            if not previous:
                with db:
                    db.execute("INSERT INTO destination VALUES(?)", (identity,))
            paths = discover(Path(config["experiment"]) / "experiment.sqlite", config["campaign"])
            enqueue(db, sorted(set(paths) | set(args.extra_root)), time.time())
            for _ in range(args.batches):
                if not publish(db, config[args.target], args.target, args.batch_size):
                    break
            print(json.dumps({"target": args.target, **report(db)}), flush=True)


if __name__ == "__main__":
    main()
