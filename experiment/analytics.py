"""Crash-safe, read-only SQLite and captured-log publisher for private S3.

The publisher records observations, not a claim of complete CDC.  Each generation
lists immutable Parquet objects explicitly; consumers should use :func:`latest_sql`.
"""

import argparse
import base64
import contextlib
import hashlib
import json
import os
from pathlib import Path
import shutil
import sqlite3
import time
import uuid

import pyarrow as pa
import pyarrow.parquet as pq

from .logs import decode as decode_log

TABLES = (
    "campaigns",
    "candidates",
    "derivations",
    "edges",
    "roles",
    "attempts",
    "activities",
    "tests",
    "events",
    "build_times",
    "replans",
    "classifications",
)
BATCH = 4096
FRAGMENT = 1024 * 1024
PART_BYTES = 8 * 1024**2
LOG_SCHEMA = pa.schema(
    [
        ("attempt", pa.string()),
        ("campaign", pa.string()),
        ("stream", pa.string()),
        ("start", pa.int64()),
        ("end", pa.int64()),
        ("raw", pa.binary()),
        ("text", pa.string()),
        ("activity", pa.string()),
        ("derivation", pa.string()),
        ("kind", pa.string()),
        ("fragment", pa.bool_()),
        ("_revision", pa.int64()),
        ("_observed_at", pa.float64()),
    ]
)


def _json(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def _pack(value):
    if isinstance(value, bytes):
        return {"$bytes": value.hex()}
    return value


def _unpack(value):
    if isinstance(value, dict) and set(value) == {"$bytes"}:
        return bytes.fromhex(value["$bytes"])
    return value


def _key(values):
    return _json([_pack(x) for x in values])


def _file_hash(path):
    with open(path, "rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def _sync(path):
    fd = os.open(path, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _schema(db, table):
    info = db.execute(f'PRAGMA table_info("{table}")').fetchall()
    keys = [r[1] for r in sorted((r for r in info if r[5]), key=lambda r: r[5])]
    if not keys:
        raise ValueError(f"table {table} has no primary key")
    return info, keys


def _arrow_type(declared):
    d = declared.upper()
    if "INT" in d:
        return pa.int64()
    if any(x in d for x in ("REAL", "FLOA", "DOUB")):
        return pa.float64()
    if "BLOB" in d:
        return pa.binary()
    return pa.string()


def _arrow_schema(info, metadata=True):
    # Tombstones preserve primary-key values and null the non-key source columns.
    fields = [pa.field(row[1], _arrow_type(row[2]), nullable=True) for row in info]
    if metadata:
        fields += [
            pa.field("_revision", pa.int64(), nullable=False),
            pa.field("_observed_at", pa.float64(), nullable=False),
            pa.field("_source_key", pa.string(), nullable=False),
            pa.field("_deleted", pa.bool_(), nullable=False),
        ]
    return pa.schema(fields)


class LocalBackend:
    """Filesystem backend useful for tests; keys are relative to its root."""

    def __init__(self, root):
        self.root = Path(root)
        self.root.mkdir(parents=True, exist_ok=True)
        self.identity = str(self.root.resolve())

    def get(self, key):
        p = self.root / key
        if not p.exists():
            return None, None
        data = p.read_bytes()
        return data, hashlib.md5(data).hexdigest()

    def put_immutable(self, key, path):
        dest = self.root / key
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.exists():
            if _file_hash(dest) != _file_hash(path):
                raise ValueError(f"immutable object collision: {key}")
        else:
            tmp = dest.with_name(dest.name + ".tmp")
            shutil.copyfile(path, tmp)
            os.replace(tmp, dest)

    def publish(self, key, data, expected_etag):
        old, etag = self.get(key)
        if etag != expected_etag:
            raise RuntimeError(
                "remote latest pointer changed; refusing concurrent writer"
            )
        p = self.root / key
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_name(p.name + ".tmp")
        tmp.write_bytes(data)
        os.replace(tmp, p)
        return hashlib.md5(data).hexdigest()


class S3Backend:
    def __init__(self, bucket, region=None):
        import boto3

        self.bucket = bucket
        self.identity = f"s3://{bucket}"
        self.client = boto3.client("s3", region_name=region)

    def get(self, key):
        try:
            r = self.client.get_object(Bucket=self.bucket, Key=key)
            return r["Body"].read(), r["ETag"].strip('"')
        except self.client.exceptions.NoSuchKey:
            return None, None
        except Exception as e:
            if getattr(e, "response", {}).get("Error", {}).get("Code") in (
                "404",
                "NoSuchKey",
            ):
                return None, None
            raise

    def put_immutable(self, key, path):
        digest = _file_hash(path)
        try:
            with open(path, "rb") as f:
                self.client.put_object(
                    Bucket=self.bucket,
                    Key=key,
                    Body=f,
                    IfNoneMatch="*",
                    Metadata={"sha256": digest},
                    ChecksumSHA256=base64.b64encode(bytes.fromhex(digest)).decode(),
                )
        except Exception as e:
            if getattr(e, "response", {}).get("Error", {}).get("Code") not in (
                "412",
                "PreconditionFailed",
            ):
                raise
            head = self.client.head_object(Bucket=self.bucket, Key=key)
            if (
                head.get("Metadata", {}).get("sha256") != digest
                or head["ContentLength"] != Path(path).stat().st_size
            ):
                raise ValueError(f"immutable object collision: {key}") from e

    def publish(self, key, data, expected_etag):
        args = {"Bucket": self.bucket, "Key": key, "Body": data}
        if expected_etag is None:
            args["IfNoneMatch"] = "*"
        else:
            args["IfMatch"] = expected_etag
        try:
            r = self.client.put_object(**args)
        except Exception as e:
            if getattr(e, "response", {}).get("Error", {}).get("Code") not in (
                "412",
                "PreconditionFailed",
                "ConditionalRequestConflict",
                "409",
            ):
                raise
            raise RuntimeError(
                "remote latest pointer changed; refusing concurrent writer"
            ) from e
        return r.get("ETag", "").strip('"')


class Publisher:
    def __init__(
        self,
        experiment,
        state,
        backend,
        prefix="",
        log_bytes=256 * 1024**2,
        reserve_bytes=0,
    ):
        self.experiment = Path(experiment)
        self.state = Path(state)
        self.backend = backend
        self.prefix = prefix.strip("/")
        self.log_bytes = log_bytes
        self.reserve_bytes = reserve_bytes
        self.state.mkdir(parents=True, exist_ok=True)
        self.spool = self.state / "spool"
        self.spool.mkdir(exist_ok=True)
        self.db = sqlite3.connect(self.state / "analytics.sqlite", timeout=30)
        self.db.execute("PRAGMA journal_mode=WAL")
        self.db.executescript("""CREATE TABLE IF NOT EXISTS index_rows(table_name TEXT,key TEXT,hash TEXT,PRIMARY KEY(table_name,key));
          CREATE TABLE IF NOT EXISTS log_cursor(attempt TEXT,stream TEXT,offset INTEGER NOT NULL,PRIMARY KEY(attempt,stream));
          CREATE TABLE IF NOT EXISTS config(k TEXT PRIMARY KEY,v TEXT);
          CREATE TABLE IF NOT EXISTS changes(table_name TEXT,key TEXT,hash TEXT,deleted INTEGER,PRIMARY KEY(table_name,key));
          CREATE TABLE IF NOT EXISTS pending(id TEXT,revision INTEGER,manifest TEXT,base_etag TEXT);""")
        self.latest_key = self._path("latest.json")
        remote, self.etag = backend.get(self.latest_key)
        remote_generation = json.loads(remote).get("generation") if remote else None
        identity = _json(
            [str(self.experiment.resolve()), backend.identity, self.prefix]
        )
        prior = self.db.execute("SELECT v FROM config WHERE k='identity'").fetchone()
        if prior and prior[0] != identity:
            raise ValueError(
                "analytics checkpoint belongs to a different source/destination/prefix"
            )
        if not prior:
            self.db.execute("INSERT INTO config VALUES('identity',?)", (identity,))
            self.db.commit()
        committed = self.db.execute(
            "SELECT v FROM config WHERE k='generation'"
        ).fetchone()
        pending_row = self.db.execute("SELECT id FROM pending").fetchone()
        if committed and not remote:
            raise ValueError(
                "remote latest pointer is missing; refusing incomplete dataset"
            )
        if (
            remote
            and committed
            and committed[0] != remote_generation
            and (not pending_row or pending_row[0] != remote_generation)
        ):
            raise ValueError(
                "remote latest pointer has an unexpected parent; refusing to continue"
            )
        if (
            remote
            and not self.db.execute("SELECT 1 FROM pending").fetchone()
            and not self.db.execute(
                "SELECT 1 FROM config WHERE k='remote_seen'"
            ).fetchone()
        ):
            raise ValueError(
                "remote dataset exists but local checkpoint is missing; refusing overwrite"
            )
        pending = self.db.execute(
            "SELECT id,revision,manifest,base_etag FROM pending"
        ).fetchone()
        if pending:
            self.pending = pending
        else:
            self.pending = None

    def _path(self, key):
        return "/".join(x for x in (self.prefix, key) if x)

    @contextlib.contextmanager
    def lock(self):
        import fcntl

        with (self.state / "publisher.lock").open("a") as f:
            try:
                fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise RuntimeError("another analytics publisher is active")
            yield

    def _snapshot(self):
        src = sqlite3.connect(
            f"file:{self.experiment / 'experiment.sqlite'}?mode=ro",
            uri=True,
            timeout=30,
        )
        src.row_factory = sqlite3.Row
        src.execute("PRAGMA query_only=ON")
        src.execute("BEGIN")
        return src

    def _write(self, table, info, records, revision, deleted=False):
        if not records:
            return None
        path = self.spool / f"{table}-{uuid.uuid4().hex}.parquet"
        schema = _arrow_schema(info)
        rows = [tuple(r) + (revision, self.observed_at, k, deleted) for k, r in records]
        arrays = [
            pa.array([r[i] for r in rows], type=schema.field(i).type)
            for i in range(len(schema))
        ]
        pq.write_table(
            pa.Table.from_arrays(arrays, schema=schema),
            path,
            compression="zstd",
            row_group_size=BATCH,
        )
        return self._part(path, table, len(rows))

    def _part(self, path, table, count, partition=""):
        if shutil.disk_usage(self.state).free < self.reserve_bytes:
            raise OSError(
                "analytics staging reached its disk reserve; publication deferred"
            )
        _sync(path)
        digest = _file_hash(path)
        os.replace(path, self.spool / f"{digest}.parquet")
        key = self._path(f"objects/table={table}/{partition}{digest}.parquet")
        return {
            "key": key,
            "sha256": digest,
            "rows": count,
            "table": table,
        }

    def _scan_table(self, src, name, rev, output):
        info, keys = _schema(src, name)
        cols = [r[1] for r in info]
        keyidx = [cols.index(k) for k in keys]
        # Events are append-only: resume from seq, never rescan historical payloads.
        if name == "events":
            last = (
                int(
                    self.db.execute(
                        "SELECT v FROM config WHERE k='events_seq'"
                    ).fetchone()[0]
                )
                if self.db.execute(
                    "SELECT 1 FROM config WHERE k='events_seq'"
                ).fetchone()
                else 0
            )
            query = f'SELECT * FROM "{name}" WHERE seq>? ORDER BY seq'
            if (
                src.execute("SELECT coalesce(max(seq),0) FROM events").fetchone()[0]
                < last
            ):
                raise ValueError(
                    "source event cursor rewound; use a new dataset/checkpoint"
                )
            cur = src.execute(query, (last,))
        else:
            cur = src.execute(f'SELECT * FROM "{name}"')
        self.db.execute("CREATE TEMP TABLE IF NOT EXISTS scan_keys(k TEXT PRIMARY KEY)")
        self.db.execute("DELETE FROM scan_keys")
        batch = []
        batch_bytes = 0
        maxseq = 0
        for row in cur:
            vals = tuple(row)
            k = _key([vals[i] for i in keyidx])
            encoded = _json([_pack(x) for x in vals]).encode()
            h = hashlib.sha256(encoded).hexdigest()
            size = len(encoded)
            if name != "events":
                self.db.execute("INSERT OR IGNORE INTO scan_keys VALUES(?)", (k,))
            old = self.db.execute(
                "SELECT hash FROM index_rows WHERE table_name=? AND key=?",
                (name, k),
            ).fetchone()
            if old is None or old[0] != h:
                if batch and (len(batch) >= BATCH or batch_bytes + size > PART_BYTES):
                    output.append(self._write(name, info, batch, rev))
                    batch, batch_bytes = [], 0
                batch.append((k, vals))
                batch_bytes += size
                self.db.execute(
                    "INSERT OR REPLACE INTO changes VALUES(?,?,?,0)", (name, k, h)
                )
            if name == "events":
                maxseq = max(maxseq, vals[keyidx[0]])
        part = self._write(name, info, batch, rev)
        if part:
            output.append(part)
        batch = []
        if name != "events":
            for (k,) in self.db.execute(
                "SELECT key FROM index_rows WHERE table_name=? AND key NOT IN (SELECT k FROM scan_keys)",
                (name,),
            ):
                self.db.execute(
                    "INSERT OR REPLACE INTO changes VALUES(?,?,NULL,1)", (name, k)
                )
                values = [_unpack(v) for v in json.loads(k)]
                tombstone = [None] * len(info)
                for col, value in zip(keys, values):
                    tombstone[cols.index(col)] = value
                batch.append((k, tuple(tombstone)))
                if len(batch) >= BATCH:
                    part = self._write(name, info, batch, rev, deleted=True)
                    if part:
                        output.append(part)
                    batch = []
            part = self._write(name, info, batch, rev, deleted=True)
            if part:
                output.append(part)
        elif maxseq:
            self.db.execute(
                "INSERT OR REPLACE INTO config VALUES('events_seq',?)", (str(maxseq),)
            )

    def _logs(self, src, rev, output):
        processed = 0
        rows = src.execute("SELECT id,campaign,state,offset FROM attempts ORDER BY id")
        for aid, campaign, status, indexed in rows:
            activities = {
                str(activity): drv
                for activity, drv in src.execute(
                    "SELECT activity,drv FROM activities WHERE attempt=?", (aid,)
                )
            }
            for stream in ("stdout", "stderr"):
                path = self.experiment / "attempts" / aid / f"{stream}.log"
                if not path.exists():
                    continue
                startrow = self.db.execute(
                    "SELECT offset FROM log_cursor WHERE attempt=? AND stream=?",
                    (aid, stream),
                ).fetchone()
                pos = startrow[0] if startrow else 0
                size = path.stat().st_size
                if size < pos:
                    raise ValueError(f"captured log shrank: {aid}/{stream}")
                live = status in ("running", "intended")
                limit = (
                    min(path.stat().st_size, indexed)
                    if stream == "stderr" and live
                    else path.stat().st_size
                )
                records = []
                batch_bytes = 0
                committed_line_end = 0
                with path.open("rb") as f:
                    while pos < limit and processed < self.log_bytes:
                        f.seek(max(0, pos - 1))
                        continuation = pos > 0 and f.read(1) != b"\n"
                        take = min(FRAGMENT, limit - pos, self.log_bytes - processed)
                        f.seek(pos)
                        raw = f.readline(take)
                        if not raw:
                            break
                        complete = raw.endswith(b"\n")
                        # An oversized/budget-split live line is safe only if its
                        # newline exists inside the captured, committed prefix.
                        if (
                            live
                            and not complete
                            and pos + len(raw) > committed_line_end
                        ):
                            found = False
                            scan = pos + len(raw)
                            while scan < limit:
                                probe = f.readline(min(FRAGMENT, limit - scan))
                                if not probe:
                                    break
                                scan += len(probe)
                                if probe.endswith(b"\n"):
                                    found = True
                                    break
                            if not found:
                                break
                            committed_line_end = scan
                        end = pos + len(raw)
                        fragment = continuation or not complete
                        parsed = (
                            decode_log(raw, pos, activities) if not fragment else None
                        )
                        activity = None
                        if not fragment and raw.startswith(b"@nix "):
                            try:
                                event = json.loads(raw[5:])
                                if (
                                    isinstance(event, dict)
                                    and event.get("id") is not None
                                ):
                                    activity = str(event["id"])
                            except ValueError:
                                pass
                        if records and (
                            len(records) >= BATCH or batch_bytes + len(raw) > PART_BYTES
                        ):
                            self._logpart(records, output)
                            records, batch_bytes = [], 0
                        records.append(
                            dict(
                                attempt=aid,
                                campaign=campaign,
                                stream=stream,
                                start=pos,
                                end=end,
                                raw=raw,
                                text=parsed["text"]
                                if parsed
                                else raw.decode("utf-8", errors="replace"),
                                activity=activity,
                                derivation=(parsed["drv"] if parsed else None),
                                kind=parsed["kind"] if parsed else None,
                                fragment=fragment,
                                _revision=rev,
                                _observed_at=self.observed_at,
                            )
                        )
                        pos = end
                        processed += len(raw)
                        batch_bytes += len(raw)
                    if records:
                        self._logpart(records, output)
                self.db.execute(
                    "INSERT OR REPLACE INTO log_cursor VALUES(?,?,?)",
                    (aid, stream, pos),
                )
                if processed >= self.log_bytes:
                    return processed
        return processed

    def _logpart(self, rows, output):
        path = self.spool / f"logs-{uuid.uuid4().hex}.parquet"
        pq.write_table(
            pa.Table.from_pylist(rows, schema=LOG_SCHEMA),
            path,
            compression="zstd",
            row_group_size=BATCH,
        )
        output.append(
            self._part(
                path,
                "logs",
                len(rows),
                f"attempt={rows[0]['attempt']}/stream={rows[0]['stream']}/",
            )
        )

    def _finalize(self):
        pid, rev, manifest, base = self.pending
        self.db.execute("BEGIN IMMEDIATE")
        for t, k, h, d in self.db.execute(
            "SELECT table_name,key,hash,deleted FROM changes"
        ):
            if d:
                self.db.execute(
                    "DELETE FROM index_rows WHERE table_name=? AND key=?", (t, k)
                )
            else:
                self.db.execute(
                    "INSERT OR REPLACE INTO index_rows VALUES(?,?,?)", (t, k, h)
                )
        self.db.execute("DELETE FROM changes")
        self.db.execute("DELETE FROM pending")
        self.db.execute("INSERT OR REPLACE INTO config VALUES('remote_seen','1')")
        self.db.execute("INSERT OR REPLACE INTO config VALUES('generation',?)", (pid,))
        self.db.commit()
        self.pending = None
        for p in self.spool.glob("*"):
            p.unlink()

    def publish(self):
        with self.lock():
            if self.pending:
                pid, rev, encoded, base = self.pending
                manifest = json.loads(encoded)
                remote, etag = self.backend.get(self.latest_key)
                # Remote pointer may already be this generation after a crash.
                if remote and json.loads(remote).get("generation") == pid:
                    self.etag = etag
                    self._finalize()
                    return manifest
                if etag != base:
                    raise RuntimeError(
                        "remote latest pointer changed; refusing concurrent writer"
                    )
            else:
                # A failed scan before the pending record was committed left only
                # unreferenced temporary spools; these are safe to discard.
                for stale in self.spool.glob("*.parquet"):
                    stale.unlink()
                src = self._snapshot()
                rev = (
                    int(
                        self.db.execute(
                            "SELECT v FROM config WHERE k='revision'"
                        ).fetchone()[0]
                    )
                    if self.db.execute(
                        "SELECT 1 FROM config WHERE k='revision'"
                    ).fetchone()
                    else 0
                ) + 1
                pid = uuid.uuid4().hex
                parts = []
                try:
                    self.observed_at = time.time()
                    source_version = src.execute("PRAGMA user_version").fetchone()[0]
                    if source_version != 6:
                        raise ValueError(
                            f"unsupported source database version: {source_version}"
                        )
                    watermark = src.execute(
                        "SELECT coalesce(max(seq),0) FROM events"
                    ).fetchone()[0]
                    tables = {}
                    for table in TABLES:
                        info, keys = _schema(src, table)
                        tables[table] = {
                            "primary_key": keys,
                            "columns": [{"name": r[1], "type": r[2]} for r in info],
                        }
                    self.db.execute("BEGIN IMMEDIATE")
                    for table in TABLES:
                        self._scan_table(src, table, rev, parts)
                    log_bytes = self._logs(src, rev, parts)
                    src.commit()
                    # A no-op still publishes monotonic revision only if any table/log activity.
                    changed = bool(parts)
                    if not changed:
                        self.db.rollback()
                        return {"generation": None, "revision": rev - 1, "files": []}
                    remote, base = self.backend.get(self.latest_key)
                    if base != self.etag:
                        raise RuntimeError(
                            "remote latest pointer changed; refusing concurrent writer"
                        )
                    if (
                        remote
                        and not self.db.execute(
                            "SELECT 1 FROM config WHERE k='remote_seen'"
                        ).fetchone()
                    ):
                        raise ValueError(
                            "remote dataset exists but local checkpoint is missing; refusing overwrite"
                        )
                    manifest = {
                        "format": "filnix-analytics-v1",
                        "generation": pid,
                        "revision": rev,
                        "observed_at": self.observed_at,
                        "source_version": source_version,
                        "events_seq": watermark,
                        "tables": tables,
                        "log_bytes": log_bytes,
                        "parent": json.loads(remote).get("generation")
                        if remote
                        else None,
                        "files": parts,
                    }
                    _sync(self.spool)
                    self.db.execute(
                        "INSERT OR REPLACE INTO config VALUES('revision',?)",
                        (str(rev),),
                    )
                    self.db.execute(
                        "INSERT INTO pending VALUES(?,?,?,?)",
                        (pid, rev, _json(manifest), base),
                    )
                    self.db.commit()
                    self.pending = (pid, rev, _json(manifest), base)
                except BaseException:
                    self.db.rollback()
                    src.rollback()
                    raise
                finally:
                    src.close()
            # Pending Parquet objects are content-addressed and safe to retry.
            for item in manifest["files"]:
                local = self.spool / f"{item['sha256']}.parquet"
                if not local.exists():
                    raise RuntimeError(
                        "pending object spool is missing; refusing incomplete publication"
                    )
                if _file_hash(local) != item["sha256"]:
                    raise ValueError(
                        "pending object checksum mismatch; refusing publication"
                    )
                self.backend.put_immutable(item["key"], local)
            self.backend.put_immutable(
                self._path(f"manifests/{pid}.json"),
                _write_bytes(self.spool / f"{pid}.json", _json(manifest).encode()),
            )
            self.etag = self.backend.publish(
                self.latest_key,
                _json(
                    {
                        "generation": pid,
                        "manifest": self._path(f"manifests/{pid}.json"),
                        "revision": rev,
                    }
                ).encode(),
                base,
            )
            self._finalize()
            return manifest

    def close(self):
        self.db.close()


def _write_bytes(path, data):
    Path(path).write_bytes(data)
    return path


def load_chain(backend, prefix=""):
    """Pin one latest pointer and follow only its committed manifest chain."""
    prefix = prefix.strip("/")
    key = f"{prefix}/latest.json" if prefix else "latest.json"
    pointer, _ = backend.get(key)
    if pointer is None:
        raise ValueError("dataset has not been published yet")
    generation = json.loads(pointer)["generation"]
    manifests, seen = [], set()
    while generation:
        if generation in seen:
            raise ValueError("manifest parent cycle")
        seen.add(generation)
        key = f"manifests/{generation}.json"
        data, _ = backend.get(f"{prefix}/{key}" if prefix else key)
        if data is None:
            raise ValueError(f"committed manifest is missing: {generation}")
        manifest = json.loads(data)
        if (
            manifest["format"] != "filnix-analytics-v1"
            or manifest["generation"] != generation
        ):
            raise ValueError("unsupported or inconsistent manifest")
        manifests.append(manifest)
        generation = manifest["parent"]
    return list(reversed(manifests))


def latest_sql(manifests, resolve=lambda key: key):
    """Build DuckDB SQL from an oldest-to-newest manifest chain.

    Every generation manifest lists only its delta files; callers follow ``parent``
    back to the initial manifest and pass that ordered chain here. Never prefix-glob.

    ``resolve`` can map S3 object keys to DuckDB-readable URLs or local paths.
    Per-table views preserve native field types. ``temporal_<table>`` retains all
    observations; ``<table>`` selects the latest non-deleted observation of each
    primary key. ``build_logs`` contains byte-exact, append-only log fragments.
    """
    if isinstance(manifests, dict):
        manifests = [manifests]
    files = {t: [] for t in (*TABLES, "logs")}
    for manifest in manifests:
        for item in manifest["files"]:
            path = str(resolve(item["key"])).replace("'", "''")
            files[item["table"]].append(f"'{path}'")
    sql = []
    casts = {
        pa.int64(): "BIGINT",
        pa.float64(): "DOUBLE",
        pa.binary(): "BLOB",
        pa.bool_(): "BOOLEAN",
        pa.string(): "VARCHAR",
    }
    for table in TABLES:
        if files[table]:
            # v1 has a fixed, explicit schema per table. Avoid reading every
            # remote footer merely to bind views before executing the query.
            source = (
                f"read_parquet([{','.join(files[table])}], hive_partitioning=false)"
            )
            sql.append(
                f"CREATE OR REPLACE VIEW temporal_{table} AS SELECT * FROM {source};"
            )
        else:
            columns = manifests[-1]["tables"][table]["columns"]
            fields = [
                f'NULL::{casts[_arrow_type(c["type"])]} AS "{c["name"]}"'
                for c in columns
            ]
            fields += [
                "NULL::BIGINT AS _revision",
                "NULL::DOUBLE AS _observed_at",
                "NULL::VARCHAR AS _source_key",
                "NULL::BOOLEAN AS _deleted",
            ]
            sql.append(
                f"CREATE OR REPLACE VIEW temporal_{table} AS SELECT {','.join(fields)} WHERE false;"
            )
        sql.append(f"""CREATE OR REPLACE VIEW {table} AS
SELECT * EXCLUDE (_rn, _deleted) FROM (
 SELECT *, row_number() OVER (PARTITION BY _source_key ORDER BY _revision DESC) _rn
 FROM temporal_{table}) WHERE _rn=1 AND NOT _deleted;""")
    if files["logs"]:
        sql.append(
            f"CREATE OR REPLACE VIEW build_logs AS SELECT * FROM read_parquet([{','.join(files['logs'])}], hive_partitioning=true);"
        )
    else:
        fields = [f'NULL::{casts[f.type]} AS "{f.name}"' for f in LOG_SCHEMA]
        sql.append(
            f"CREATE OR REPLACE VIEW build_logs AS SELECT {','.join(fields)} WHERE false;"
        )
    return "\n".join(sql)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--config", required=True)
    p.add_argument(
        "--query",
        help="read committed S3 generations with DuckDB instead of publishing",
    )
    p.add_argument(
        "--log-bytes",
        type=int,
        help="override the captured-log byte budget for this run (for bulk backfill)",
    )
    a = p.parse_args(argv)
    if a.log_bytes is not None and a.log_bytes < 0:
        p.error("--log-bytes must be non-negative")
    config = json.loads(Path(a.config).read_text())
    backend = S3Backend(config["bucket"], config.get("region"))
    if a.query:
        import duckdb

        chain = load_chain(backend, config.get("prefix", ""))
        with duckdb.connect() as con:
            con.execute("SET memory_limit='1GB'; SET threads=2; LOAD httpfs; LOAD aws;")
            profile = os.environ.get("AWS_PROFILE", "default").replace("'", "''")
            region = config.get("region", "eu-central-1").replace("'", "''")
            con.execute(
                f"CREATE SECRET (TYPE s3, PROVIDER credential_chain, CHAIN 'process;config;sso;env', PROFILE '{profile}', REGION '{region}');"
            )
            con.execute(latest_sql(chain, lambda key: f"s3://{config['bucket']}/{key}"))
            result = con.execute(a.query)
            names = [r[0] for r in result.description]
            while rows := result.fetchmany(100):
                for row in rows:
                    print(json.dumps(dict(zip(names, row)), default=str))
        return
    pub = Publisher(
        config["experiment"],
        config["state"],
        backend,
        config.get("prefix", ""),
        a.log_bytes
        if a.log_bytes is not None
        else config.get("log_bytes", 256 * 1024**2),
        config.get("reserve_bytes", 20 * 1024**3),
    )
    try:
        manifest = pub.publish()
        print(
            _json(
                {
                    k: manifest.get(k)
                    for k in (
                        "generation",
                        "revision",
                        "observed_at",
                        "events_seq",
                        "log_bytes",
                    )
                }
                | {"objects": len(manifest["files"])}
            )
        )
    finally:
        pub.close()


if __name__ == "__main__":
    main()
