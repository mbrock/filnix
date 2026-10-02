"""Mirror committed analytics objects to an unlisted anonymous-read prefix.

This is deliberate publication, not authentication or redaction. The private
configuration must never be included in Git or the canonical campaign export.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
from itertools import batched
import json
from pathlib import Path
import re
import tempfile

from .analytics import S3Backend, _json, latest_sql, load_chain


def publish_share(backend, source_prefix, share_prefix, base_url):
    if not re.fullmatch(r"share/[a-z2-7]{16}/v1", share_prefix):
        raise ValueError("share prefix must contain a 16-character base32 code")
    source_prefix = source_prefix.strip("/")
    if not source_prefix or source_prefix.startswith("share/"):
        raise ValueError("share source must be a separate private prefix")
    manifests = load_chain(backend, source_prefix)
    current = manifests[-1]
    index_key = f"{share_prefix}/index.json"
    data, etag = backend.get(index_key)
    previous = json.loads(data) if data else None
    if previous and previous["source_prefix"] != source_prefix:
        raise ValueError("share belongs to a different source")
    if previous and previous["generation"] == current["generation"]:
        return {"copied": 0, "unchanged": True}
    known = {}
    if previous:
        data, _ = backend.get(previous["manifest"])
        if data is None:
            raise ValueError("previous share inventory is missing")
        known = {item["key"]: item["sha256"] for item in json.loads(data)["files"]}
    files, copies = {}, []
    for manifest in manifests:
        for item in manifest["files"]:
            source = item["key"]
            if not source.startswith(f"{source_prefix}/objects/"):
                raise ValueError("manifest object is outside the private dataset")
            dest = share_prefix + source[len(source_prefix) :]
            shared = {**item, "key": dest}
            if dest in files and files[dest] != shared:
                raise ValueError("conflicting file inventory")
            if dest in files:
                continue
            files[dest] = shared
            if dest in known:
                if known[dest] != item["sha256"]:
                    raise ValueError("share inventory checksum collision")
            else:
                copies.append((source, dest, item["sha256"]))
    # Copies stay within S3; no Parquet download, staging or recompression.
    # Bound both workers and outstanding tasks. A failed run leaves the old
    # pointer intact; partial immutable copies are verified and reused on retry.
    with ThreadPoolExecutor(max_workers=8) as pool:
        for batch in batched(copies, 64):
            for _ in pool.map(lambda args: backend.copy_immutable(*args), batch):
                pass
    inventory = {**current, "parent": None, "files": list(files.values())}
    generation = current["generation"]
    manifest_key = f"{share_prefix}/manifests/{generation}.json"
    sql_key = f"{share_prefix}/views/{generation}.sql"
    sql = latest_sql(inventory, lambda key: f"{base_url.rstrip('/')}/{key}")
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "manifest.json"
        path.write_text(_json(inventory))
        backend.put_immutable(manifest_key, path)
        path = Path(tmp) / "views.sql"
        path.write_text(sql)
        backend.put_immutable(sql_key, path)
    backend.publish(
        index_key,
        _json(
            {
                "format": "filnix-analytics-share-v1",
                "generation": generation,
                "revision": current["revision"],
                "source_prefix": source_prefix,
                "manifest": manifest_key,
                "sql": sql_key,
                "objects": len(files),
                "archived_log_bytes": sum(m["log_bytes"] for m in manifests),
            }
        ).encode(),
        etag,
    )
    return {"copied": len(copies), "objects": len(files), "unchanged": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True)
    args = parser.parse_args()
    config = json.loads(Path(args.config).read_text())
    backend = S3Backend(config["bucket"], config["region"])
    base_url = f"https://{config['bucket']}.s3.{config['region']}.amazonaws.com"
    with open(Path(config["state"]) / "share.lock", "a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        result = publish_share(
            backend,
            config["source_prefix"],
            config["share_prefix"],
            base_url,
        )
    # Do not put the locator code or share URL into service logs.
    print(_json(result))


if __name__ == "__main__":
    main()
