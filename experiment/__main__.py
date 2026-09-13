"""Local administration; mutations use the controller socket or an exclusive lock."""

import argparse
import io
import json
import os
from pathlib import Path
import socket
import subprocess
import tarfile
import tempfile

from . import nix
from .controller import Controller
from .model import atomic_json, connect, import_campaign, writer_lock


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--state", default=os.environ.get("FILNIX_STATE", "/var/lib/filnix-experiment")
    )
    sub = p.add_subparsers(dest="command", required=True)
    imp = sub.add_parser(
        "import",
        help="snapshot a committed source revision and import a paused campaign",
    )
    imp.add_argument("manifest")
    imp.add_argument("--name", required=True)
    imp.add_argument("--repo", default=".")
    imp.add_argument("--revision", default="HEAD")
    imp.add_argument("--inventory")
    sub.add_parser("controller")
    web = sub.add_parser("web")
    web.add_argument("--port", type=int, default=8777)
    sub.add_parser("status")
    backup = sub.add_parser("backup")
    backup.add_argument("destination")
    for op in ("plan", "run", "pause", "retry", "build-once", "retry-derivation"):
        cmd = sub.add_parser(op)
        cmd.add_argument("campaign")
        if op in ("plan", "retry", "build-once"):
            cmd.add_argument("ids", type=int, nargs="+")
        if op == "retry-derivation":
            cmd.add_argument("drv")
    cancel = sub.add_parser("cancel")
    cancel.add_argument("attempt")
    args = p.parse_args()
    state = Path(args.state).resolve()
    if args.command == "web":
        from waitress import serve
        from .web import application

        serve(
            application(state),
            host="127.0.0.1",
            port=args.port,
            threads=4,
            expose_tracebacks=False,
            max_request_body_size=0,
        )
        return
    if args.command == "status":
        with connect(state, readonly=True) as db:
            print(
                json.dumps(
                    [
                        dict(r)
                        for r in db.execute(
                            "SELECT id,name,mode,hold,heartbeat FROM campaigns"
                        )
                    ],
                    indent=2,
                )
            )
        return
    if args.command == "backup":
        import sqlite3

        with (
            connect(state, readonly=True) as src,
            sqlite3.connect(args.destination) as dest,
        ):
            src.backup(dest)
        return
    if args.command in (
        "plan",
        "run",
        "pause",
        "retry",
        "cancel",
        "build-once",
        "retry-derivation",
    ):
        request = {k: v for k, v in vars(args).items() if k not in ("state", "command")}
        request["op"] = args.command
        try:
            with socket.socket(socket.AF_UNIX) as s:
                s.settimeout(60)
                s.connect(str(state / "control.sock"))
                s.sendall((json.dumps(request) + "\n").encode())
                response = json.loads(s.makefile().readline(65536))
        except (FileNotFoundError, ConnectionRefusedError):
            with writer_lock(state), connect(state) as db:
                response = {"ok": Controller(db, state).dispatch(request)}
        if "error" in response:
            p.error(response["error"])
        print(response["ok"])
        return
    with writer_lock(state), connect(state) as db:
        if args.command == "controller":
            Controller(db, state).serve()
        elif args.command == "import":
            manifest = json.loads(Path(args.manifest).read_text())
            rev = subprocess.check_output(
                [
                    "git",
                    "-C",
                    args.repo,
                    "rev-parse",
                    "--verify",
                    args.revision + "^{commit}",
                ],
                text=True,
            ).strip()
            archive = subprocess.check_output(["git", "-C", args.repo, "archive", rev])
            with tempfile.TemporaryDirectory(prefix="filnix-source-") as tmp:
                with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
                    tar.extractall(tmp, filter="data")
                source = subprocess.check_output(
                    nix.command(
                        "store", "add-path", "--name", "filnix-campaign-source", tmp
                    ),
                    text=True,
                ).strip()
            selections = []
            if args.inventory:
                selections = [
                    json.loads(line)
                    for line in Path(args.inventory).read_text().splitlines()
                ]
            version = subprocess.check_output([nix.NIX, "--version"], text=True).strip()
            cid = import_campaign(
                db,
                args.name,
                manifest,
                source,
                rev,
                nix.DEFAULT_POLICY,
                version,
                selections,
            )
            Controller(db, state).root(source)
            atomic_json(state / (cid + ".manifest.json"), manifest)
            print(cid)


if __name__ == "__main__":
    main()
