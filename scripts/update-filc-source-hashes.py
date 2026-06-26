#!/usr/bin/env python3
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


def run(args, **kwargs):
    return subprocess.run(args, check=True, text=True, **kwargs)


def output(args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs).strip()


def succeeds(args, **kwargs):
    return subprocess.run(args, **kwargs).returncode == 0


def repo_root(path):
    try:
        return Path(output(["git", "-C", str(path), "rev-parse", "--show-toplevel"]))
    except subprocess.CalledProcessError:
        raise SystemExit(f"error: not a git repository: {path}")


def load_json(path):
    with path.open() as f:
        return json.load(f)


def write_json(path, data):
    with path.open("w") as f:
        json.dump(data, f, indent=2)
        f.write("\n")


def copy_without_git(source, dest):
    def ignore(directory, names):
        if Path(directory) == source:
            return {".git"} & set(names)
        return set()

    shutil.copytree(source, dest, ignore=ignore, symlinks=True)


def main():
    parser = argparse.ArgumentParser(
        description="Update Fil-C sparse fetchgit hashes from one local clone."
    )
    parser.add_argument(
        "--repo",
        default=os.environ.get("FILC_REPO"),
        required=os.environ.get("FILC_REPO") is None,
        help="local pizlonator/fil-c clone to use; can also be set with FILC_REPO",
    )
    parser.add_argument(
        "--rev",
        help="also update lib/filc-upstream.json to this revision before hashing",
    )
    parser.add_argument(
        "--pull",
        action="store_true",
        help="run git pull --ff-only in the local clone before hashing",
    )
    args = parser.parse_args()

    root = Path(__file__).resolve().parents[1]
    upstream_path = root / "lib" / "filc-upstream.json"
    hashes_path = root / "lib" / "filc-hashes.json"

    upstream = load_json(upstream_path)
    if args.rev:
        upstream["filc-rev"] = args.rev
        write_json(upstream_path, upstream)

    rev = upstream["filc-rev"]
    sparse_checkouts = upstream["sparseCheckouts"]
    repo = repo_root(Path(args.repo).expanduser())

    if args.pull:
        run(["git", "-C", str(repo), "pull", "--ff-only"])

    if not succeeds(
        ["git", "-C", str(repo), "cat-file", "-e", f"{rev}^{{commit}}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ):
        run(["git", "-C", str(repo), "fetch", "--tags", "origin", rev])

    hashes = {}
    current_worktree = None

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        try:
            for name, paths in sorted(sparse_checkouts.items()):
                current_worktree = tmp_path / f"worktree-{name}"
                hash_dir = tmp_path / f"hash-{name}"

                run(
                    [
                        "git",
                        "-C",
                        str(repo),
                        "worktree",
                        "add",
                        "--quiet",
                        "--detach",
                        "--no-checkout",
                        str(current_worktree),
                        rev,
                    ]
                )
                run(["git", "-C", str(current_worktree), "sparse-checkout", "init", "--cone"])
                run(
                    [
                        "git",
                        "-C",
                        str(current_worktree),
                        "sparse-checkout",
                        "set",
                        *paths,
                    ]
                )
                run(["git", "-C", str(current_worktree), "checkout"], stdout=subprocess.DEVNULL)

                copy_without_git(current_worktree, hash_dir)
                source_hash = output(
                    ["nix", "hash", "path", "--type", "sha256", "--sri", str(hash_dir)]
                )
                hashes[name] = source_hash
                print(f"{name} {source_hash}")

                run(
                    [
                        "git",
                        "-C",
                        str(repo),
                        "worktree",
                        "remove",
                        "--force",
                        str(current_worktree),
                    ],
                    stdout=subprocess.DEVNULL,
                )
                current_worktree = None
                shutil.rmtree(hash_dir)
        finally:
            if current_worktree is not None and current_worktree.exists():
                run(
                    [
                        "git",
                        "-C",
                        str(repo),
                        "worktree",
                        "remove",
                        "--force",
                        str(current_worktree),
                    ],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )

    write_json(
        hashes_path,
        {
            "filc-rev": rev,
            "hashes": hashes,
        },
    )


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        print(f"error: command failed: {' '.join(error.cmd)}", file=sys.stderr)
        raise SystemExit(error.returncode)
