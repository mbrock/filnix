#!/usr/bin/env python3
"""Regenerate scratch sources without invalidating unchanged compiled files."""
import pathlib
import shutil
import subprocess
import sys
import tempfile

here = pathlib.Path(__file__).resolve().parent
repo = here.parents[4]
dest = pathlib.Path(sys.argv[1]).resolve()
dest.mkdir(parents=True, exist_ok=True)
subprocess.run([sys.executable, str(here / 'convert.py'), str(repo / 'nanofil/rocq/theories'), str(dest / 'theories')], check=True)
with tempfile.TemporaryDirectory() as temp:
    tree = pathlib.Path(temp) / 'glibc'
    shutil.copytree(repo / 'nanofil/rocq/glibc', tree)
    subprocess.run([sys.executable, str(here / '10-flatten.py'), str(tree)], check=True)
    subprocess.run([sys.executable, str(here.parent / 'stages/15-code.py'), str(tree)], check=True)
    shutil.copytree(here.parent / 'overlay', tree, dirs_exist_ok=True)
    for source in tree.rglob('*'):
        if not source.is_file():
            continue
        target = dest / 'glibc' / source.relative_to(tree)
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or source.read_bytes() != target.read_bytes():
            shutil.copyfile(source, target)
