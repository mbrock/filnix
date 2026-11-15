#!/usr/bin/env python3
"""Check that image.pl keeps exact items and refuses selections a lookup could not trust."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SWIPL = os.environ.get("SWIPL", "swipl")
F = "func({n},export,w,[],[block(start,[],[],ret(w,const(0)))])"
IMAGE = [F.format(n="f"), "alias(g,weak,f)", "alias(h,export,g)", "data(d,rw(export),8,[])",
         F.format(n="unused"), "alias(bad,export,d)", "alias(lost,export,nowhere)",
         F.format(n="twice"), F.format(n="twice")]


def select(work, image, reference, *names):
    linked, ref, report = work / "image.term", work / "ref.term", work / "report.txt"
    linked.write_text(f"module([{','.join(image)}]).\n")
    if reference is not None:
        ref.write_text(f"module([{','.join(reference)}]).\n")
    result = subprocess.run([SWIPL, HERE / "image.pl", linked, ref if reference is not None else "-",
                             report, *names], capture_output=True, text=True)
    return result, report.read_text() if result.returncode == 0 else ""


def refused(work, message, *args):
    result, _ = select(work, *args)
    assert result.returncode != 0 and message in result.stderr, (args, result.stderr)


with tempfile.TemporaryDirectory() as tmp:
    work = Path(tmp)
    # An alias chain brings in its targets, in the image's order and with its terms.
    result, report = select(work, IMAGE, IMAGE, "h")
    assert result.returncode == 0, result.stderr
    assert result.stdout.replace(" ", "") == f"module([{F.format(n='f')},alias(g,weak,f),alias(h,export,g)]).\n"
    assert report.splitlines()[1].startswith("g: unique alias (weak) of f, sha256 ")
    assert all(line.endswith("equal to reference") for line in report.splitlines()), report
    result, report = select(work, IMAGE, None, "f")
    assert result.returncode == 0 and report.endswith("no reference\n"), report
    refused(work, "missing name in linked image: absent", IMAGE, None, "f", "absent")
    refused(work, "2 items name twice in linked image", IMAGE, None, "twice")
    refused(work, "missing name in linked image: nowhere", IMAGE, None, "lost")
    refused(work, "d is neither a function nor an alias", IMAGE, None, "bad")
    refused(work, "d is neither a function nor an alias", IMAGE, None, "d")
    # The reference must hold the same term, once, under each selected name.
    refused(work, "g differs from the reference image", IMAGE,
            [F.format(n="f"), "alias(g,export,f)", "alias(h,export,g)"], "h")
    refused(work, "f differs from the reference image", IMAGE, ["alias(g,weak,f)"], "g")
    refused(work, "f differs from the reference image", IMAGE, [F.format(n="f"), F.format(n="f")], "f")
print("image selection: alias closure, exact terms and eight refusals passed")
