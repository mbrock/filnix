#!/usr/bin/env python3
"""Check that image.pl keeps exact items and refuses selections a lookup could not trust."""
import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import time
import tomllib

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

# Hello's manifest reads the unit files that nix/hello-glibc.nix reads. A changed
# sibling must stop generation before any unit compiles.
generate = runpy.run_path(str(HERE / "generate.py"))
manifest = tomllib.loads((HERE.parents[1] / "glibc/hello/code.toml").read_text())
with tempfile.TemporaryDirectory() as tmp:
    root, capture = Path(tmp) / "nanofil", Path(tmp) / "capture"
    names = []
    for name in manifest["units_files"]:
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text((HERE.parents[2] / name).read_text())
        names += [u for u in path.read_text().split()]
    # The manifest's own startup units follow the listed ones.
    names += [u for _, u in generate["units"](manifest.get("units", ""))]
    for unit in names:
        (capture / (unit + ".i")).parent.mkdir(parents=True, exist_ok=True)
        (capture / (unit + ".i")).touch()
    unit_rows = generate["manifest_units"](manifest, root)
    assert [u for _, u in generate["units"](unit_rows)] == names and len(set(names)) == len(names)
    generate["check_units"](capture, "hello", unit_rows)
    siblings = root / manifest["units_files"][1]
    original = siblings.read_text()
    for old, new in (("stdlib/abs.os", "stdlib/absent.os"), ("stdlib/abs.os", names[0])):
        siblings.write_text(original.replace(old, new, 1))
        started = time.monotonic()
        try:
            generate["check_units"](capture, "hello", generate["manifest_units"](manifest, root))
            raise AssertionError(f"accepted a changed sibling: {new}")
        except ValueError as error:
            assert new in str(error) and time.monotonic() - started < 1, error

# The whole image decodes in groups of slices, in slice order, and a group
# counts the block files that a slice imports.
with tempfile.TemporaryDirectory() as tmp:
    out = Path(tmp)
    def slice_file(n, size, uses=""):
        imports = f"From Glibc Require Import {uses}.\n" if uses else ""
        (out / f"HelloImageCode{n}.v").write_text(imports + "x" * size + "\n")
    slice_file("01", 400_000)
    slice_file("03", 300_000)
    slice_file("02", 1_000, "HelloImageCode03")
    slice_file("04", 600_000)
    (out / "HelloImageTerm.v").write_text("Definition hello_image_term : term :=\n"
        "  TApp \"module\" [TList (hello_image_items_01 ++ hello_image_items_02 ++ hello_image_items_04)].\n")
    generate["image_decoders"](out, 321, "main", "(** provenance *)\n")
    assert sorted(p.name for p in out.glob("HelloImageDec*.v")) == ["HelloImageDec01.v", "HelloImageDec02.v"]
    assert "Import HelloImageCode01 HelloImageCode02." in (out / "HelloImageDec01.v").read_text()
    assert "hello_image_items_01 ++ hello_image_items_02." in (out / "HelloImageDec01.v").read_text()
    assert "Import HelloImageCode04." in (out / "HelloImageDec02.v").read_text()
    joined = (out / "HelloImageCode.v").read_text()
    assert "hello_image_md_01 ++ hello_image_md_02." in joined and "(** provenance *)" in joined
    assert "exact hello_image_dec_02." in joined
    # A join that names a slice with no file stops generation.
    (out / "HelloImageCode04.v").unlink()
    try:
        generate["image_decoders"](out, 321, "main", "")
        raise AssertionError("accepted a join that names a missing slice")
    except FileNotFoundError:
        pass
print("image selection: alias closure, exact terms, eight refusals and two unit-list refusals, ordered decode groups and a missing slice passed")
