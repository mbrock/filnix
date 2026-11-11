#!/usr/bin/env python3
"""Regenerate/check checked-IR fixtures for the user-glibc proof campaign.

Build /tmp/filcc and /tmp/swipl as in nanofil/AGENTS.md, then run:
  python3 nanofil/rocq/glibc/fixtures/gen_fixtures.py [--update]

--pp selects capture.nix's output; --hello selects nanofil-hello-fixture.captured.
Absent these, Nix builds them. --work-dir retains IR, checked terms, linked
modules and logs for nanofil-model --module and inspection; otherwise they
live in a temporary directory. Inputs are never rewritten: .filc_* assembly
and each capture command's cc_options are part of the fixture contract.

The manifest retains all 305 census units, atexit.oS and all 15 named
shared-libc siblings (321 unique paths; the campaign prompt said 320).
Compile/parse the large locale tables with a 64 MiB stack: ulimit -s 65536.
Run parse.sh's swipl with --stack_limit=8g (the default 1 GiB is too small).
"""

import argparse
import concurrent.futures
import filecmp
import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time


HERE = Path(__file__).resolve().parent
NF = HERE.parents[2]
REPO = NF.parent
NANOFIL = NF / "bin/nanofil"
CHECKER = "rocq/glibc/fixtures/gen_fixtures.py"
LEAVES = """
string/strlen.os string/strnlen.os string/strchr.os string/strchrnul.os
string/strrchr.os string/strcmp.os string/strncmp.os string/memchr.os
string/memcmp.os string/memcpy.os string/mempcpy.os string/memset.os
string/strdup.os malloc/malloc.os csu/errno.os csu/errno-loc.os
ctype/ctype-info.os locale/C-ctype.os locale/global-locale.os
locale/mb_cur_max.os wcsmbs/mbsinit.os wctype/wcfuncs.os
""".split()

spec = importlib.util.spec_from_file_location("glibc_survey", NF / "survey/glibc/run.py")
survey = importlib.util.module_from_spec(spec)
spec.loader.exec_module(survey)


def run(command, env, out=None, inp=None):
    """Keep stderr beside every product, including failed compiles."""
    with (open(out, "wb") if out else open(os.devnull, "wb")) as stdout, \
            (open(str(out) + ".log", "w+b") if out else tempfile.TemporaryFile()) as stderr, \
            (open(inp, "rb") if inp else open(os.devnull, "rb")) as stdin:
        try:
            subprocess.run(list(map(str, command)), cwd=NF / "src", env=env,
                           stdin=stdin, stdout=stdout, stderr=stderr,
                           timeout=300, check=True)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired):
            stderr.seek(0)
            raise RuntimeError(f"failed: {' '.join(map(str, command))}\n"
                               + stderr.read().decode(errors="replace")) from None


def nix_output(args):
    return Path(subprocess.check_output(
        ["nix", "build", "--no-link", "--print-out-paths", *args], cwd=REPO,
        stdin=subprocess.DEVNULL, text=True).strip())


def generate(args, work):
    pp = args.pp or nix_output(["-f", "nanofil/survey/glibc/capture.nix"])
    hello = args.hello or nix_output([".#checks.x86_64-linux.nanofil-hello-fixture.captured"])
    env = dict(os.environ)
    env.setdefault("SWIPL", shutil.which("swipl") or "/tmp/swipl/bin/swipl")
    env.setdefault("FILCC", "/tmp/filcc/bin/clang")
    # A capture's flags, not the caller's ambient C dialect, govern each unit.
    for key in ("NANOFIL_STD", "NANOFIL_COMMON", "NANOFIL_MATH_ERRNO"):
        env.pop(key, None)
    if not env.get("NANOFIL_STATE"):
        state = work / "nanofil.state"
        run([NANOFIL, "--save-state", state], env)
        env["NANOFIL_STATE"] = str(state)

    units = (HERE / "units_hello.txt").read_text().splitlines()
    if not units or units != sorted(set(units)) or any(not u for u in units):
        raise ValueError("units_hello.txt must be sorted, unique and nonempty")

    def checked(source, dest, ccenv=None, ccopts=()):
        dest.parent.mkdir(parents=True, exist_ok=True)
        unit_env = env | (ccenv or {})
        ir = dest.with_suffix(dest.suffix + ".ir")
        run([NANOFIL, "-O", *ccopts, "cc-ir", source], unit_env, ir)
        run([NANOFIL, "--script", NF / "bench/trap-checked.pl", ir], unit_env, dest)
        return dest

    def compile_unit(unit):
        ccenv, ccopts = survey.cc_options((pp / (unit + ".cmd")).read_text())
        return checked(pp / (unit + ".i"), work / "glibc" / (unit + ".term"),
                       ccenv, ccopts)

    print(f"glibc-fixtures: {len(units)} units, {args.jobs} at a time", flush=True)
    start = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        futures = [pool.submit(compile_unit, unit) for unit in units]
        for n, future in enumerate(concurrent.futures.as_completed(futures), 1):
            future.result()
            if n % 25 == 0 or n == len(units):
                print(f"glibc-fixtures: {n}/{len(units)} in {time.monotonic() - start:.1f}s",
                      flush=True)

    def glibc_spec(unit):
        return f"glibc_{unit}={work / 'glibc' / (unit + '.term')}"

    archive = [a for unit in units for a in ("--archive", glibc_spec(unit))]
    leaf_terms = [work / "glibc" / (unit + ".term") for unit in LEAVES]
    # Root every exported definition in the leaf units, including exported
    # aliases and data. No synthetic calls, and no local-name collisions.
    root = work / "string_units_root.term"
    run([env["SWIPL"], "-q", "-g", """
current_prolog_flag(argv, Files),
findall(N, (member(F, Files), read_file_to_terms(F, [module(Is)], []),
            member(I, Is),
            (I = func(N,L,_,_,_); I = data(N,L,_,_); I = alias(N,L,_)),
            L \\= local, L \\= ro(local), L \\= extern(weak)), Ns0),
sort(Ns0, Ns), findall(item(p,sym(N,0)), member(N,Ns), Init),
write_canonical(module([data(string_units_root,ro(export),8,Init)])),
write('.'), nl, halt
""", "--", *leaf_terms], env, root)
    hi = checked(HERE / "hi_atexit.c", work / "hi_atexit.term")
    hello_terms = sorted(hello.rglob("*.term"))
    if not hello_terms:
        raise ValueError(f"no GNU Hello terms under {hello}")
    # Keep Hello's ordinary objects and archive glibc. Local names use stable
    # capture-relative object paths, never temporary or store paths.
    hello_specs = [f"hello_{t.relative_to(hello)}={t}" for t in hello_terms]
    modules = [
        ("StringUnits", "string_units", "Rung-1 user glibc leaf units",
         [f"root={root}", *map(glibc_spec, LEAVES)]),
        ("HiAtexit", "hi_atexit", "hi_atexit.c with user glibc and exit handlers",
         [f"hi_atexit={hi}", *archive]),
        ("HelloGlibc", "hello_glibc", "GNU Hello 2.12.3 with user glibc",
         [*hello_specs, *archive]),
    ]
    status = 0
    for name, symbol, description, objects in modules:
        linked = work / (name + ".term")
        entry = "string_units_root" if name == "StringUnits" else "main"
        run([env["SWIPL"], NF / "rocq/scripts/link.pl", "--ctors", entry, *objects],
            env, linked)
        generated = work / (name + "Code.v")
        run([env["SWIPL"], NF / "rocq/scripts/gallina.pl", symbol, description, CHECKER],
            env, generated, linked)
        target = HERE / generated.name
        if args.update:
            shutil.copyfile(generated, target)
            print(f"glibc-fixtures: wrote {target.name}", flush=True)
        elif target.exists() and filecmp.cmp(generated, target, shallow=False):
            print(f"glibc-fixtures: {target.name} is current", flush=True)
        else:
            print(f"glibc-fixtures: {target.name} differs; run {CHECKER} --update", flush=True)
            status = 1
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--pp", type=lambda p: Path(p).resolve())
    parser.add_argument("--hello", type=lambda p: Path(p).resolve())
    parser.add_argument("--work-dir", type=lambda p: Path(p).resolve())
    parser.add_argument("-j", "--jobs", type=int, default=4)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    if args.work_dir:
        args.work_dir.mkdir(parents=True, exist_ok=True)
        return generate(args, args.work_dir)
    with tempfile.TemporaryDirectory(prefix="glibc-fixtures-") as work:
        return generate(args, Path(work))


if __name__ == "__main__":
    raise SystemExit(main())
