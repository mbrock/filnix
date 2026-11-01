#!/usr/bin/env python3
"""Upstream Fil-C's test suite (filc/tests) built by nanofil.

    FILCC=/tmp/filcc/bin/clang SWIPL=/tmp/swipl/bin/swipl \
      nanofil/tests/filctests.py ~/fil-c [-j 24] [--filter RE] [--cc filcc]

The argument is a Fil-C checkout at the staging pin (lib/filc-staging.json).
Each test directory whose sources are all C is compiled as filc/run-tests
compiles it (manifest optFlags, default -O2, with -Ifilc/tests -g), but
each .c by nanofil: filcc preprocesses, the working tree's bin/nanofil
compiles, `as` assembles. filcc links, with filc/tests/utils.c, and builds
the manifest's libraries. Runs happen in the checkout, with output in
filc/test-output/NAME as the tests expect, in run-tests' default subrun
(FUGC_RAGE_MODE=1) or, with --modes all, in all four of its subruns. `return`, `output-includes` and
`output-excludes` are checked as run-tests checks them. `--cc filcc`
compiles with filcc instead, which separates failures of the environment
from nanofil's.

Each failure gets one category, and results.json in the output directory
lists every test's. Two categories are safety failures: "crash" (a
signal, not a Fil-C panic) and "missed trap" (exit 0 where the manifest
wants a panic or a crash); "trap message differs" is not one. docs/filc-tests.md has the categories and the latest
counts.
"""
import argparse, json, os, re, shlex, subprocess, sys, tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
NANOFIL = HERE.parent / "bin" / "nanofil"

ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
ap.add_argument("filc", type=Path, help="Fil-C checkout")
ap.add_argument("-j", type=int, default=os.cpu_count())
ap.add_argument("--filter", default=".", help="regex on test names")
ap.add_argument("--cc", choices=["nanofil", "filcc"], default="nanofil")
ap.add_argument("--timeout", type=int, default=180, help="seconds per run")
ap.add_argument("--modes", default="default",
                help="comma-separated run-tests subruns, or all: default (GC rage mode), "
                     "scribble, stw, release")
args = ap.parse_args()
ROOT = args.filc.resolve()
TESTS = ROOT / "filc/tests"
OUTDIR = Path("filc/test-output")  # relative to ROOT, as the tests expect
FILCC = os.environ.get("FILCC") or sys.exit("set FILCC to a filcc clang")
STATE = Path(tempfile.mkdtemp()) / "nanofil.state"
# run-tests' four ways to run a test (its subRuns).
MODE_ENV = {
    "default": "FUGC_RAGE_MODE=1",
    "scribble": "FUGC_RAGE_MODE=1 FUGC_SCRIBBLE=1 FUGC_VERIFY=1",
    "stw": "FUGC_MIN_THRESHOLD=0 FUGC_STW=1",
    "release": "",
}
MODES = list(MODE_ENV) if args.modes == "all" else args.modes.split(",")


def arr(x):
    return [] if x is None else x if isinstance(x, list) else [x]


def sh(cmd, log, timeout=600):
    try:
        p = subprocess.run(cmd, shell=True, cwd=ROOT, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                           timeout=timeout)
        out, rc = p.stdout, p.returncode
    except subprocess.TimeoutExpired as e:
        out, rc = (e.stdout or b"") + b"\n<<timeout>>\n", "timeout"
    with open(log, "ab") as f:
        f.write(b"$ " + cmd.encode() + b"\n" + out + b"\n")
    return rc, out.decode("utf-8", "replace")


def manifest(name):
    """The test's manifest, or None with the reason it is skipped."""
    d = TESTS / name
    if not (d / "manifest").exists():
        return None, None
    m = yaml.safe_load((d / "manifest").read_text()) or {}
    plat = m.get("only-on-platform")
    if plat and not re.search(plat, "x86_64-linux"):
        return None, "other platform"
    if any(k.startswith("needs") and k not in ("needsGLIBC", "needsAVX512", "needsSHANI")
           for k in m):
        return None, "needs a CPU feature or flavor"
    if m.get("skip"):
        return None, "skip"
    srcs = sorted(e.name for e in d.iterdir() if e.suffix in (".c", ".cpp", ".s", ".ll"))
    if not srcs:
        return None, None
    if any(not s.endswith(".c") for s in srcs):
        return None, "C++, assembly or IR"
    return (m, srcs), None


def compile_c(src, obj, opt, log):
    if args.cc == "filcc":
        return sh(f"{FILCC} -c -o {obj} {src} -Ifilc/tests {opt} -g", log)
    rc, out = sh(f"{FILCC} -E -U__SIZEOF_INT128__ -o {obj}.i {src} -Ifilc/tests {opt}", log)
    if rc != 0:
        return rc, out
    # The flags nanofil-cc (nix/nanofil-cc.nix) maps onto nanofil's.
    flags, env = opt.split(), ""
    opts = "--inline=none" if {"-O0", "-fno-inline"} & set(flags) else ""
    if {"-fno-builtin", "-ffreestanding"} & set(flags):
        opts += " --memcpy=call"
    if "-fcommon" in flags:
        env += " NANOFIL_COMMON=1"
    for f in flags:
        if re.fullmatch(r"-std=(c|gnu)(23|2x)", f):
            env += " NANOFIL_STD=c23"
        elif re.fullmatch(r"-std=(c|gnu)(89|90)|-ansi|-fgnu89-inline", f):
            env += " NANOFIL_STD=gnu89"
    rc, out = sh(f"cd {NANOFIL.parent.parent / 'src'} && NANOFIL_STATE={STATE}{env} "
                 f"{NANOFIL} {opts} cc {ROOT / obj}.i > {ROOT / obj}.s", log)
    if rc != 0:
        return rc, out
    return sh(f"as -o {obj} {obj}.s", log)


TRAP = re.compile(r"filc safety error|filc user error|filc panic")


def outcome(name):
    (m, srcs), _ = manifest(name)
    o = OUTDIR / name
    subprocess.run(["rm", "-rf", str(ROOT / o)])
    (ROOT / o).mkdir(parents=True)
    log = ROOT / o / "log.txt"
    expect, opt = m["return"], m.get("optFlags", "-O2")
    for s in srcs:
        rc, out = compile_c(TESTS / name / s, o / f"{s}.o", opt, log)
        if expect == "compileFailure":
            if rc == 0:
                return "wrong", f"compiled {s}, which filcc refuses"
        elif rc == "timeout":
            return "compile timeout", s
        elif rc != 0:
            msg = re.search(r"^nanofil: (?:\S+:\d+: )?(.*)$", out, re.M)
            return ("refused", msg.group(1)) if msg else ("compile error", out.strip()[-300:])
    if expect == "compileFailure":
        text = log.read_text(errors="replace")
        lacks = [e for e in arr(m.get("output-includes")) if e not in text]
        return ("pass", "") if not lacks else ("diagnostic differs", lacks[0])
    if expect == "compileOnly":
        return "pass", ""
    libfiles = set()
    for lib, data in (m.get("libraries") or {}).items():
        objs = " ".join(f"{o / f}.o" for f in data["files"])
        libfiles |= set(data["files"])
        if data.get("isStatic"):
            cmd = f"ar cr {o / lib}.a {objs}"
        else:
            ext = "" if data.get("isBundle") else ".so"
            cmd = f"{FILCC} -shared -o {o / lib}{ext} {objs} {data.get('extraLinkerArgs', '')}"
        rc, out = sh(cmd, log)
        if rc != 0:
            return "link error", out.strip()[-300:]
    objs = " ".join(f"{o / s}.o" for s in srcs if s not in libfiles)
    rc, out = sh(f"{FILCC} -o {o / name} {objs} {m.get('extraLinkerArgs', '')} -lm "
                 f"{o.parent / 'utils.o'}", log)
    if expect == "linkFailure":
        return ("pass", "") if rc != 0 else ("wrong", "linked, which filcc refuses")
    if rc != 0:
        undef = re.search(r"undefined reference to '(?:pizlonated_)?([^']*)'", out)
        return "link error", (f"undefined {undef.group(1)}" if undef else out.strip()[-300:])
    for d in arr(m.get("mkdirs")):
        (ROOT / o / d).mkdir(parents=True, exist_ok=True)
    ldp = f"LD_LIBRARY_PATH={m['extraLDPath']} " if m.get("extraLDPath") else ""
    env = " ".join(arr(m.get("extra-env")))
    extra = " ".join(shlex.quote(str(a)) for a in arr(m.get("extraArgs")))
    for mode in MODES:
        if not (m.get("subRuns") or {mode: True}).get(mode):
            continue
        rc, out = sh(f"ulimit -c 0; {MODE_ENV[mode]} FILC_EXIT_ON_PANIC=1 FILC_DUMP_SETUP=1 "
                     f"{ldp}{env} {o / name} {extra}", log, timeout=args.timeout)
        verdict = judge(m, expect, rc, out)
        if verdict[0] != "pass":
            return verdict[0], (f"[{mode}] " if len(MODES) > 1 else "") + verdict[1]
    return "pass", ""


def judge(m, expect, rc, out):
    """One run's category, by Filip Pizlo's triage: a crash (a signal, not
    a Fil-C panic) or a missed trap is a safety failure; a different
    panic where one is due is not."""
    if rc == "timeout":
        return "run timeout", ""
    ok = {"failure": rc == 42, "crash": rc != 0, "success": rc == 0,
          "exit13": rc == 13, "dontCrash": rc in (0, 42)}[expect]
    lacks = [e for e in arr(m.get("output-includes")) if e not in out]
    has = [e for e in arr(m.get("output-excludes")) if e in out]
    if ok and not lacks and not has:
        return "pass", ""
    trapped = rc == 42 and TRAP.search(out)
    first = (TRAP.search(out) and out[TRAP.search(out).start():].splitlines()[0]) or ""
    if expect != "crash" and (rc < 0 or rc >= 128):
        return "crash", f"signal {rc - 128 if rc >= 128 else -rc}"
    if expect in ("failure", "crash") and rc == 0:
        return "missed trap", f"exited 0; expected {expect}"
    if expect in ("failure", "crash") and trapped:
        return "trap message differs", f"wanted {lacks[0]!r}, got {first!r}" if lacks else first
    if trapped:
        return "spurious trap", first
    if not ok:
        return "wrong exit", f"rc={rc}, expected {expect}"
    return "wrong output", f"lacks {lacks[0]!r}" if lacks else f"has {has[0]!r}"


def run(name):
    try:
        cat, detail = outcome(name)
    except Exception as e:  # a runner bug, not a test result
        cat, detail = "runner error", repr(e)
    print(f"{cat:22} {name} {detail}"[:200], flush=True)
    return {"test": name, "category": cat, "detail": detail}


def main():
    if args.cc == "nanofil":
        subprocess.run(f"cd {NANOFIL.parent.parent / 'src'} && {NANOFIL} --save-state {STATE}",
                       shell=True, check=True, stdin=subprocess.DEVNULL)
    (ROOT / OUTDIR).mkdir(parents=True, exist_ok=True)
    subprocess.run(f"{FILCC} -O3 -c -o {OUTDIR / 'utils.o'} filc/tests/utils.c -Ifilc/tests",
                   shell=True, cwd=ROOT, check=True)
    names, skipped = [], Counter()
    for e in sorted(os.listdir(TESTS)):
        if not re.search(args.filter, e):
            continue
        sel, why = manifest(e)
        if sel:
            names.append(e)
        elif why:
            skipped[why] += 1
    print(f"{len(names)} tests; skipped: {dict(skipped)}", flush=True)
    with ThreadPoolExecutor(args.j) as ex:
        results = list(ex.map(run, names))
    out = ROOT / OUTDIR / "results.json"
    out.write_text(json.dumps({"cc": args.cc, "skipped": skipped, "results": results}, indent=1))
    print()
    for cat, n in Counter(r["category"] for r in results).most_common():
        print(f"{n:6} {cat}")
    print(f"results: {out}")


main()
