#!/usr/bin/env python3
"""Rerun the nanofil package survey (docs/survey.md).

  python3 nanofil/survey/run.py [--jobs N] [--cores N] [--timeout S] [--report] [NAME...]

Run from the repository root, after building nothing: it evaluates the
ports in ports.nix (survey/default.nix), sets aside C++ packages (by
their sources' file names) and those that build with LLVM, Rust or Go,
builds each remaining package with filcc (`ref`) and then with nanofil
alone (`nf`), each with the port's own checkPhase, and writes
survey/survey.tsv and the table in docs/survey.md between its markers.
Builds already in the store are not redone, so a rerun after a change to
nanofil rebuilds only the nanofil builds. Names restrict the survey."""

import argparse, concurrent.futures, json, os, re, subprocess, sys, tarfile, zipfile, collections

here = os.path.dirname(os.path.abspath(__file__))
work = os.environ.get("SURVEY_WORK", "/tmp/nanofil-survey")
CXX = (".cc", ".cpp", ".cxx", ".c++", ".C")
SKIP_DEPS = ("llvm", "clang", "rustc", "cargo", "go", "rust")


def sh(args, **kw):
    return subprocess.run(args, text=True, errors="replace", capture_output=True,
                          stdin=subprocess.DEVNULL, **kw)


def nix_build(drvs, log, a):
    """Build drvs (keep going) and return the set that timed out."""
    if not drvs:
        return set()
    args = ["nix", "build", "--no-link", "--keep-going", "-L", "-j", str(a.jobs),
            "--cores", str(a.cores), "--option", "timeout", str(a.timeout)]
    # If the client loses the daemon ("Nix daemon out of memory"), every
    # build still running is reported as failed without having failed:
    # build what is left again, at most twice.
    todo = drvs
    for _ in range(3):
        start = os.path.getsize(log) if os.path.exists(log) else 0
        with open(log, "a") as f:
            subprocess.run(args + [d + "^*" for d in todo], stdout=f,
                           stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        with open(log, "rb") as f:
            f.seek(start)
            lost = b"Nix daemon out of memory" in f.read()
        todo = [d for d in todo if not built(d)]
        if not lost or not todo:
            break
        print(f"nix daemon lost; building {len(todo)} again", file=sys.stderr)
    text = open(log, errors="replace").read()
    return set(re.findall(r"building of '(/nix/store/[^']+\.drv)[^']*' timed out", text)) | \
        set(re.findall(r"'(/nix/store/[^']+\.drv)' timed out", text))


def built(drv):
    outs = sh(["nix-store", "-q", "--outputs", drv]).stdout.split()
    return bool(outs) and all(os.path.exists(o) for o in outs)


# The first error, in this order of preference: nanofil's own, the
# wrapper's refusal, configure's verdict, any compiler or make error; a
# nanofil error in config.log (a probe's) only when nothing else says why.
ERR = [re.compile(p) for p in (
    r"^nanofil: .*", r"^nanofil-survey-cc: .*", r".*configure: error: .*",
    r".*\berror: .*", r".*Error [0-9]+.*", r".*\bFAIL\b.*", r"^nanofil-survey-config: .*",
    r".*No such file.*")]


def outcome(drv, timedout, docheck):
    """(status, first error, objects, cxx, fallbacks) of one build."""
    if built(drv):
        return ("tests pass" if docheck else "built"), "", *counts(sh(["nix", "log", drv]).stdout)
    if drv in timedout:
        return "timeout", "", "", "", ""
    log = sh(["nix", "log", drv]).stdout
    if not log:
        return "dependency fails", "", "", "", ""
    lines = [re.sub(r"\x1b\[[0-9;]*m", "", l) for l in log.splitlines()]
    phases = [l for l in lines if l.startswith("Running phase: ")]
    phase = phases[-1].split(": ", 1)[1] if phases else "?"
    status = "tests fail" if phase in ("checkPhase", "installCheckPhase") else "fails in " + phase
    start = max((i for i, l in enumerate(lines) if l == "Running phase: " + phase), default=0)
    first = ""
    for pat in ERR:
        m = next((l for l in lines[start:] if pat.match(l)), None) or \
            next((l for l in lines if pat.match(l) and pat.pattern.startswith("^nanofil")), None)
        if m:
            first = m
            break
    if not first:
        first = next((l for l in reversed(lines) if l.strip()), "")
    return status, first.strip()[:300], *counts(log)


def counts(log):
    m = re.findall(r"nanofil-survey: (\d+) objects, (\d+) C\+\+, (\d+) fallbacks", log)
    return m[-1] if m else ("", "", "")


def languages(src):
    """Counts of C and C++ source file names in a source tarball or tree."""
    names = []
    try:
        if os.path.isdir(src):
            for _, _, fs in os.walk(src):
                names += fs
        elif zipfile.is_zipfile(src):
            names = zipfile.ZipFile(src).namelist()
        elif tarfile.is_tarfile(src) and not src.endswith(".zst"):
            with tarfile.open(src) as t:
                names = [m.name for m in t.getmembers()]
        else:
            r = sh(["tar", "-tf", src])
            names = r.stdout.split("\n") if r.returncode == 0 else []
    except Exception:
        names = []
    c = sum(n.endswith(".c") for n in names)
    cxx = sum(n.endswith(CXX) for n in names)
    return c, cxx


def main():
    p = argparse.ArgumentParser()
    p.add_argument("names", nargs="*")
    p.add_argument("--jobs", type=int, default=6)
    p.add_argument("--cores", type=int, default=4)
    p.add_argument("--timeout", type=int, default=5400)
    p.add_argument("--classify", action="store_true", help="stop after setting packages aside")
    p.add_argument("--report", action="store_true", help="only rewrite docs/survey.md from survey.tsv")
    a = p.parse_args()
    if a.report:
        return report()
    os.makedirs(work, exist_ok=True)
    blog = os.path.join(work, "build.log")
    r = sh(["nix", "eval", "--json", "-f", here, "names"])
    if r.returncode:
        sys.exit(r.stderr)
    names = a.names or sorted(json.loads(r.stdout))
    # One evaluation per package: a missing attribute is not catchable
    # inside Nix, and one package's must not stop the others'.
    def one(n):
        r = sh(["nix", "eval", "--json", "-f", here, "meta." + n])
        if r.returncode:
            err = [l.strip() for l in r.stderr.splitlines() if "error:" in l]
            return n, {"eval_error": err[-1] if err else "?"}
        return n, json.loads(r.stdout)
    with concurrent.futures.ThreadPoolExecutor(8) as ex:
        meta = dict(ex.map(one, names))
    rows = {}
    todo = []
    srcs = [meta[n]["srcDrv"] for n in names if meta[n].get("srcDrv")]
    nix_build(srcs, os.path.join(work, "src.log"), a)
    for n in names:
        m = meta[n]
        row = dict(name=n, version=m.get("version") or "")
        deps = [d for d in (m.get("deps") or []) if d.split("-")[0] in SKIP_DEPS]
        c, cxx = languages(m["src"]) if m.get("src") and os.path.exists(m["src"]) else (0, 0)
        row["c"], row["cxx"] = c, cxx
        if not m.get("ref") or not m.get("nf"):
            row["kind"] = "evaluation fails"
            row["error"] = m.get("eval_error", "")
        elif deps:
            row["kind"] = "needs " + ", ".join(sorted(set(deps)))
        elif c == 0 and cxx == 0:
            row["kind"] = "no C sources found"
        elif 2 * cxx > c:  # C++ source files more than half as many as C's
            row["kind"] = "C++"
        else:
            row["kind"] = "C"
            todo.append(n)
        rows[n] = row
    print(f"{len(todo)} C packages of {len(names)}", file=sys.stderr)
    if a.classify:
        json.dump({"rows": rows, "meta": meta}, open(os.path.join(work, "classify.json"), "w"), indent=1)
        return
    tref = nix_build([meta[n]["ref"] for n in todo], blog, a)
    nfs = [meta[n]["nf"] for n in todo if built(meta[n]["ref"])]
    tnf = nix_build(nfs, blog, a)
    for n in todo:
        m, row = meta[n], rows[n]
        row["ref"], row["ref_error"], *_ = outcome(m["ref"], tref, m["doCheck"])
        if built(m["ref"]):
            (row["nf"], row["error"], row["objects"], row["cxx_objects"],
             row["fallbacks"]) = outcome(m["nf"], tnf, m["doCheck"])
        else:
            row["nf"] = "not tried"
    write(rows)


COLS = ["name", "version", "kind", "c", "cxx", "ref", "nf", "objects", "cxx_objects",
        "fallbacks", "cause", "error", "ref_error"]

# A failure's cause, from its first error; the first pattern that matches
# wins. Some configure verdicts are a probe's consequence, traced by hand
# (docs/survey.md): the pthread probe expands glibc's pthread_cleanup_push,
# autoconf's C89 probe has a K&R definition, gnulib's strerror_r and
# curl's prototype probes expect a conflicting redeclaration to fail.
CAUSES = [
    (r"resource_error|stack_overflow", "compiler resource limit"),
    (r"filc safety error|filc panic", "nanofil-built program traps"),
    (r"__atomic_(load|store|exchange|compare_exchange)\b", "generic __atomic builtins"),
    (r"alignment attributes|pthread|thread support|threads|threading", "alignment attributes"),
    (r"\basm\b", "inline or top-level asm"),
    (r"K&R|C-89|C99", "K&R definitions"),
    (r"cannot assign ptr\(char\) to int|prototype mismatch", "incompatible redeclarations accepted"),
    (r"__builtin_types_compatible_p|__builtin_choose_expr", "__builtin_types_compatible_p, __builtin_choose_expr"),
    (r"vector types", "vector types"),
    (r"undeclared identifier __builtin_", "other builtins"),
    (r"(initializer|assertion|case label) is not (a|an address) constant", "constant expressions not folded"),
    (r"ctor .* not defined|device-mapper", "constructor on a declaration"),
    (r"alias is supported only", "aliases beyond one prototyped function"),
    (r"GNU case ranges", "GNU case ranges"),
    (r"working compiler", "calls passing arguments to a () function"),
    (r"undefined reference", "unresolved Fil-C symbol at link"),
    (r"^nanofil: failed", "nanofil internal failure"),
]


# Test failures traced by hand to a cause the first error cannot show,
# applied while the package's tests fail (docs/survey.md, Causes).
TRACED = {
    "libressl": "timing-dependent test",
}


def cause(row):
    if row.get("nf") in ("built", "tests pass", "not tried", "", None):
        return ""
    if row.get("nf") == "tests fail" and row.get("name") in TRACED:
        return TRACED[row["name"]]
    err = row.get("error") or ""
    other = "package tests fail" if row.get("nf") == "tests fail" else "other syntax or typing gaps"
    return next((c for p, c in CAUSES if re.search(p, err)), other)


def write(rows):
    for r in rows.values():
        r["cause"] = cause(r) if r["kind"] == "C" else ""
    with open(os.path.join(here, "survey.tsv"), "w") as f:
        f.write("\t".join(COLS) + "\n")
        for n in sorted(rows):
            f.write("\t".join(str(rows[n].get(c, "")).replace("\t", " ") for c in COLS) + "\n")
    c = [r for r in rows.values() if r["kind"] == "C"]
    kinds = collections.Counter(r["kind"] if not r["kind"].startswith("needs") else "needs LLVM, Rust or Go"
                                for r in rows.values())
    aside = ["| Set aside | Packages |", "| --- | ---: |"] + \
        [f"| {k} | {v} |" for k, v in sorted(kinds.items()) if k != "C"]
    outcomes = collections.Counter((r["ref"], r["nf"]) for r in c)
    counts = ["| filcc | nanofil | Packages |", "| --- | --- | ---: |"] + \
        [f"| {a} | {b} | {v} |" for (a, b), v in sorted(outcomes.items(), key=lambda kv: -kv[1])]
    by = collections.defaultdict(list)
    for r in c:
        if r["cause"]:
            by[r["cause"]].append(r["name"])
    causes = ["| Cause | Packages | Which |", "| --- | ---: | --- |"] + \
        [f"| {k} | {len(v)} | {', '.join(sorted(v))} |"
         for k, v in sorted(by.items(), key=lambda kv: (-len(kv[1]), kv[0]))]
    table = ["| Package | Version | filcc | nanofil | nanofil objects | Cause | First error |",
             "| --- | --- | --- | --- | ---: | --- | --- |"]
    for r in sorted(c, key=lambda r: r["name"]):
        err = (r.get("error") or "").replace("|", "\\|").replace("`", "'")
        table.append(f"| {r['name']} | {r['version']} | {r['ref']} | {r['nf']} | "
                     f"{r.get('objects') or ''} | {r['cause']} | {('`' + err + '`') if err else ''} |")
    doc = os.path.join(here, "..", "docs", "survey.md")
    text = open(doc).read()
    start, end = "<!-- survey table -->", "<!-- end survey table -->"
    body = "\n\n".join("\n".join(x) for x in (aside, counts, causes, table))
    i, j = text.index(start) + len(start), text.index(end)
    open(doc, "w").write(text[:i] + "\n\n" + body + "\n\n" + text[j:])


def report():
    """Rewrite the tables from survey/survey.tsv, building nothing."""
    import csv
    with open(os.path.join(here, "survey.tsv")) as f:
        write({r["name"]: r for r in csv.DictReader(f, delimiter="\t")})


if __name__ == "__main__":
    main()
