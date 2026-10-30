#!/usr/bin/env python3
"""The nanofil package survey's manifest and report (docs/survey.md).

The campaign service on swa (docs/campaign-service.md) builds the
survey; this script freezes what it builds and reports what it found:

  campaignctl submit nanofil-survey --opt plain [--rev REV]
      runs `run.py manifest` from the frozen revision: evaluates the
      ports in ports.nix (survey/default.nix), sets aside C++ packages
      (by their sources' file names), those that build with LLVM, Rust
      or Go, and the slow ones, and prints a manifest with `ref.NAME`
      (filcc) and `nf.NAME` (nanofil alone; requires ref.NAME) roots.
  python3 nanofil/survey/run.py report CAMPAIGN
      reads the campaign's results from the service and writes
      survey/survey.tsv (survey-OPT.tsv with an --opt) and, for the
      plain survey, the table in docs/survey.md between its markers.
  python3 nanofil/survey/run.py --report
      rewrites the docs/survey.md tables from survey.tsv alone."""

import argparse, concurrent.futures, json, os, re, subprocess, sys, tarfile, zipfile, collections

here = os.path.dirname(os.path.abspath(__file__))
work = os.environ.get("SURVEY_WORK", "/tmp/nanofil-survey")
CXX = (".cc", ".cpp", ".cxx", ".c++", ".C")
SKIP_DEPS = ("llvm", "clang", "rustc", "cargo", "go", "rust")


def sh(args, **kw):
    return subprocess.run(args, text=True, errors="replace", capture_output=True,
                          stdin=subprocess.DEVNULL, **kw)


def fetch(drvs, log):
    """Realise the sources (keep going), to read their file names."""
    if not drvs:
        return
    with open(log, "a") as f:
        subprocess.run(["nix", "build", "--no-link", "--keep-going"] + [d + "^*" for d in drvs],
                       stdout=f, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)


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


def classify(ev, names):
    """Evaluate every port and set aside what the survey does not build."""
    # One evaluation per package: a missing attribute is not catchable
    # inside Nix, and one package's must not stop the others'.
    def one(n):
        r = sh(ev + ["meta." + n])
        if r.returncode:
            err = [l.strip() for l in r.stderr.splitlines() if "error:" in l]
            return n, {"eval_error": err[-1] if err else "?"}
        return n, json.loads(r.stdout)
    with concurrent.futures.ThreadPoolExecutor(8) as ex:
        meta = dict(ex.map(one, names))
    os.makedirs(work, exist_ok=True)
    fetch([meta[n]["srcDrv"] for n in names if meta[n].get("srcDrv")],
          os.path.join(work, "src.log"))
    rows = {}
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
        rows[n] = row
    return rows, meta


def manifest(a):
    """Print the frozen survey's manifest for the campaign service."""
    ev = ["nix", "eval", "--json", "-f", here] + (["--argstr", "opt", a.opt] if a.opt else [])
    r = sh(ev + ["names"])
    if r.returncode:
        sys.exit(r.stderr)
    names = a.names or sorted(json.loads(r.stdout))
    slow = json.loads(sh(ev + ["slow"]).stdout or "{}")
    rows, meta = classify(ev, names)
    roots, aside = [], []
    for n in sorted(rows):
        row, m = rows[n], meta[n]
        selected = row["kind"] == "C" and (
            a.select == "all" or (n in slow) == (a.select == "slow"))
        if not selected:
            if row["kind"] == "C":
                row["kind"] = "slow"
                row["error"] = slow.get(n, "")
            aside.append(row)
            continue
        info = dict(package=n, version=row["version"], doCheck=bool(m.get("doCheck")),
                    c=row["c"], cxx=row["cxx"])
        tags = ["slow"] if n in slow else []
        roots.append(dict(name="ref." + n, drv=m["ref"], tags=["ref"] + tags, meta=info))
        roots.append(dict(name="nf." + n, drv=m["nf"], tags=["nf"] + tags,
                          requires=["ref." + n], meta=info))
    opt = a.opt or "plain"
    kind = "bench" if a.select == "slow" else "nanofil-survey"
    print(f"{len(roots) // 2} packages of {len(names)}", file=sys.stderr)
    json.dump(dict(id=f"{kind}-{opt}-{a.revision}", kind=kind,
                   name=f"nanofil survey · {opt}" + (" · slow" if a.select == "slow" else ""),
                   source=a.source, revision=a.revision,
                   options=dict(opt=opt, select=a.select),
                   roots=roots, set_aside=aside), sys.stdout)


def status(r):
    """The survey's words for a root's latest attempt (web.cc survey_status)."""
    state, outcome = r.get("state"), r.get("outcome")
    if state == "running":
        return "building"
    if not outcome:
        return "pending" if state == "pending" else ""
    if outcome in ("built", "already-valid", "substituted", "resolves-to-already-valid"):
        return "tests pass" if (r.get("meta") or {}).get("doCheck") else "built"
    if outcome == "timed-out":
        return "timeout"
    if outcome == "skipped":
        return "not tried"
    if outcome in ("cancelled", "incomplete"):
        return "interrupted"
    if r.get("native_status") == "DependencyFailed":
        return "dependency fails"
    phase = r.get("phase") or ""
    if phase in ("checkPhase", "installCheckPhase"):
        return "tests fail"
    return "fails in " + phase if phase else outcome


def seconds(r):
    return f"{r['build_ns'] / 1e9:.0f}" if r and r.get("build_ns") is not None else ""


def machine(r):
    if not r or r.get("build_ns") is None:
        return ""
    m = r.get("machine") or "local"
    return m.split("@")[-1].split("://")[-1].split(".")[0]


def campaign_report(a):
    """survey.tsv and the docs/survey.md table from a campaign's results."""
    if a.results:
        results = json.load(open(a.results))
    else:
        ctl = os.environ.get("CAMPAIGNCTL") or next(
            (c for c in ("/opt/filnix-campaign/bin/campaignctl",) if os.path.exists(c)),
            "campaignctl")
        r = sh([ctl, "--json", "results", a.campaign])
        if r.returncode:
            sys.exit(r.stderr)
        results = json.loads(r.stdout)
    campaign = results["campaign"]
    extras = campaign.get("extras") or {}
    if isinstance(extras, str):
        extras = json.loads(extras)
    rows = {r["name"]: r for r in extras.get("set_aside", [])}
    pairs = collections.defaultdict(dict)
    for root in results["roots"]:
        for k in ("meta", "tags", "counts"):
            if isinstance(root.get(k), str):
                root[k] = json.loads(root[k])
        pairs[root["meta"]["package"]]["nf" if "nf" in root["tags"] else "ref"] = root
    for n, p in pairs.items():
        ref, nf = p.get("ref"), p.get("nf")
        m = (ref or nf)["meta"]
        row = dict(name=n, version=m.get("version", ""), kind="C", c=m.get("c", ""),
                   cxx=m.get("cxx", ""), ref=status(ref) if ref else "",
                   ref_error=(ref or {}).get("error") or "",
                   ref_s=seconds(ref), nf=status(nf) if nf else "",
                   nf_s=seconds(nf), nf_machine=machine(nf))
        if nf and nf.get("outcome") not in (None, "skipped"):
            counts = nf.get("counts") or {}
            row.update(error=nf.get("error") or "", objects=counts.get("objects", ""),
                       cxx_objects=counts.get("cxx", ""), fallbacks=counts.get("fallbacks", ""))
        if row["nf"] == "timeout":
            row["error"] = ""
        rows[n] = row
    opt = (campaign.get("options") or {})
    if isinstance(opt, str):
        opt = json.loads(opt)
    opt = opt.get("opt", "plain")
    write(rows, "" if opt == "plain" else opt, campaign)


def main():
    p = argparse.ArgumentParser()
    sub = p.add_subparsers(dest="command")
    m = sub.add_parser("manifest", help="print the survey's manifest")
    m.add_argument("names", nargs="*")
    m.add_argument("--opt", default="", help="nanofil options for every compile, e.g. -O")
    m.add_argument("--select", choices=("default", "slow", "all"), default="default",
                   help="leave out (default), only (slow) or keep the slow packages")
    m.add_argument("--source", default="", help="the frozen flake reference")
    m.add_argument("--revision", default="", help="the frozen revision")
    r = sub.add_parser("report", help="write survey.tsv and docs/survey.md from a campaign")
    r.add_argument("campaign", nargs="?")
    r.add_argument("--results", help="a `campaignctl --json results` file instead")
    p.add_argument("--report", action="store_true", help="only rewrite docs/survey.md from survey.tsv")
    a = p.parse_args()
    if a.report:
        return report()
    if a.command == "manifest":
        if a.opt == "plain":
            a.opt = ""
        return manifest(a)
    if a.command == "report":
        if not a.campaign and not a.results:
            p.error("report needs a campaign or --results")
        return campaign_report(a)
    p.print_help()


COLS = ["name", "version", "kind", "c", "cxx", "ref", "nf", "objects", "cxx_objects",
        "fallbacks", "cause", "error", "ref_error", "ref_s", "nf_s", "nf_machine"]

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
    if row.get("nf") in ("built", "tests pass", "not tried", "", None,
                         "pending", "building", "interrupted"):
        return ""
    if row.get("nf") == "tests fail" and row.get("name") in TRACED:
        return TRACED[row["name"]]
    err = row.get("error") or ""
    if row.get("nf") == "timeout":
        return "build timeout"
    other = "package tests fail" if row.get("nf") == "tests fail" else "other syntax or typing gaps"
    return next((c for p, c in CAUSES if re.search(p, err)), other)


def write(rows, opt="", campaign=None):
    for r in rows.values():
        r["cause"] = cause(r) if r["kind"] == "C" else ""
    tsv = "survey" + ("-" + opt.strip("-").replace(" ", "") if opt else "") + ".tsv"
    with open(os.path.join(here, tsv), "w") as f:
        f.write("\t".join(COLS) + "\n")
        for n in sorted(rows):
            f.write("\t".join(str(rows[n].get(c, "")).replace("\t", " ") for c in COLS) + "\n")
    if opt:
        return
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
    table = ["| Package | Version | filcc | nanofil | nanofil s | nanofil objects | Cause | First error |",
             "| --- | --- | --- | --- | ---: | ---: | --- | --- |"]
    for r in sorted(c, key=lambda r: r["name"]):
        err = (r.get("error") or "").replace("|", "\\|").replace("`", "'")
        table.append(f"| {r['name']} | {r['version']} | {r['ref']} | {r['nf']} | "
                     f"{r.get('nf_s') or ''} | {r.get('objects') or ''} | {r['cause']} | {('`' + err + '`') if err else ''} |")
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
