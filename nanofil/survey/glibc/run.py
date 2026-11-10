#!/usr/bin/env python3
"""Compile user glibc's translation units to nanofil IR (docs/zsys.md).

A by-hand experiment, not a check: it measures how much of user glibc
nanofil's C frontend reads, and why the rest fails. It does not build a
libc.

  nix build -f nanofil/survey/glibc/capture.nix -o /tmp/glibc-pp
  nanofil/bin/nanofil --save-state /tmp/nanofil.state
  NANOFIL_STATE=/tmp/nanofil.state python3 nanofil/survey/glibc/run.py \
      /tmp/glibc-pp /tmp/glibc-nf [-j 12] [--timeout 120] [--only libc]
  python3 nanofil/survey/glibc/run.py --report /tmp/glibc-nf

Each captured OBJ.i whose object is a shared one (.os, what libc.so and
its siblings link) goes through `nanofil cc-ir`. OK units leave their IR
in OUT/ir/OBJ.ir; failures their stderr in OUT/err/OBJ.err. OUT/units.tsv
has one row per unit (object, module, status, seconds, cause, first
message), and --report prints the counts by module and by cause.
"""

import argparse, collections, concurrent.futures, os, re, subprocess, sys, time

here = os.path.dirname(os.path.abspath(__file__))
nanofil = os.path.join(here, "..", "..", "bin", "nanofil")
src = os.path.join(here, "..", "..", "src")

# (cause, pattern on the first error message). The first match wins.
CAUSES = [
    ("timeout", r"^timeout"),
    ("stack or memory", r"resource_error|Out of global|Stack limit|out of memory"),
    ("Fil-C module asm (.filc_*)", r'top-level asm "\.filc_'),
    ("other top-level asm", r"top-level asm"),
    ("inline asm", r"\basm\b|__asm__|assembl"),
    ("__int128", r"__int128|int128"),
    ("_Float128 / long double math", r"_Float128|__float128|_Float64x|_Float32x"),
    ("vectors", r"vector|__m128|__m256|ext_vector"),
    ("complex", r"_Complex|complex"),
    ("builtin", r"__builtin_[A-Za-z0-9_]+|builtin"),
    ("attribute", r"attribute|__attribute__"),
    ("atomics", r"_Atomic|__atomic|__sync_"),
    ("thread-local", r"__thread|_Thread_local|thread_local|tls"),
    ("bit-fields", r"bit-?field"),
    ("labels as values / computed goto", r"computed goto|&&|label address|goto \*"),
    ("nested functions", r"nested function"),
    ("variable-length arrays", r"variable[- ]length|VLA"),
    ("statement expressions", r"statement expression|\(\{"),
    ("aliases / symbol versioning", r"alias|symver|\.symver"),
    ("setjmp", r"setjmp|nonlocal"),
    ("parse", r"C parse failed|parse"),
    ("lexer / preprocessor", r"lexer|preprocessing|unterminated"),
    ("types", r"type|incompatible|conversion|cast"),
    ("undeclared or unknown name", r"undeclared|unknown|no member|not declared"),
    ("initializer", r"initiali[sz]er"),
    ("constant expression", r"constant"),
]


def first_message(err):
    for line in err.splitlines():
        line = line.strip()
        if not line or line.startswith("Warning:") or line.startswith("%"):
            continue
        return line[:300]
    return ""


def cause_of(msg):
    for name, pat in CAUSES:
        if re.search(pat, msg):
            return name
    return "other"


def module_of(cmd):
    m = re.search(r"-DMODULE_NAME=(\S+)", cmd)
    return m.group(1) if m else "?"


def cc_options(cmd):
    """The environment and options nanofil-cc (nix/nanofil-cc.nix) derives
    from a compile command's flags, so each unit is read as the survey
    would compile it: glibc's -fgnu89-inline gives its extern inline
    functions the GNU rule (NANOFIL_STD=gnu89)."""
    env, opts = {}, []
    for a in cmd.split():
        if a in ("-std=c23", "-std=gnu23", "-std=c2x", "-std=gnu2x"):
            env["NANOFIL_STD"] = "c23"
        elif a in ("-std=c89", "-std=c90", "-std=gnu89", "-std=gnu90", "-std=iso9899:1990",
                   "-std=iso9899:199409", "-ansi", "-fgnu89-inline"):
            env["NANOFIL_STD"] = "gnu89"
        elif a.startswith("-std="):
            env.pop("NANOFIL_STD", None)
        elif a in ("-fno-builtin", "-fno-builtin-memcpy", "-fno-builtin-memmove", "-ffreestanding"):
            opts = [o for o in opts if not o.startswith("--memcpy")] + ["--memcpy=call"]
        elif a in ("-fno-inline", "-O0"):
            opts = [o for o in opts if not o.startswith("--inline")] + ["--inline=none"]
        elif a == "-fcommon":
            env["NANOFIL_COMMON"] = "1"
        elif a == "-fno-common":
            env.pop("NANOFIL_COMMON", None)
    return env, opts


def units(pp, only):
    for root, _, files in os.walk(pp):
        for f in files:
            if not f.endswith(".os.i"):
                continue
            path = os.path.join(root, f)
            obj = os.path.relpath(path, pp)[:-2]
            with open(path[:-2] + ".cmd", errors="replace") as fh:
                cmd = fh.read()
            mod = module_of(cmd)
            if only and mod not in only:
                continue
            yield obj, mod, path, cc_options(cmd)


# A top-level asm statement of Fil-C's module-asm directives (.filc_rename,
# .filc_alias, .filc_weak_alias, .filc_weak, .filc_globl, ...), as
# libc-symbols.h's hidden_proto, hidden_def and their kin expand. Their
# names never hold a parenthesis.
FILC_ASM = re.compile(rb'\b(?:__asm__|__asm|asm)\s*\(\s*"\.filc_[^)]*\)\s*;')


# The only __int128 in the corpus: three unused padding members of
# bits/link.h's audit structs, which ldsodefs.h brings into 732 units.
INT128_PAD = re.compile(rb'\b__int128_t (__glibc_unused\d)((?:\[\d+\])?);')


def rewrite(path, dest, drop, pad):
    """Write path's text to dest, without .filc_* module asm (drop) and
    with the padding members as aligned bytes (pad), keeping line numbers."""
    with open(path, "rb") as fh:
        text = fh.read()
    if drop:
        text = FILC_ASM.sub(lambda m: b"\n" * m.group(0).count(b"\n"), text)
    if pad:
        text = INT128_PAD.sub(rb'__attribute__((__aligned__(16))) unsigned char \1\2[16];', text)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    with open(dest, "wb") as fh:
        fh.write(text)


def compile_one(job):
    obj, mod, path, (ccenv, ccopts), out, timeout, drop, pad = job
    env = dict(os.environ)
    env.pop("NANOFIL_STD", None)
    env.pop("NANOFIL_COMMON", None)
    env.update(ccenv)
    t = time.monotonic()
    tmp = None
    if drop or pad:
        tmp = os.path.join(out, "in", obj + ".i")
        rewrite(path, tmp, drop, pad)
        path = tmp
    try:
        p = subprocess.run([nanofil] + ccopts + ["cc-ir", os.path.abspath(path)], cwd=src, env=env,
                           stdin=subprocess.DEVNULL, capture_output=True, timeout=timeout)
        status = "ok" if p.returncode == 0 else "error"
        stdout, stderr = p.stdout, p.stderr.decode(errors="replace")
    except subprocess.TimeoutExpired:
        status, stdout, stderr = "timeout", b"", "timeout after %ds" % timeout
    secs = time.monotonic() - t
    if status == "ok":
        dest = os.path.join(out, "ir", obj + ".ir")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "wb") as fh:
            fh.write(stdout)
        msg, cause = "", ""
    else:
        dest = os.path.join(out, "err", obj + ".err")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w") as fh:
            fh.write(stderr)
        msg = first_message(stderr) if status == "error" else stderr
        cause = cause_of(msg)
    if tmp:
        os.remove(tmp)
    return obj, mod, status, secs, cause, msg


def report(out):
    rows = []
    with open(os.path.join(out, "units.tsv")) as fh:
        next(fh)
        for line in fh:
            obj, mod, status, secs, cause, msg = line.rstrip("\n").split("\t")
            rows.append((obj, mod, status, float(secs), cause, msg))
    by_mod = collections.defaultdict(collections.Counter)
    for r in rows:
        by_mod[r[1]][r[2]] += 1
    print("| module | units | to IR | fail | timeout |\n| --- | ---: | ---: | ---: | ---: |")
    tot = collections.Counter()
    for mod in sorted(by_mod, key=lambda m: -sum(by_mod[m].values())):
        c = by_mod[mod]
        n = sum(c.values())
        tot.update(c)
        print("| %s | %d | %d | %d | %d |" % (mod, n, c["ok"], c["error"], c["timeout"]))
    print("| all | %d | %d | %d | %d |" % (sum(tot.values()), tot["ok"], tot["error"], tot["timeout"]))
    print()
    causes = collections.Counter(r[4] for r in rows if r[2] != "ok")
    print("| cause | units | example |\n| --- | ---: | --- |")
    for cause, n in causes.most_common():
        ex = next(r for r in rows if r[2] != "ok" and r[4] == cause)
        print("| %s | %d | `%s`: %s |" % (cause, n, ex[0], ex[5][:120].replace("|", "\\|")))
    print()
    msgs = collections.Counter(re.sub(r"\d+", "N", r[5])[:100] for r in rows if r[2] != "ok")
    print("Most common first messages:")
    for m, n in msgs.most_common(40):
        print("%5d  %s" % (n, m))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pp", nargs="?")
    ap.add_argument("out")
    ap.add_argument("-j", type=int, default=max(1, (os.cpu_count() or 2) - 2))
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--only", action="append", help="MODULE_NAME to keep, such as libc")
    ap.add_argument("--drop-filc-asm", action="store_true",
                    help="remove .filc_* module asm first, which nanofil does not read yet")
    ap.add_argument("--int128-padding", action="store_true",
                    help="read bits/link.h's __int128_t padding as aligned bytes")
    ap.add_argument("--report", action="store_true")
    a = ap.parse_args()
    if a.report:
        report(a.pp or a.out)
        return
    if not os.environ.get("NANOFIL_STATE"):
        print("set NANOFIL_STATE (nanofil --save-state FILE) for 0.05 s starts", file=sys.stderr)
    jobs = sorted(units(a.pp, a.only))
    print("glibc-nf: %d units, %d at a time" % (len(jobs), a.j), file=sys.stderr, flush=True)
    os.makedirs(a.out, exist_ok=True)
    done = collections.Counter()
    t0 = time.monotonic()
    with open(os.path.join(a.out, "units.tsv"), "w") as tsv, \
            concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        tsv.write("object\tmodule\tstatus\tseconds\tcause\tmessage\n")
        futs = [ex.submit(compile_one, (o, m, p, cc, a.out, a.timeout, a.drop_filc_asm,
                                             a.int128_padding))
                for o, m, p, cc in jobs]
        for i, f in enumerate(concurrent.futures.as_completed(futs), 1):
            obj, mod, status, secs, cause, msg = f.result()
            done[status] += 1
            tsv.write("%s\t%s\t%s\t%.2f\t%s\t%s\n" % (obj, mod, status, secs, cause,
                                                      msg.replace("\t", " ").replace("\n", " ")))
            if i % 50 == 0 or i == len(futs):
                print("glibc-nf: %d/%d after %.0fs: %s" % (i, len(futs), time.monotonic() - t0,
                                                           dict(done)), file=sys.stderr, flush=True)
    report(a.out)


if __name__ == "__main__":
    main()
