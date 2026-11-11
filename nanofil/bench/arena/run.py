#!/usr/bin/env python3
"""M0 benchmark & correctness gate for the 32-bit `w` arena (`docs/lambda-anf.md`).

1. Runs a formal-interpreter `difftest.sh` check on `kernels.ir` with a tiny
   64-word nursery so `interp:run/5` (`Semantics.v`) and native Fil-C execute
   real Cheney `minor_gc` evacuations across `list_sum`, `term_eqb` and `avl`
   and agree bit-for-bit.
2. Runs a 1,024-word nursery GC stress test (47,434 minor GCs) on both
   `arena-ir-checked` and `arena-ir-erased` under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.
3. Runs 1 warmup + TRIALS interleaved, CPU-pinned rounds across all 7 modes at
   SCALE (default 4: ~32.8M Cons cells, ~15.8M Term blocks, ~9.6M AVL nodes),
   verifying identical 64-bit checksums on every run and printing Markdown
   tables of wall-time medians, ratios to `ocamlopt`, peak RSS and loop sizes.
"""
import argparse, json, os, random, re, shutil, statistics, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "../../.."))
NANOFIL = os.path.join(REPO, "nanofil")

SELFTEST_IR = """
func(init_tiny_state, local, void, [param(p, tmp(st))], [
    block(entry, [], [
        let(tmp(ast), a, check(0, 28, write, 4), [tmp(st)]),
        raw_store(w, 0, const(1800), tmp(ast)),
        raw_store(w, 4, const(1), tmp(ast)),
        raw_store(w, 8, const(1800), tmp(ast)),
        raw_store(w, 12, const(1864), tmp(ast)),
        raw_store(w, 16, const(1800), tmp(ast)),
        raw_store(w, 20, const(0), tmp(ast)),
        raw_store(w, 24, const(0), tmp(ast))
    ], ret)
]).

run(selftest_list, []).
func(selftest_list, export, l, [], [
    block(entry, [], [
        let(tmp(arena), p, alloc(8), [const(8192)]),
        let(tmp(roots), p, alloc(8), [const(512)]),
        let(tmp(st), p, alloc(8), [const(32)]),
        call(void, global(init_tiny_state), [arg(p, tmp(st))]),
        call(result(tmp(r), l), global(bench_list),
             [arg(p, tmp(arena)), arg(p, tmp(roots)), arg(p, tmp(st)),
              arg(w, const(32)), arg(w, const(3))])
    ], ret(tmp(r)))
]).

run(selftest_term, []).
func(selftest_term, export, l, [], [
    block(entry, [], [
        let(tmp(arena), p, alloc(8), [const(8192)]),
        let(tmp(roots), p, alloc(8), [const(512)]),
        let(tmp(st), p, alloc(8), [const(32)]),
        call(void, global(init_tiny_state), [arg(p, tmp(st))]),
        call(result(tmp(r), l), global(bench_term),
             [arg(p, tmp(arena)), arg(p, tmp(roots)), arg(p, tmp(st)),
              arg(w, const(2)), arg(w, const(3))])
    ], ret(tmp(r)))
]).

run(selftest_avl, []).
func(selftest_avl, export, l, [], [
    block(entry, [], [
        let(tmp(arena), p, alloc(8), [const(16384)]),
        let(tmp(roots), p, alloc(8), [const(512)]),
        let(tmp(st), p, alloc(8), [const(32)]),
        call(void, global(init_tiny_state), [arg(p, tmp(st))]),
        call(result(tmp(r), l), global(bench_avl),
             [arg(p, tmp(arena)), arg(p, tmp(roots)), arg(p, tmp(st)),
              arg(w, const(24)), arg(w, const(2))])
    ], ret(tmp(r)))
]).
"""


def find_tool(env_var, candidates):
    if env_var in os.environ and os.path.exists(os.environ[env_var]):
        return os.environ[env_var]
    for c in candidates:
        if os.path.isabs(c) and os.path.exists(c):
            return c
        w = shutil.which(c)
        if w:
            return w
    raise SystemExit(f"missing tool {env_var}: tried {candidates}")


def count_loop_insts(asm_path, start_label, end_label):
    lines = open(asm_path).readlines()
    inside = False
    n = 0
    for l in lines:
        s = l.strip()
        if s == f"{start_label}:":
            inside = True
            continue
        if inside and s == f"{end_label}:":
            break
        if inside and l.startswith("\t") and not s.startswith("."):
            n += 1
    return n


def parse_output(stdout):
    res = {}
    for line in stdout.strip().splitlines():
        parts = line.split("\t")
        if len(parts) >= 3:
            res[parts[0]] = (int(parts[1]), float(parts[2]))
    return res


def measure_rss_mb(cmd, env=None):
    out = subprocess.check_output(
        ["/usr/bin/env", "python3", "-c",
         "import resource, subprocess, sys; "
         "subprocess.check_call(sys.argv[1:], stdout=subprocess.DEVNULL); "
         "print(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024.0)",
         *cmd],
        env=env, text=True
    )
    return float(out.strip())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=7)
    ap.add_argument("--scale", type=int, default=3)
    ap.add_argument("--cpu", type=int, default=2)
    ap.add_argument("--json", default="")
    ap.add_argument("--skip-difftest", action="store_true")
    args = ap.parse_args()

    filcc = find_tool("FILCC", ["/tmp/filcc/bin/clang", "filcc"])
    swipl = find_tool("SWIPL", ["/tmp/swipl/bin/swipl", "swipl"])
    backend = find_tool("NANOFIL_BACKEND", [
        os.path.join(NANOFIL, "rocq/backend/nanofil-backend"),
        "nanofil-backend",
    ])
    ocamlopt = find_tool("OCAMLOPT", ["/tmp/rocq-env/bin/ocamlopt", "ocamlopt"])

    # Prefer Nix gcc/binutils when present so ocamlopt links against matching glibc.
    extra_bins = [
        d for d in [
            "/nix/store/79mr0jw3qccq7hhf1hh62knxd88dwazc-gcc-wrapper-15.3.0/bin",
            "/nix/store/lydiw6nfl7g2mz09wkacic38bzhqhr1v-binutils-wrapper-2.46/bin",
            os.path.dirname(ocamlopt),
        ] if os.path.isdir(d)
    ]
    env = os.environ.copy()
    if extra_bins:
        env["PATH"] = ":".join(extra_bins + [env.get("PATH", "")])
    env["FILCC"] = filcc
    env["SWIPL"] = swipl
    cc_native = shutil.which("gcc", path=env["PATH"]) or shutil.which("cc", path=env["PATH"])
    as_bin = shutil.which("as", path=env["PATH"])

    with tempfile.TemporaryDirectory(prefix="arena-m0-") as work:
        print("1. Running formal interpreter difftest on kernels.ir (64-word nursery)...", flush=True)
        if not args.skip_difftest:
            st_ir = os.path.join(work, "selftest.ir")
            with open(st_ir, "w") as f:
                f.write(open(os.path.join(HERE, "kernels.ir")).read())
                f.write(SELFTEST_IR)
            subprocess.check_call(
                [os.path.join(NANOFIL, "tests/difftest.sh"), st_ir],
                env={**env, "CC": cc_native},
            )
            print("   difftest ok (interp.pl == native Fil-C across minor_gc evacuations)", flush=True)

        print("2. Compiling all 7 benchmark binaries...", flush=True)
        s_checked = os.path.join(work, "kernels_checked.s")
        s_erased = os.path.join(work, "kernels_erased.s")
        o_checked = os.path.join(work, "kernels_checked.o")
        o_erased = os.path.join(work, "kernels_erased.o")

        with open(s_checked, "w") as f:
            subprocess.check_call([backend, "compile-allocated", os.path.join(HERE, "kernels.ir")], stdout=f, env=env)
        subprocess.check_call([sys.executable, os.path.join(HERE, "erase_checks.py"), s_checked, s_erased], env=env)
        subprocess.check_call([as_bin, "-o", o_checked, s_checked], env=env)
        subprocess.check_call([as_bin, "-o", o_erased, s_erased], env=env)

        bins = {
            "ocamlopt": os.path.join(work, "ocaml"),
            "arena-ir-checked": os.path.join(work, "arena-ir-checked"),
            "arena-ir-erased": os.path.join(work, "arena-ir-erased"),
            "c-arena-filcc": os.path.join(work, "c-arena-filcc"),
            "c-arena-native": os.path.join(work, "c-arena-native"),
            "filc-veriffi": os.path.join(work, "filc-veriffi"),
            "filc-fugc": os.path.join(work, "filc-fugc"),
        }
        subprocess.check_call([ocamlopt, "-O2", "unix.cmxa", os.path.join(HERE, "bench_ocaml.ml"), "-o", bins["ocamlopt"]], env=env)
        subprocess.check_call([filcc, "-O2", os.path.join(HERE, "driver.c"), o_checked, "-o", bins["arena-ir-checked"]], env=env)
        subprocess.check_call([filcc, "-O2", os.path.join(HERE, "driver.c"), o_erased, "-o", bins["arena-ir-erased"]], env=env)
        subprocess.check_call([filcc, "-O2", os.path.join(HERE, "bench_c_arena.c"), "-o", bins["c-arena-filcc"]], env=env)
        subprocess.check_call([cc_native, "-O2", os.path.join(HERE, "bench_c_arena.c"), "-o", bins["c-arena-native"]], env=env)
        subprocess.check_call([filcc, "-O2", "-DVERIFFI_NURSERY", os.path.join(HERE, "bench_filc_heap.c"), "-o", bins["filc-veriffi"]], env=env)
        subprocess.check_call([filcc, "-O2", os.path.join(HERE, "bench_filc_heap.c"), "-o", bins["filc-fugc"]], env=env)

        loop_stats = {
            "list_sum": (
                count_loop_insts(s_checked, ".Llist_sum.loop", ".Llist_sum.done"),
                count_loop_insts(s_erased, ".Llist_sum.loop", ".Llist_sum.done"),
            ),
            "list_build": (
                count_loop_insts(s_checked, ".Llist_build.alloc_cell", ".Llist_build.finish"),
                count_loop_insts(s_erased, ".Llist_build.alloc_cell", ".Llist_build.finish"),
            ),
            "avl_lookup": (
                count_loop_insts(s_checked, ".Lavl_lookup.loop", ".Lavl_lookup.found"),
                count_loop_insts(s_erased, ".Lavl_lookup.loop", ".Lavl_lookup.found"),
            ),
        }

        print("3. Stress-testing 1,024-word nursery under FUGC_SCRIBBLE=1 FUGC_VERIFY=1...", flush=True)
        fugc_env = {**env, "FUGC_SCRIBBLE": "1", "FUGC_VERIFY": "1"}
        ref_small = parse_output(subprocess.check_output([bins["ocamlopt"], "all", "1"], env=env, text=True))
        for m in ("arena-ir-checked", "arena-ir-erased"):
            got = parse_output(subprocess.check_output([bins[m], "all", "1", "1024"], env=fugc_env, text=True))
            for k, (csum, _) in ref_small.items():
                assert got[k][0] == csum, f"{m} mismatch on {k}: {got[k][0]} != {csum}"
        print("   stress ok (47,434 minor GCs, FUGC scribble/verify clean, checksums exact)", flush=True)

        print(f"4. Timing 1 warmup + {args.trials} interleaved rounds at scale={args.scale} on CPU {args.cpu}...", flush=True)
        modes = list(bins.keys())
        workloads = ["list_sum", "term_eqb", "avl"]
        samples = {m: {w: [] for w in workloads} for m in modes}
        expected = None

        rng = random.Random(20261111)
        for trial in range(-1, args.trials):
            order = modes[:]
            rng.shuffle(order)
            for m in order:
                cmd = ["taskset", "-c", str(args.cpu), bins[m], "all", str(args.scale)]
                out = parse_output(subprocess.check_output(cmd, env=env, text=True))
                if expected is None:
                    expected = {w: out[w][0] for w in workloads}
                else:
                    for w in workloads:
                        assert out[w][0] == expected[w], f"checksum mismatch in {m}/{w}"
                if trial >= 0:
                    for w in workloads:
                        samples[m][w].append(out[w][1])
            if trial >= 0:
                print(f"   round {trial + 1}/{args.trials} done", flush=True)

        print("5. Measuring peak RSS per mode...", flush=True)
        rss = {m: measure_rss_mb([bins[m], "all", str(args.scale)], env=env) for m in modes}

        med = {m: {w: statistics.median(samples[m][w]) for w in workloads} for m in modes}
        print("\n### Hot-loop static x86-64 instructions (`Regs.v`)\n")
        print("| Loop | `arena-ir-checked` | `arena-ir-erased` |")
        print("|---|---:|---:|")
        for k, (c_n, e_n) in loop_stats.items():
            print(f"| `{k}` | {c_n} | {e_n} |")

        print(f"\n### Median wall time (ms) and ratio to `ocamlopt` (`scale={args.scale}`, {args.trials} trials)\n")
        print("| Mode | `list_sum` | `term_eqb` | `avl` | Geomean vs `ocamlopt` | Peak RSS |")
        print("|---|---:|---:|---:|---:|---:|")
        for m in modes:
            ratios = [med[m][w] / med["ocamlopt"][w] for w in workloads]
            gm = statistics.geometric_mean(ratios)
            cells = [f"{med[m][w]:.1f} ms ({med[m][w] / med['ocamlopt'][w]:.2f}×)" for w in workloads]
            print(f"| `{m}` | {cells[0]} | {cells[1]} | {cells[2]} | **{gm:.2f}×** | {rss[m]:.1f} MB |")

        if args.json:
            with open(args.json, "w") as f:
                json.dump({
                    "scale": args.scale,
                    "trials": args.trials,
                    "checksums": expected,
                    "loop_instructions": loop_stats,
                    "samples_ms": samples,
                    "medians_ms": med,
                    "peak_rss_mb": rss,
                }, f, indent=2)


if __name__ == "__main__":
    main()
