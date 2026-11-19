#!/usr/bin/env python3
"""Check and report the structural architecture of nanofil/rocq/glibc/.

Reads a declarative, editable layer manifest (default: nanofil/rocq/glibc/arch.json)
and verifies five pragmatic invariants across the Rocq tree:

  1. Layer DAG: cross-directory Glibc imports follow the manifest's layer map,
     sibling applications stay isolated, and L0 stays free of Iris/Fix/zsys.
  2. Single-instantiation functors: `Module X := ...On ...` lives only in Fix*.v.
  3. Tactic locality: non-Local `Ltac` / `Tactic Notation` definitions live only
     in `*Tactics.v` or designated proof-infrastructure modules.
  4. Import hygiene: no duplicate `Require`s, explicit `Require Export` list,
     and tracking of direct Glibc imports with zero symbol reference.
  5. Dependency depth: reports per-directory max depth and critical-path depth.

By default, compares against the ratcheted `baseline` in arch.json so existing
campaign debt cannot grow while each refactoring phase tightens the ratchet.
"""
import argparse
import collections
import json
import re
import sys
import time
from pathlib import Path

DEFAULT_TREE = Path(__file__).resolve().parent.parent / "rocq" / "glibc"
DEFAULT_MANIFEST = DEFAULT_TREE / "arch.json"

REQ_STMT_RE = re.compile(
    r"(?:From\s+([\w.]+)\s+)?Require\s+(?:(Import|Export)\s+)?([^.]+)\.",
    re.MULTILINE,
)
IMP_STMT_RE = re.compile(r"(?:^|\n)\s*(?:Import|Export)\s+[^.]+\.", re.MULTILINE)
IDENT_RE = re.compile(r"[A-Za-z_][\w']*")
FUNCTOR_APP_RE = re.compile(
    r"^\s*Module\s+(?:(?:Import|Export)\s+)?([A-Za-z_][\w']*)\s*(?::[^:=]+)?\s*:=\s*([A-Za-z_][\w'.]*On)\b",
    re.MULTILINE,
)
NONLOCAL_TACTIC_RE = re.compile(
    r"^(?!\s*(?:Local|#\[local\]))\s*(?:#\[[^\]]*\]\s*)?(?:Global\s+|Export\s+)?(?:Ltac\s+([A-Za-z_][\w']*)|Tactic\s+Notation\s+\"([^\"]+)\")",
    re.MULTILINE,
)
EXPORTED_DECL_RE = re.compile(
    r"^(?!\s*(?:Local|#\[local\]))\s*(?:#\[[^\]]*\]\s*)?(?:Global\s+|Export\s+)?"
    r"(?:Definition|Lemma|Theorem|Corollary|Proposition|Fact|Remark|Fixpoint|CoFixpoint|"
    r"Inductive|CoInductive|Record|Structure|Class|Instance|Ltac|Abbreviation|Module(?:\s+Type)?)"
    r"\s+([A-Za-z_][\w']*)",
    re.MULTILINE,
)
TACTIC_NOT_RE = re.compile(
    r"^(?!\s*(?:Local|#\[local\]))\s*(?:#\[[^\]]*\]\s*)?(?:Global\s+|Export\s+)?Tactic\s+Notation\s+\"([^\"]+)\"",
    re.MULTILINE,
)


LEX_TOKEN_RE = re.compile(r'\(\*|\*\)|"(?:""|[^"])*"')


def _strip_comments(text, keep_strings):
    """Remove nested (* ... *) comments, optionally replacing string contents with spaces."""
    out = []
    pos = 0
    depth = 0
    for m in LEX_TOKEN_RE.finditer(text):
        tok = m.group(0)
        start, end = m.span()
        if depth == 0:
            if tok == "(*":
                out.append(text[pos:start])
                depth = 1
                pos = end
            elif tok == "*)":
                out.append(text[pos:end])
                pos = end
            else:
                out.append(text[pos:start])
                if keep_strings:
                    out.append(tok)
                else:
                    out.append('"' + ("\n" * tok.count("\n")) + '"')
                pos = end
        else:
            if tok == "(*":
                depth += 1
            elif tok == "*)":
                depth -= 1
                if depth == 0:
                    out.append("\n" * text[pos:end].count("\n"))
                    pos = end
    if depth:
        raise ValueError("unterminated Rocq comment")
    out.append(text[pos:])
    return "".join(out)


def strip_comments_and_strings(text):
    return _strip_comments(text, keep_strings=False)


def strip_comments_keep_strings(text):
    return _strip_comments(text, keep_strings=True)


def top_dir(path, tree):
    rel = path.relative_to(tree)
    return rel.parts[0] if len(rel.parts) > 1 else "."


def module_layer(mod, subdir, manifest):
    for lname, cfg in manifest["layers"].items():
        if mod in cfg.get("files", ()):
            return lname
    for lname, cfg in manifest["layers"].items():
        if subdir in cfg.get("dirs", ()):
            return lname
    return None


def extract_exported_symbols(code_with_strings):
    syms = set()
    for m in EXPORTED_DECL_RE.finditer(code_with_strings):
        syms.add(m.group(1))
    for m in TACTIC_NOT_RE.finditer(code_with_strings):
        for w in IDENT_RE.findall(m.group(1)):
            syms.add(w)
    for m in re.finditer(r"\bRecord\b[^{]+\{([^}]+)\}", code_with_strings, re.DOTALL):
        for fm in re.finditer(r"\b([A-Za-z_][\w']*)\s*:", m.group(1)):
            syms.add(fm.group(1))
    for m in re.finditer(r"\bInductive\b[^.]+\.", code_with_strings, re.DOTALL):
        for cm in re.finditer(r"\|\s*([A-Za-z_][\w']*)\b", m.group(0)):
            syms.add(cm.group(1))
    return syms


def analyze(tree, manifest):
    tree = Path(tree).resolve()
    files = {}
    for p in sorted(tree.rglob("*.v")):
        files[p.stem] = p

    dirs = {m: top_dir(p, tree) for m, p in files.items()}
    layers = {m: module_layer(m, dirs[m], manifest) for m, p in files.items()}

    unknown_dirs = sorted({dirs[m] for m in files if layers[m] is None})

    direct_glibc = {}
    direct_ext = {}
    reexported_glibc = collections.defaultdict(set)
    exported_syms = {}
    body_tokens = {}

    duplicate_require_files = []
    unapproved_require_exports = []
    functor_apps = []
    exported_tactics = []
    l0_violations = []

    allowed_functors = set(manifest.get("functor_instantiation_modules", ()))
    allowed_tac_dirs = set(manifest.get("tactic_export_dirs", ()))
    allowed_tac_suffixes = tuple(manifest.get("tactic_export_module_suffixes", ()))
    allowed_tac_mods = set(manifest.get("tactic_export_modules", ()))
    allowed_req_exports = set(manifest.get("require_export_modules", ()))

    for mod, path in sorted(files.items()):
        raw = path.read_text()
        code_s = strip_comments_keep_strings(raw)
        code = strip_comments_and_strings(raw)

        gdeps = set()
        edeps = set()
        seen_glibc = collections.Counter()
        has_req_export = False

        for m in REQ_STMT_RE.finditer(code):
            prefix, kind, body = m.group(1), m.group(2), m.group(3)
            tokens = [t for t in body.split() if t and not t.startswith("-")]
            if kind == "Export":
                has_req_export = True
            for tok in tokens:
                short = tok.split(".")[-1]
                if prefix == "Glibc" or (prefix is None and short in files):
                    if short in files:
                        gdeps.add(short)
                        seen_glibc[short] += 1
                        if kind == "Export":
                            reexported_glibc[mod].add(short)
                else:
                    edeps.add((prefix or "", tok))

        direct_glibc[mod] = gdeps
        direct_ext[mod] = edeps

        dups = sorted(k for k, v in seen_glibc.items() if v > 1)
        if dups:
            duplicate_require_files.append((mod, dirs[mod], dups))

        if has_req_export and mod not in allowed_req_exports:
            unapproved_require_exports.append((mod, dirs[mod]))

        if mod not in allowed_functors:
            for m in FUNCTOR_APP_RE.finditer(code):
                functor_apps.append((mod, dirs[mod], m.group(1), m.group(2)))

        can_export_tactics = (
            dirs[mod] in allowed_tac_dirs
            or mod in allowed_tac_mods
            or any(mod.endswith(suf) for suf in allowed_tac_suffixes)
        )
        if not can_export_tactics:
            for m in NONLOCAL_TACTIC_RE.finditer(code_s):
                tname = m.group(1) or f'"{m.group(2)}"'
                exported_tactics.append((mod, dirs[mod], tname))

        # L0 purity checks
        if layers[mod] == "L0":
            l0_cfg = manifest["layers"]["L0"]
            forbid_prefixes = tuple(l0_cfg.get("forbid_external_prefixes", ()))
            forbid_mods = set(l0_cfg.get("forbid_modules", ()))
            for pre, tok in sorted(edeps):
                full = f"{pre}.{tok}" if pre else tok
                if any(full.startswith(fp) for fp in forbid_prefixes):
                    l0_violations.append((mod, full))
            for g in sorted(gdeps):
                if g in forbid_mods:
                    l0_violations.append((mod, g))

        exported_syms[mod] = extract_exported_symbols(code_s)
        body = IMP_STMT_RE.sub(" ", REQ_STMT_RE.sub(" ", code))
        body_tokens[mod] = set(IDENT_RE.findall(body))

    # Propagate symbols through Require Export (fixed point)
    effective_syms = {m: set(s) for m, s in exported_syms.items()}
    changed = True
    while changed:
        changed = False
        for m, reexps in reexported_glibc.items():
            for sub in reexps:
                before = len(effective_syms[m])
                effective_syms[m].update(effective_syms.get(sub, ()))
                effective_syms[m].add(sub)
                if len(effective_syms[m]) > before:
                    changed = True

    # Layer DAG violations
    layer_edge_counts = collections.Counter()
    layer_edge_examples = collections.defaultdict(list)
    for u, vs in sorted(direct_glibc.items()):
        lu = layers[u]
        du = dirs[u]
        if lu is None:
            continue
        cfg = manifest["layers"][lu]
        allowed_layers = set(cfg.get("may_import_layers", (lu,)))
        isolate_siblings = cfg.get("isolate_siblings", False)
        for v in sorted(vs):
            lv = layers[v]
            dv = dirs[v]
            if lv is None:
                continue
            ok = False
            if lv in allowed_layers:
                ok = True
            elif lu == lv and (not isolate_siblings or du == dv):
                ok = True
            if not ok:
                key = f"{du} -> {dv}"
                layer_edge_counts[key] += 1
                if len(layer_edge_examples[key]) < 5:
                    layer_edge_examples[key].append(f"{u}->{v}")

    # Unused direct Glibc edges (zero exported symbol or module-name match)
    unused_by_dir = collections.Counter()
    total_edges = 0
    for u, vs in direct_glibc.items():
        toks = body_tokens[u]
        du = dirs[u]
        for v in vs:
            total_edges += 1
            if v not in toks and not (effective_syms[v] & toks):
                unused_by_dir[du] += 1

    # Dependency depths (per directory and critical targets)
    def longest_path(graph, restrict=None):
        memo = {}

        def lp(node):
            if node in memo:
                return memo[node]
            best = (1, [node])
            for dep in graph.get(node, ()):
                if restrict is not None and dep not in restrict:
                    continue
                l, p = lp(dep)
                if l + 1 > best[0]:
                    best = (l + 1, p + [node])
            memo[node] = best
            return best

        return lp

    dir_depths = {}
    for d in sorted(set(dirs.values())):
        sub = {m for m, md in dirs.items() if md == d}
        lp = longest_path(direct_glibc, restrict=sub)
        best_l, best_p = max((lp(m) for m in sub), key=lambda x: x[0])
        dir_depths[d] = (best_l, len(sub), best_p[-1])

    target_depths = {}
    lp_all = longest_path(direct_glibc)
    for tgt in manifest.get("critical_path_targets", ()):
        if tgt in files:
            l, path = lp_all(tgt)
            target_depths[tgt] = (l, path)

    return {
        "file_count": len(files),
        "total_edges": total_edges,
        "unknown_dirs": unknown_dirs,
        "l0_violations": l0_violations,
        "layer_edges": dict(sorted(layer_edge_counts.items())),
        "layer_edge_examples": dict(layer_edge_examples),
        "functor_apps": functor_apps,
        "exported_tactics": exported_tactics,
        "duplicate_require_files": duplicate_require_files,
        "unapproved_require_exports": unapproved_require_exports,
        "unused_by_dir": dict(sorted(unused_by_dir.items())),
        "unused_total": sum(unused_by_dir.values()),
        "dir_depths": dir_depths,
        "target_depths": target_depths,
    }


def make_baseline(res):
    return {
        "layer_edges": res["layer_edges"],
        "functor_apps": len(res["functor_apps"]),
        "exported_tactics": len(res["exported_tactics"]),
        "duplicate_require_files": len(res["duplicate_require_files"]),
        "unused_edges": res["unused_total"],
    }


def compare_against_baseline(res, baseline, strict=False):
    failures = []
    improvements = []

    if res["unknown_dirs"]:
        failures.append(f"unmapped directories not in arch.json: {res['unknown_dirs']}")
    if res["l0_violations"]:
        failures.append(f"L0 purity violations ({len(res['l0_violations'])}): {res['l0_violations'][:5]}")
    if res["unapproved_require_exports"]:
        failures.append(
            f"unlisted Require Export ({len(res['unapproved_require_exports'])}): "
            f"{res['unapproved_require_exports'][:5]}"
        )

    base_edges = {} if strict else baseline.get("layer_edges", {})
    for edge, count in sorted(res["layer_edges"].items()):
        allowed = base_edges.get(edge, 0)
        if count > allowed:
            exs = ", ".join(res["layer_edge_examples"].get(edge, [])[:3])
            failures.append(f"layer violation {edge}: {count} > baseline {allowed} (e.g. {exs})")
        elif not strict and count < allowed:
            improvements.append(f"layer {edge}: {count} (was {allowed})")
    if not strict:
        for edge, allowed in sorted(base_edges.items()):
            if edge not in res["layer_edges"] and allowed > 0:
                improvements.append(f"layer {edge}: 0 (was {allowed})")

    scalars = [
        ("functor_apps", len(res["functor_apps"]), "functor instantiations outside Fix*.v"),
        ("exported_tactics", len(res["exported_tactics"]), "exported tactics outside *Tactics.v"),
        ("duplicate_require_files", len(res["duplicate_require_files"]), "files with duplicate Require"),
        ("unused_edges", res["unused_total"], "zero-symbol-match direct Glibc imports"),
    ]
    for key, actual, label in scalars:
        allowed = 0 if strict else baseline.get(key, 0)
        if actual > allowed:
            failures.append(f"{label}: {actual} > baseline {allowed}")
        elif not strict and actual < allowed:
            improvements.append(f"{label}: {actual} (was {allowed})")

    return failures, improvements


def print_report(res, manifest):
    print(f"Scanned {res['file_count']} files ({res['total_edges']} direct Glibc edges)\n")
    print(f"Layer violations ({sum(res['layer_edges'].values())} edges across {len(res['layer_edges'])} pairs):")
    for edge, count in sorted(res["layer_edges"].items(), key=lambda kv: (-kv[1], kv[0])):
        exs = ", ".join(res["layer_edge_examples"][edge][:3])
        print(f"  {edge:24s} {count:4d}   ({exs})")

    print(f"\nFunctor instantiations outside Fix*.v ({len(res['functor_apps'])}):")
    by_functor = collections.Counter(f for _, _, _, f in res["functor_apps"])
    for fname, cnt in by_functor.most_common():
        print(f"  {fname:30s} {cnt:3d}")

    print(f"\nExported tactics outside *Tactics.v ({len(res['exported_tactics'])}):")
    by_dir = collections.Counter(d for _, d, _ in res["exported_tactics"])
    for d, cnt in by_dir.most_common():
        print(f"  {d:14s} {cnt:4d}")
    top_files = collections.Counter((d, m) for m, d, _ in res["exported_tactics"]).most_common(10)
    print("  Top files:", ", ".join(f"{d}/{m}({c})" for (d, m), c in top_files))

    print(f"\nImport hygiene:")
    print(f"  Duplicate Require files: {len(res['duplicate_require_files'])}")
    print(f"  Zero-symbol-match edges: {res['unused_total']} / {res['total_edges']} ({100*res['unused_total']/max(1,res['total_edges']):.1f}%)")
    for d, cnt in sorted(res["unused_by_dir"].items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"    {d:14s} {cnt:4d}")

    print("\nIntra-directory max dependency depth:")
    for d, (depth, count, top) in sorted(res["dir_depths"].items(), key=lambda kv: (-kv[1][0], kv[0])):
        print(f"  {d:14s} depth {depth:2d} / {count:3d} files  (top: {top})")

    for tgt, (depth, path) in res["target_depths"].items():
        print(f"\nCritical-path depth to {tgt}: {depth} files")


def main(argv=None):
    t0 = time.monotonic()
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tree", type=Path, default=DEFAULT_TREE)
    ap.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    ap.add_argument("--report", action="store_true", help="Print full breakdown of current structural debt")
    ap.add_argument("--strict", action="store_true", help="Ignore baseline ratchet and require zero violations")
    ap.add_argument("--update-baseline", action="store_true", help="Write current counts into manifest baseline")
    args = ap.parse_args(argv)

    manifest = json.loads(args.manifest.read_text())
    res = analyze(args.tree, manifest)

    if args.update_baseline:
        manifest["baseline"] = make_baseline(res)
        args.manifest.write_text(json.dumps(manifest, indent=2) + "\n")
        print(f"Updated baseline in {args.manifest}", file=sys.stderr)
        print_report(res, manifest)
        return 0

    if args.report:
        print_report(res, manifest)
        return 0

    failures, improvements = compare_against_baseline(res, manifest.get("baseline", {}), strict=args.strict)
    elapsed = time.monotonic() - t0
    if failures:
        print("Architecture tripwire fired (fix the tangle or intentionally revise arch.json):", file=sys.stderr)
        for f in failures:
            print(f"  FAIL: {f}", file=sys.stderr)
        print(f"{res['file_count']} files checked in {elapsed:.2f}s; {len(failures)} failure(s)", file=sys.stderr)
        return 1

    depth_summary = ", ".join(f"{t}={d}" for t, (d, _) in res["target_depths"].items())
    print(
        f"proof_arch_check: ok ({res['file_count']} files, {sum(res['layer_edges'].values())} baselined layer edges, "
        f"{len(res['functor_apps'])} functors, {len(res['exported_tactics'])} exported tactics, "
        f"{len(res['duplicate_require_files'])} dup-req, {res['unused_total']} unused edges; "
        f"depth {depth_summary}; {elapsed:.2f}s)"
    )
    if improvements:
        print("Improvements below baseline (run --update-baseline to tighten):")
        for imp in improvements:
            print(f"  IMPROVED: {imp}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
