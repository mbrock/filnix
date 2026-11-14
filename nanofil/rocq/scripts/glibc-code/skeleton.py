#!/usr/bin/env python3
"""Print block-lemma statement skeletons from a manifest's linked IR."""
import argparse
import json
from pathlib import Path
import runpy
import tempfile
import tomllib

HERE = Path(__file__).resolve().parent
generator = runpy.run_path(str(HERE / "generate.py"))


def atom(name):
    if not all(32 <= ord(c) <= 126 for c in name):
        raise ValueError(f"skeleton requires a printable ASCII name: {name!r}")
    return 'TAtom "' + name.replace('"', '""') + '"'


def names(ns):
    return "[" + "; ".join(atom(n) for n in ns) + "]"


def entry_line(function, label, predecessor, expr_type):
    origin = "None" if predecessor is None else f"(Some ({atom(predecessor)}))"
    return (f"WP (ERun (mkFrame {function} e [] None (Enter ({atom(label)}) {origin}))"
            f" : {expr_type}) {{{{ Φ }}}}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("unit", help="manifest directory/fixture row, e.g. getopt/Getopt")
    parser.add_argument("function", help="exact linked IR symbol, including its object prefix")
    parser.add_argument("--capture", type=Path, default=Path("/tmp/glibc-pp"))
    parser.add_argument("--rocq-function", default="F", help="decoded func expression (default: F)")
    parser.add_argument("--expr-type", default="gexpr", help="local expression notation (default: gexpr)")
    parser.add_argument("--json", action="store_true", help="print block data and entry lines as JSON")
    args = parser.parse_args()
    unit = Path(args.unit)
    manifest = generator["GLIBC"] / unit.parent / "code.toml"
    config = tomllib.loads(manifest.read_text())
    matches = []
    for cfg in [config, *config.get("batch", [])]:
        for row in generator["rows"](cfg["fixtures"]):
            fields = row.split("|")
            if len(fields) not in (4, 5):
                parser.error(f"invalid fixture row: {row}")
            if fields[0] == unit.name:
                matches.append((cfg, fields))
    if len(matches) != 1:
        parser.error(f"expected one manifest row for {args.unit}, found {len(matches)}")
    cfg, (name, roots, paths, _, *program) = matches[0]
    if not args.capture.is_dir():
        parser.error("build survey/glibc/capture.nix and pass its path with --capture")
    with tempfile.TemporaryDirectory(prefix="glibc-blocks-") as tmp:
        work = Path(tmp)
        gen = generator["Generator"](args.capture.resolve(), work)
        if cfg["layout"] in ("stdio", "buffer"):
            hashes = "buffer-fixtures.sha256" if cfg["layout"] == "buffer" else "fixtures.sha256"
            generator["run"](["sha256sum", "-c", manifest.parent / hashes], cwd=gen.capture)
        linked = gen.link(cfg, name, roots or cfg.get("roots", ""),
                          "- " + paths if paths else cfg.get("units", ""),
                          program[0] if program else "")
        term = work / "linked.term"
        term.write_text(linked)
        blocks = json.loads(generator["run"]([gen.swipl, HERE / "blocks.pl", term, args.function], env=gen.env))
    for block in blocks:
        for entry in block["entries"]:
            entry["wp"] = entry_line(args.rocq_function, block["label"], entry["predecessor"], args.expr_type)
    if args.json:
        print(json.dumps(blocks, indent=2))
        return
    print("(* Statement skeletons only. Supply the runtime/logic context, resources and continuation.")
    print("   Live-out includes new values; keeps preserves only the names this block never writes. *)")
    for i, block in enumerate(blocks, 1):
        print(f'\n(* Block {block["label"]}; predecessors: {", ".join(block["predecessors"]) or "none"}; '
              f'successors: {", ".join(block["successors"]) or "none"}. *)')
        print(f'(* Live-out: {names(block["live_out"])}. *)')
        print(f'(* Unchanged live-out: keeps {names(block["keeps"])} e e\'. *)')
        print(f'(* New live-out values need lookup facts in e\': {names(block["outputs"])}. *)')
        if not block["entries"]:
            print("(* Unreachable non-entry block without predecessors: no Enter statement. *)")
        for j, entry in enumerate(block["entries"], 1):
            values = "".join(f" x{k}" for k in range(len(entry["reads"])))
            print(f"Lemma wp_block_{i:03d}_from_{j:03d} e{values} Φ :")
            for k, n in enumerate(entry["reads"]):
                print(f"  lookup ({atom(n)}) e = Some x{k} ->")
            print("  (* Add resources and a continuation for the successors above. *)")
            print("  " + entry["wp"])


if __name__ == "__main__":
    main()
