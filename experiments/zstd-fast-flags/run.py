#!/usr/bin/env python3
"""Alternate CPU-pinned zstd variants and retain all benchmark output."""
import argparse
import hashlib
import json
import pathlib
import re
import statistics
import subprocess


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("work", type=pathlib.Path)
    p.add_argument("--cpu", default="2")
    p.add_argument("--rounds", type=int, default=5)
    args = p.parse_args()
    args.work.mkdir(parents=True, exist_ok=True)
    expr = pathlib.Path(__file__).with_name("default.nix")

    def build(attr):
        return subprocess.check_output([
            "nix", "build", "--impure", "-f", str(expr), attr,
            "--no-link", "--print-out-paths",
        ], text=True).strip()

    paths = {name: build(attr) for name, attr in (
        ("before", "before.bin"), ("after", "after.bin"),
        ("yolo", "yolo.bin"), ("c", "base.bin"),
    )}
    src = pathlib.Path(subprocess.check_output([
        "nix", "eval", "--impure", "--raw", "-f", str(expr), "base.src.outPath",
    ], text=True))
    # The earlier fixture's exact LCG, repeated for a 4 MiB CLI workload.
    r = 42
    alphabet = bytearray()
    for _ in range(1 << 20):
        r = (r * 1664525 + 1013904223) & 0xffffffff
        alphabet.append(r >> 28)
    corpora = {"alphabet16": bytes(alphabet) * 4,
               "zstd-source": b"".join(f.read_bytes() for f in sorted(src.rglob("*"))
                                        if f.suffix in (".c", ".h"))}
    metadata = {"binaries": paths, "cpu": args.cpu, "rounds": args.rounds,
                "corpora": {}}
    for name, data in corpora.items():
        (args.work / name).write_bytes(data)
        metadata["corpora"][name] = {
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    (args.work / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    rows = []
    # Rotations reduce systematic order bias; each timed process is
    # single-threaded and runs compression and decompression for >=1 s each.
    variants = list(paths)
    with (args.work / "raw.log").open("w") as raw:
        for trial in range(args.rounds):
            for corpus in corpora:
                for level in (1, 3, 9):
                    order = variants[trial % 4:] + variants[:trial % 4]
                    for variant in order:
                        cmd = ["taskset", "-c", args.cpu, paths[variant] + "/bin/zstd",
                               "-b" + str(level), "-i1", "-q", str(args.work / corpus)]
                        print(f"round={trial + 1} corpus={corpus} level={level} {variant}",
                              flush=True)
                        result = subprocess.run(cmd, text=True, stdout=subprocess.PIPE,
                                                stderr=subprocess.STDOUT, check=True)
                        raw.write(json.dumps(cmd) + "\n" + result.stdout + "\n")
                        raw.flush()
                        # Quiet mode emits both final best-of-inner-loop rates.
                        rates = re.findall(r"([0-9.]+) MB/s\s+([0-9.]+) MB/s", result.stdout)
                        if not rates:
                            raise RuntimeError(result.stdout)
                        compression, decompression = map(float, rates[-1])
                        rows.append(dict(trial=trial + 1, corpus=corpus, level=level,
                                         variant=variant, compression=compression,
                                         decompression=decompression))
                        (args.work / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
    print("corpus,level,variant,compression_MBps,decompression_MBps,comp_range_pct,decomp_range_pct")
    for corpus in corpora:
        for level in (1, 3, 9):
            for variant in variants:
                group = [row for row in rows if (row["corpus"], row["level"], row["variant"])
                         == (corpus, level, variant)]
                values = [[row[key] for row in group]
                          for key in ("compression", "decompression")]
                medians = [statistics.median(v) for v in values]
                ranges = [(max(v) - min(v)) / m * 100 for v, m in zip(values, medians)]
                print(",".join(map(str, [corpus, level, variant] + medians + ranges)))


if __name__ == "__main__":
    main()
