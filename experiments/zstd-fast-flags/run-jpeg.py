#!/usr/bin/env python3
"""Spot-benchmark the existing libjpeg-turbo SaRCAsm experiment."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import statistics
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("work", type=pathlib.Path, help="build-jpeg.sh output directory")
p.add_argument("--cpu", default="2")
p.add_argument("--rounds", type=int, default=5)
args = p.parse_args()
width = height = 2048
metadata = {"width": width, "height": height, "cpu": args.cpu, "images": {}}
for kind in ("smooth", "textured"):
    r = 42
    pixels = bytearray()
    for y in range(height):
        for x in range(width):
            noise = 0
            if kind == "textured":
                r = (r * 1664525 + 1013904223) & 0xffffffff
                noise = (r >> 24) // 2
            pixels.extend(((x // 8 + y // 16 + noise) % 256,
                           (x // 16 + y // 8 + noise) % 256,
                           (x // 12 + y // 12 + noise) % 256))
    image = f"P6\n{width} {height}\n255\n".encode() + pixels
    (args.work / f"{kind}.ppm").write_bytes(image)
    metadata["images"][kind] = hashlib.sha256(image).hexdigest()
    # Verify encoded bytes and decoded pixels are unchanged across assemblers.
    encoded = []
    decoded = []
    for variant in ("before", "after"):
        jpeg = subprocess.check_output([
            str(args.work / variant / "cjpeg"), "-quality", "90", "-sample", "2x2",
            str(args.work / f"{kind}.ppm")])
        ppm = subprocess.check_output([str(args.work / variant / "djpeg")], input=jpeg)
        encoded.append(jpeg)
        decoded.append(ppm)
    assert encoded[0] == encoded[1], "encoded JPEG changed"
    assert decoded[0] == decoded[1], "decoded pixels changed"
(args.work / "bench-metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
rows = []
with (args.work / "bench-raw.log").open("w") as raw:
    variants = ["before", "after", "c"]
    for trial in range(args.rounds):
        for image in metadata["images"]:
            order = variants[trial % 3:] + variants[:trial % 3]
            for variant in order:
                build = "after" if variant == "c" else variant
                env = os.environ.copy()
                if variant == "c":
                    env["JSIMD_FORCENONE"] = "1"
                cmd = ["taskset", "-c", args.cpu, str(args.work / build / "tjbench"),
                       str(args.work / f"{image}.ppm"), "90", "-subsamp", "420",
                       "-rgb", "-benchtime", "2", "-warmup", "0.2", "-nowrite"]
                print(trial + 1, image, variant, flush=True)
                result = subprocess.check_output(cmd, env=env, text=True, stderr=subprocess.STDOUT)
                raw.write(json.dumps(cmd) + f" JSIMD_FORCENONE={env.get('JSIMD_FORCENONE', '')}\n"
                          + result + "\n")
                raw.flush()
                values = re.findall(r"Throughput:\s+([0-9.]+) Megapixels/sec", result)
                assert len(values) == 2, result
                rows.append(dict(trial=trial + 1, image=image, variant=variant,
                                 compression=float(values[0]), decompression=float(values[1])))
                (args.work / "bench-results.json").write_text(json.dumps(rows, indent=2) + "\n")
for image in metadata["images"]:
    for variant in variants:
        group = [r for r in rows if (r["image"], r["variant"]) == (image, variant)]
        values = [[r[key] for r in group] for key in ("compression", "decompression")]
        medians = [statistics.median(v) for v in values]
        ranges = [(max(v) - min(v)) / m * 100 for v, m in zip(values, medians)]
        print(image, variant, *medians, "range_pct", *ranges)
