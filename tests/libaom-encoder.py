"""Lossless multi-frame encode/decode checks using installed Fil-C libaom apps."""

import pathlib
import struct
import subprocess
import sys

bin_dir = pathlib.Path(sys.argv[1])
width, height, frames = 64, 48, 3
for bits in (8, 10, 12):
    raw = bytearray()
    chroma = "420jpeg" if bits == 8 else f"420p{bits}"
    y4m = bytearray(
        f"YUV4MPEG2 W{width} H{height} F30:1 Ip A1:1 C{chroma}\n".encode()
    )
    for frame in range(frames):
        pixels = bytearray()
        for plane in range(3):
            w, h = (width, height) if plane == 0 else (width // 2, height // 2)
            for y in range(h):
                for x in range(w):
                    value = (13 * x + 7 * y + 97 * frame + 211 * plane) % (1 << bits)
                    pixels.extend(bytes([value]) if bits == 8 else struct.pack("<H", value))
        raw.extend(pixels)
        y4m.extend(b"FRAME\n" + pixels)
    input_file = pathlib.Path(f"input-{bits}.y4m")
    input_file.write_bytes(y4m)
    # Good-quality lookahead and realtime partitioning take different paths.
    for usage, speed, lag in ((0, 6, 8), (1, 8, 0)):
        stream = f"stream-{bits}-{usage}.ivf"
        output = pathlib.Path(f"decoded-{bits}-{usage}.yuv")
        subprocess.run(
            [str(bin_dir / "aomenc"), "--codec=av1", "--passes=1", "--threads=2",
             f"--usage={usage}", f"--cpu-used={speed}", f"--lag-in-frames={lag}",
             "--lossless=1", f"--bit-depth={bits}", f"--input-bit-depth={bits}",
             "--ivf", "-o", stream, str(input_file)],
            check=True,
        )
        subprocess.run(
            [str(bin_dir / "aomdec"), "--codec=av1", "--rawvideo",
             f"--output-bit-depth={bits}", "-o", str(output), stream],
            check=True,
        )
        assert output.read_bytes() == raw, f"{bits}-bit usage={usage}: decoded pixels differ"
        print(f"libaom {bits}-bit usage={usage}: all Y/U/V samples in {frames} frames verified", flush=True)
