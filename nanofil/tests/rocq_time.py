#!/usr/bin/env python3
"""Report source-located warnings for Rocq -time sentences over five seconds."""
import argparse
from decimal import Decimal
from pathlib import Path
import re


# Rocq 9.1.1: Chars 9 - 50 [From~Corelib~Require~Import~In...] 0.003 secs (0.003u,0.s)
# Chars are UTF-8 byte offsets, not Python string indices. Ignore other output,
# including watchdog progress lines that may quote a previous timing record.
TIMING = re.compile(r"^Chars (\d+) - (\d+) \[.*\] (\d+(?:\.\d*)?) secs \(")
LOADING = re.compile(rb"^(?:From\s+\S+\s+)?Require\b|^Load\b")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("log", type=Path)
    args = parser.parse_args()
    source = args.source.read_bytes()
    with args.log.open(errors="replace") as log:
        for line in log:
            match = TIMING.match(line)
            if not match or Decimal(match[3]) <= Decimal(5):
                continue
            start, end = int(match[1]), int(match[2])
            prefix = source[:start]
            row = prefix.count(b"\n") + 1
            column = len(prefix.rsplit(b"\n", 1)[-1].decode("utf-8", errors="replace")) + 1
            # Non-loading commands include tactics, Qed and other vernacular;
            # do not pretend this inexpensive split is a proof profiler.
            kind = "module loading" if LOADING.match(source[start:end]) else "proof/vernacular"
            print(f"{args.source}:{row}:{column}: warning: Rocq sentence took "
                  f"{match[3]}s (>5s; {kind}; bytes {start}-{end})")


if __name__ == "__main__":
    main()
