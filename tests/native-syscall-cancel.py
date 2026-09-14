#!/usr/bin/env python3
"""Check gate outcomes and inject cancellation at every real gate instruction."""
import argparse
import re
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("binary")
parser.add_argument("--repeats", type=int, default=20)
args = parser.parse_args()
assert args.repeats > 0


def run(*arguments):
    result = subprocess.run([args.binary, *map(str, arguments)],
                            capture_output=True, text=True, timeout=12)
    if result.returncode:
        raise AssertionError((arguments, result.returncode, result.stdout, result.stderr))
    return result.stdout


for case in range(10):
    for repeat in range(args.repeats):
        run(case)
    print(f"case={case}: {args.repeats} passes", flush=True)

nm = subprocess.check_output(["nm", "-n", args.binary], text=True)
symbols = {parts[2]: int(parts[0], 16) for line in nm.splitlines()
           if len(parts := line.split()) == 3}
start = symbols["filc_cancel_syscall_begin"]
end = symbols["filc_cancel_syscall_end"]
disassembly = subprocess.check_output(["objdump", "-d", args.binary], text=True)
addresses = [int(match[1], 16) for line in disassembly.splitlines()
             if (match := re.match(r"\s*([0-9a-f]+):\s", line))
             and start <= int(match[1], 16) <= end]
assert addresses and addresses[0] == start and addresses[-1] == end
for address in addresses:
    run(10, address - start)
print(f"instruction window: {len(addresses)} injection points passed")
