#!/usr/bin/env python3
"""Require that Rocq rejects one file with an error of its own.

    rocq_reject.py --file FILE.v [--timeout SECONDS] [--log LOG] -- COMMAND...

The glibc check lists the proof files that need the interpreter's
runtime, and each listed file must fail to compile against an abstract
runtime. A failure certifies that only when the compiler itself rejected
the file. This program runs COMMAND, which compiles FILE.v, and exits
with status 0 only when COMMAND exits with status 1 and reports an error
at a position in FILE.v that is neither a resource error nor a failure
to load a library.

It exits with status 1, and says why, when the file compiles, when
COMMAND does not start, runs out of time, is ended by a signal or exits
with another status, and when its error is not located in FILE.v.
"""
import argparse
import os
import re
import signal
import subprocess
import sys

# Rocq reports these at a position in the file with status 1, but they
# say that the compiler could not do its work, not that the file is wrong.
NOT_A_REJECTION = [
    "Out of memory",
    "Stack overflow",
    "Timeout",
    "Anomaly",
    "User interrupt",
    "Cannot find a physical path",
    "Cannot find library",
    "Unable to locate library",
    "Cannot load",
    "Compiled library",
    "inconsistent assumptions",
    "bad magic number",
    "No such file",
    "Permission denied",
]

LOCATED = re.compile(r'^File "([^"]+)", line (\d+), characters \d+-\d+:\n(Error:.*?)(?=^File "|\Z)',
                     re.M | re.S)


def refuse(reason, output=""):
    sys.stdout.write(output)
    print(f"rocq_reject: refused: {reason}", file=sys.stderr)
    return 1


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--file", required=True, help="the source file that COMMAND compiles")
    parser.add_argument("--timeout", type=float, default=900)
    parser.add_argument("--log", help="write COMMAND's output here")
    parser.add_argument("command", nargs="+")
    args = parser.parse_args()
    try:
        # The compiler gets its own process group, so that a timeout ends
        # every process it started.
        process = subprocess.Popen(args.command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, errors="replace", start_new_session=True)
    except OSError as error:
        return refuse(f"the compiler did not start: {error}")
    try:
        output, _ = process.communicate(timeout=args.timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
        timed_out = True
    if args.log:
        with open(args.log, "w") as log:
            log.write(output)
    if timed_out:
        return refuse(f"the compiler did not finish in {args.timeout:g} seconds", output)
    status = process.returncode
    if status == 0:
        return refuse(f"{args.file} compiles", output)
    if status < 0:
        return refuse(f"the compiler was ended by signal {-status}", output)
    if status != 1:
        return refuse(f"the compiler exited with status {status}, not with the status 1 of a rejected file", output)
    wanted = os.path.normpath(args.file)
    errors = [(line, text) for name, line, text in LOCATED.findall(output)
              if os.path.normpath(name) == wanted]
    if not errors:
        return refuse(f"the compiler reported no error at a position in {args.file}", output)
    line, text = errors[-1]
    for phrase in NOT_A_REJECTION:
        if phrase in text:
            return refuse(f"the error at line {line} is not a rejection of the file: {phrase}", output)
    sys.stdout.write(output)
    print(f"rocq_reject: accepted: Rocq rejects {args.file} at line {line}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
