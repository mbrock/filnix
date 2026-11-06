#!/usr/bin/env python3
"""Run a check with timestamped progress, a soft budget and a hard deadline.

Output is forwarded unchanged. Every 15s, even when the child is silent,
report its label, elapsed time and most recent output. A hard timeout kills
the whole process group, not just the shell waiting for the test.
"""
import argparse
import datetime
import os
import selectors
import signal
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--label", required=True)
    parser.add_argument("--interval", type=float, default=15)
    parser.add_argument("--warn-after", type=float, default=60)
    parser.add_argument("--timeout", type=float, default=300)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or not 0 < args.interval or not 0 < args.warn_after <= args.timeout:
        parser.error("need a command and positive interval, warning and timeout budgets")
    start = time.monotonic()
    last, pending, warned = "no output yet", b"", False

    def report(state):
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        elapsed = time.monotonic() - start
        print(f"@@nanofil-progress {stamp} {state} elapsed={elapsed:.1f}s "
              f"label={args.label} last={last}", flush=True)

    report("start")
    child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             start_new_session=True)

    def terminate(grace=1):
        # The shell can exit before a grandchild; signal the group either way.
        try:
            os.killpg(child.pid, signal.SIGTERM)
            time.sleep(grace)
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def interrupted(signum, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupted)
    next_report = start + args.interval
    timed_out = False
    try:
        with selectors.DefaultSelector() as selector:
            selector.register(child.stdout, selectors.EVENT_READ)
            while selector.get_map() or child.poll() is None:
                now = time.monotonic()
                if not warned and now - start >= args.warn_after:
                    report(f"WARNING budget={args.warn_after:g}s")
                    warned = True
                if now - start >= args.timeout:
                    report(f"TIMEOUT budget={args.timeout:g}s")
                    timed_out = True
                    terminate()
                    break
                if now >= next_report:
                    report("running")
                    next_report = now + args.interval
                for key, _ in selector.select(timeout=min(.25, max(0, next_report - now))):
                    data = os.read(key.fd, 65536)
                    if not data:
                        selector.unregister(key.fileobj)
                        continue
                    sys.stdout.buffer.write(data)
                    sys.stdout.buffer.flush()
                    lines = (pending + data).split(b"\n")
                    pending = lines.pop()[-500:]
                    if lines:
                        # Do not replay machine-readable completion markers:
                        # fleet coverage must count each actual step only once.
                        last = " ".join(lines[-1].decode(errors="replace").split()).replace("@@", "")[-240:]
        code = child.wait()
    except KeyboardInterrupt:
        report("interrupted")
        # A parent watchdog may itself be timing out. Clean up our child
        # group before that parent escalates and kills this watchdog.
        terminate(grace=0)
        child.wait()
        return 130
    finally:
        child.stdout.close()
    report(f"done exit={124 if timed_out else code}")
    return 124 if timed_out else code if code >= 0 else 128 - code


if __name__ == "__main__":
    sys.exit(main())
