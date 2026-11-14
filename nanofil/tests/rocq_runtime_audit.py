#!/usr/bin/env python3
"""Audit the top-level proofs recorded in one abstract glibc object's glob."""

import re
import subprocess
import sys
from pathlib import Path


# Only the Runtime interface may supply assumptions. Keep this allowlist
# explicit so a new signature field does not silently authorize itself.
FIELDS = """
state start ready alloc fresh_allocation address_space freed_bounds ready_kept
free free_lifetime retention free_keeps_ids free_checked free_succeeds
at_safepoint safepoints safepoint collector_live safepoint_lifetime non_moving
aux_round_trip rooting safepoint_ready
""".split()
ALLOWED = {f"Fix.R.{name}" for name in FIELDS}


def audit(glob, out):
    text = glob.read_text()
    module = re.search(r"^F(Glibc\.[\w.]+)$", text, re.M)
    if not module:
        raise ValueError(f"{glob}: missing Glibc module identity")
    names = re.findall(r"^prf \d+:\d+ <> (\S+)$", text, re.M)
    queries = [f"Require Import {module[1]}."]
    queries += [f"Print Assumptions {module[1]}.{name}." for name in names]
    Path("RuntimeAudit.v").write_text("\n".join(queries) + "\n")
    result = subprocess.run(
        ["rocq", "c", "-q", "-R", "theories", "Nanofil", "-R", "glibc", "Glibc", "RuntimeAudit.v"],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (out / "assumptions.log").write_text(result.stdout)
    if result.returncode:
        raise ValueError(result.stdout)
    actual = set(re.findall(r"^(\S+)\s*:", result.stdout, re.M)) - {"Axioms"}
    unexpected = actual - ALLOWED
    if unexpected:
        raise ValueError(f"{module[1]}: unexpected assumptions: {sorted(unexpected)}")
    # A missing query/report is not evidence of a closed theorem.
    reports = result.stdout.count("Closed under the global context") + len(
        re.findall(r"^Axioms:\s*$", result.stdout, re.M)
    )
    if reports != len(names):
        raise ValueError(f"{module[1]}: {reports} reports for {len(names)} proofs")
    (out / "assumption-names").write_text("".join(n + "\n" for n in sorted(actual)))
    summary = f"{module[1]}: {len(names)} top-level proofs audited\n"
    (out / "summary").write_text(summary)
    print(summary, end="")


if __name__ == "__main__":
    try:
        audit(Path(sys.argv[1]), Path(sys.argv[2]))
    except ValueError as error:
        sys.exit(f"runtime-audit: {error}")
