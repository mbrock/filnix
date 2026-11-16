#!/usr/bin/env python3
"""Exercise the kernel-checking lint through its command-line interface."""

import subprocess
import sys
import tempfile
from pathlib import Path


gate = Path(__file__).resolve().parents[1] / "rocq/scripts/kernel-flags.py"
commands = [
    ("Unset Universe Checking.", "checking flag"),
    ("Local Unset Guard Checking.", "checking flag"),
    ("#[local] Unset Positivity Checking.", "checking flag"),
    ("Set Universe Checking.", "checking flag"),
    ("Typing Flags Set foo.", "typing flags"),
    ("Set Definitional UIP.", "definitional UIP"),
    ("Set Rewrite Rules.", "rewrite rules"),
    ("Symbol bad : nat.", "rewrite rules"),
    ("Rewrite Rule bad := x.", "rewrite rules"),
    ("Parameter Inline bad : nat.", "inlined parameter"),
    ("#[bypass_check] Definition bad := 0.", "bypass_check attribute"),
    ("Primitive bad : nat.", "kernel primitive"),
    ("Register bad as foo.", "kernel primitive"),
    ('Declare ML Module "bad_plugin".', "plugin load"),
]
options = [
    "-type-in-type",
    "-impredicative-set",
    "-allow-rewrite-rules",
    '-set "Guard Checking"',
    '-unset "Universe Checking"',
]

with tempfile.TemporaryDirectory() as tmp:
    roots = [Path(tmp) / name for name in ("theories", "glibc")]
    for root in roots:
        (root / "nested").mkdir(parents=True)

    def expect(status, message):
        result = subprocess.run(
            [sys.executable, str(gate), *map(str, roots)], capture_output=True, text=True
        )
        output = result.stdout + result.stderr
        assert result.returncode == status and message in output, output

    (roots[0] / "Clean.v").write_text(
        "(* Unset Guard Checking. (* #[bypass_check] *) *)\n"
        'Definition text := "Unset Universe Checking. Declare ML Module ""bad"".".\n'
        "Definition n := 0.\n"
    )
    expect(0, "no command weakens kernel checking")
    for index, (command, kind) in enumerate(commands):
        control = roots[index % 2] / "nested/Control.v"
        control.write_text("(* Scratch control. *)\n" + command + "\n")
        expect(1, f"{kind}:")
        control.unlink()
    for filename in ("_RocqProject", "_CoqProject"):
        control = roots[1] / "nested" / filename
        for option in options:
            control.write_text("-R . Glibc\n" + option + "\n")
            expect(1, f"{filename}:2: command-line option: {option.split()[0]}")
        control.unlink()
    expect(0, "no command weakens kernel checking")

print(f"kernel-flags: {len(commands) + 2 * len(options)} forbidden-command and option controls rejected; "
      "comments and strings ignored")
