#!/usr/bin/env python3
"""Exercise the signature gate through its command-line interface."""

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


gate = Path(__file__).with_name("runtime_signature.py")
source = Path(sys.argv[1]) if len(sys.argv) > 1 else gate.resolve().parents[1]
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    for name in ("rocq/theories/core/Runtime.v", "docs/runtime-axioms.md"):
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, target)
    shutil.copytree(source / "tests/c/prog", root / "tests/c/prog")

    def expect(status, message):
        result = subprocess.run([sys.executable, str(gate), str(root)], capture_output=True, text=True)
        output = result.stdout + result.stderr
        assert result.returncode == status and message in output, output
        print(output.strip())

    expect(0, "logical fields have documented probes")
    runtime = root / "rocq/theories/core/Runtime.v"
    runtime.write_text(runtime.read_text().replace(
        "End Runtime.", "Axiom probe_gate_control : True.\nEnd Runtime.", 1))
    expect(1, "probe_gate_control: expected exactly one")
    page = root / "docs/runtime-axioms.md"
    page.write_text(page.read_text() +
        "\n| `probe_gate_control` | Scratch control. | "
        "[probe](../tests/c/prog/axiom-gate-control.c) | Test. |\n")
    expect(1, "probe_gate_control: row must name existing")
    (root / "tests/c/prog/axiom-gate-control.c").write_text("int main(void) { return 0; }\n")
    expect(0, "logical fields have documented probes")
    (root / "tests/c/prog/axiom-fresh.c").unlink()
    expect(1, "row must name existing")

print("runtime-signature: scratch axiom and missing-probe controls passed")
