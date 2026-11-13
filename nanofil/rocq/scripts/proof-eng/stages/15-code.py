#!/usr/bin/env python3
"""Factor generated code helpers without changing a program term or statement."""
import importlib.util
from pathlib import Path
import sys

source = Path(__file__).resolve().parents[2] / "glibc-code/prelude.py"
spec = importlib.util.spec_from_file_location("code_prelude", source)
prelude = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prelude)
# This stage explicitly selects the shared-prelude form; generation defaults
# to the legacy form until the campaign's cutover.
(Path(sys.argv[1]) / "CodePrelude.v").write_bytes(
    (Path(__file__).resolve().parents[1] / "overlay/CodePrelude.v").read_bytes())
count = 0
for path in sorted(Path(sys.argv[1]).rglob("*.v")):
    text = path.read_text()
    # Hand-written proofs can define similarly named helpers. Only generated
    # files bearing the generator's explicit warning belong to this stage.
    if "Do not edit." not in text and "Regenerate this file rather than editing it." not in text:
        continue
    result = prelude.shared(text)
    if result != text:
        path.write_text(result)
        count += 1
project = Path(sys.argv[1]) / "_RocqProject"
if project.exists():
    lines = project.read_text().splitlines()
    if "CodePrelude.v" not in lines:
        first = next((i for i, line in enumerate(lines) if line.endswith(".v")), len(lines))
        lines.insert(first, "CodePrelude.v")
        project.write_text("\n".join(lines) + "\n")
print(f"code: shared the prelude in {count} generated files")
