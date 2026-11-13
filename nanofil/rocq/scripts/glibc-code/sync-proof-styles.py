#!/usr/bin/env python3
"""Record main's per-file computed-proof styles in the manifests, not fixtures."""
import argparse
from pathlib import Path
import re
import tomllib

here = Path(__file__).resolve().parent
manifests = here.parents[2] / "rocq/glibc"
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("tree", type=Path, help="glibc tree whose proof styles should be recorded")
args = parser.parse_args()

updates = []
for manifest in sorted(manifests.rglob("code.toml")):
    styles = {}
    directory = args.tree / manifest.parent.relative_to(manifests)
    if not directory.is_dir():
        parser.error(f"missing fixture directory: {directory}")
    for file in sorted(directory.glob("*Code*.v")):
        text = file.read_text()
        if "Do not edit." not in text and "Regenerate this file rather than editing it." not in text:
            continue
        proofs = re.findall(r"^Proof\. (.*?) Qed\.$", text, re.M)
        kinds = set()
        for proof in proofs:
            if proof == "vm_compute. reflexivity.":
                kinds.add("vm_compute")
            elif re.fullmatch(r"vm_cast_no_check \(eq_refl .+\)\.", proof):
                kinds.add("vm_cast_no_check")
            else:
                raise ValueError(f"unrecognized computed proof in {file}: {proof}")
        if len(kinds) > 1:
            raise ValueError(f"mixed proof styles in {file}; finish that file's conversion first")
        if kinds == {"vm_cast_no_check"}:
            styles[file.name] = "vm_cast_no_check"
    old = manifest.read_text()
    config = tomllib.loads(old)
    if config.get("proof_styles", {}) == styles:
        continue
    text = re.sub(r"(?ms)^\[proof_styles\]\n.*?(?=^\[|\Z)", "", old).rstrip() + "\n"
    if styles:
        text += "\n[proof_styles]\n" + "".join(f'"{name}" = "{style}"\n' for name, style in styles.items())
    updates.append((manifest, text, len(styles)))

# Validate every file before changing a manifest.
for manifest, text, count in updates:
    manifest.write_text(text)
    print(f"{manifest.relative_to(manifests)}: {count} vm_cast_no_check files")
print(f"proof styles: {len(updates)} manifests updated")
