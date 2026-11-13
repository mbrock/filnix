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
    old = manifest.read_text()
    config = tomllib.loads(old)
    styles = {}
    directory = args.tree / manifest.parent.relative_to(manifests)
    if not directory.is_dir():
        parser.error(f"missing fixture directory: {directory}")
    expected = set()
    for batch in [config, *config.get("batch", [])]:
        for row in batch["fixtures"].splitlines():
            if not row.strip():
                continue
            name = row.strip().split("|")[0]
            if batch["layout"] in ("getopt", "hi_atexit"):
                term = directory / (name + "Term.v")
                if not term.is_file():
                    parser.error(f"missing fixture: {term}")
                indices = re.findall(r"\b" + re.escape(name) + r"Code(\d+)\b", term.read_text())
                if not indices:
                    parser.error(f"missing slice references in {term}")
                expected.add(term.name)
                expected.update(f"{name}Code{i:02}.v" for i in range(1, max(map(int, indices)) + 1))
            else:
                expected.add(name + "Code.v")
    if set(config.get("proof_styles", {})) - expected:
        parser.error(f"proof styles name unexpected fixtures in {manifest}")
    for name in sorted(expected):
        file = directory / name
        if not file.is_file():
            parser.error(f"missing fixture: {file}")
        text = file.read_text()
        if "Do not edit." not in text and "Regenerate this file rather than editing it." not in text:
            parser.error(f"unrecognized generated header in {file}")
        blocks = re.compile(r"^\s*Proof\.(.*?)\bQed\.", re.M | re.S)
        proofs = [" ".join(match[1].split()) for match in blocks.finditer(text)]
        if re.search(r"^\s*(Proof|Qed|Defined|Admitted|Abort|Save)\b", blocks.sub("", text), re.M):
            parser.error(f"unrecognized proof block in {file}")
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
