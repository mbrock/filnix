#!/usr/bin/env python3
"""Select plausible Fil-C inputs from pinned Nixpkgs without building packages."""

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
EXPRESSION = ROOT / "scripts/package-inventory.nix"
sys.path.insert(0, str(ROOT))
from experiment.scope import kernel_metadata

POLICY_VERSION = 2
SELECTED = {"candidate", "uncertain"}
ASSEMBLY = re.compile(r"(?i)(?:\b|_)(?:asm|assembly|assembler|nasm|yasm|simd|sse[234]?|avx\w*|neon)(?:\b|_)")
JIT = re.compile(r"(?i)\b(?:jit|luajit|javascriptcore|v8)\b")
COMPILE = re.compile(r"\$(?:\{)?(?:CC|CXX)\b|\b(?:gcc|clang|g\+\+|c\+\+)\s|\b(?:cmake|meson|autoreconfHook)\b")
OTHER_BUILDERS = re.compile(r"\b(?:buildRustPackage|buildGoModule|buildGoPackage|buildDunePackage|buildMavenPackage|buildRebar3|mixRelease)\b")
SCRIPT_BUILDERS = re.compile(r"\b(?:buildPythonApplication|buildPythonPackage|buildNpmPackage|buildNodePackage|buildYarnPackage|buildRubyGem)\b")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def read_jsonl(path, recover_tail=False):
    data = path.read_bytes()
    lines = data.splitlines(keepends=True)
    rows, offset = [], 0
    for index, line in enumerate(lines):
        try:
            rows.append(json.loads(line))
        except (json.JSONDecodeError, UnicodeDecodeError):
            if recover_tail and index == len(lines) - 1 and not line.endswith(b"\n"):
                # A killed writer may leave only part of its last observation.
                with path.open("r+b") as stream:
                    stream.truncate(offset)
                return rows
            raise
        offset += len(line)
    if recover_tail and data and not data.endswith(b"\n"):
        with path.open("ab") as stream:
            stream.write(b"\n")
    return rows


def command(args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


class Evaluator:
    """One bounded evaluator at a time; errors are isolated by splitting batches."""

    def __init__(self, nixpkgs=None, timeout=45, memory_mib=4096):
        self.nixpkgs = nixpkgs
        self.timeout = timeout
        self.memory_mib = memory_mib
        self.cpus = sorted(os.sched_getaffinity(0))[:2]

    def limits(self):
        os.sched_setaffinity(0, self.cpus)
        limit = self.memory_mib * 1024 * 1024
        resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

    def evaluate(self, expression, **variables):
        env = os.environ.copy()
        # Pin our configuration instead of inheriting user evaluator overrides.
        env.update({"FILNIX_INVENTORY_ROOT": str(ROOT), **variables})
        args = ["nix", "eval", "--offline", "--impure", "--json", "--no-write-lock-file",
                "--option", "allow-import-from-derivation", "false",
                "--option", "max-jobs", "0", "--option", "builders", "",
                "--option", "eval-cores", "1", "--expr", expression]
        proc = subprocess.Popen(args, cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                start_new_session=True, preexec_fn=self.limits)
        try:
            stdout, stderr = proc.communicate(timeout=self.timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.communicate()
            raise RuntimeError(f"evaluation exceeded {self.timeout}s") from None
        if proc.returncode:
            raise RuntimeError(f"evaluator exit {proc.returncode}: {stderr[-6000:]}")
        try:
            return json.loads(stdout), stderr
        except json.JSONDecodeError as error:
            raise RuntimeError(f"invalid evaluator output: {error}") from error

    def resolve(self):
        result, _ = self.evaluate('''
          let f = builtins.getFlake (builtins.getEnv "FILNIX_INVENTORY_ROOT");
          in f.inputs.nixpkgs.outPath
        ''')
        self.nixpkgs = result
        return result

    def metadata(self, names):
        return self.evaluate('''
          import (builtins.toPath (builtins.getEnv "FILNIX_INVENTORY_EXPRESSION")) {
            nixpkgsPath = builtins.toPath (builtins.getEnv "FILNIX_INVENTORY_NIXPKGS");
            names = builtins.fromJSON (builtins.getEnv "FILNIX_INVENTORY_NAMES");
          }
        ''', FILNIX_INVENTORY_EXPRESSION=str(EXPRESSION),
            FILNIX_INVENTORY_NIXPKGS=self.nixpkgs,
            FILNIX_INVENTORY_NAMES=json.dumps(names))

    def batch(self, names, log):
        try:
            records, stderr = self.metadata(names)
            if stderr:
                log.write(json.dumps({"attrs": names, "diagnostic": stderr[-12000:]}) + "\n")
            return records
        except RuntimeError as error:
            log.write(json.dumps({"attrs": names, "diagnostic": str(error)}) + "\n")
            log.flush()
            if len(names) == 1:
                return [{"attrPath": names, "status": "evaluation-error", "error": str(error)}]
            middle = len(names) // 2
            return self.batch(names[:middle], log) + self.batch(names[middle:], log)


def source_evidence(metadata, nixpkgs):
    """Inspect packaging expressions and adjacent patches, never realize src."""
    position = metadata.get("position")
    if not position:
        return None, [], []
    file = Path(position.rsplit(":", 1)[0])
    try:
        relative = file.relative_to(nixpkgs).as_posix()
    except ValueError:
        return None, [], []
    # Shared/generated expressions contain unrelated packages. Do not match
    # their contents or adjacent patches as if they belonged to one package.
    if (not file.is_file() or file.stat().st_size > 128 * 1024
            or relative.startswith(("pkgs/top-level/", "pkgs/build-support/"))):
        return relative, [], []
    evidence, tags = [], set()
    files = [file] + sorted(file.parent.glob("*.patch")) + sorted(file.parent.glob("*.diff"))
    for source in files[:21]:
        if source.stat().st_size > 512 * 1024:
            continue
        for number, line in enumerate(source.read_text(errors="replace").splitlines(), 1):
            signals = []
            if ASSEMBLY.search(line):
                signals.append("assembly-mentioned")
            if JIT.search(line):
                signals.append("jit-mentioned")
            if source == file and COMPILE.search(line):
                signals.append("c-build-mentioned")
            if source == file and OTHER_BUILDERS.search(line):
                signals.append("other-language-builder-mentioned")
            if source == file and SCRIPT_BUILDERS.search(line):
                signals.append("script-package-builder-mentioned")
            for tag in signals:
                tags.add(tag)
                # A handful of examples per signal is enough to review a choice.
                if sum(e["signal"] == tag for e in evidence) < 4:
                    evidence.append({"signal": tag, "file": source.relative_to(nixpkgs).as_posix(),
                                     "line": number, "text": line.strip()[:240]})
    return relative, sorted(tags), evidence


def classify(record, source_file=None, source_tags=(), evidence=()):
    row = {**record, "sourceFile": source_file, "evidence": list(evidence)}
    tags = set(source_tags)
    reasons = []
    decision = "unresolved"
    if record["status"] == "not-a-package":
        decision, reasons = "excluded", ["top-level attribute is not a derivation"]
    elif record["status"] != "evaluated":
        reasons = ["metadata evaluation failed; retained for review"]
    else:
        m = record["metadata"]
        # Some inputs have no name (Nixpkgs 26.05 has a few).
        native = [n for n in m.get("nativeBuildInputs") or [] if n]
        inputs = [n for n in (m.get("buildInputs") or []) + (m.get("propagatedBuildInputs") or []) if n]
        hints = m.get("builderHints") or {}
        pname = m.get("pname") or record["attrPath"][0]
        for name in native:
            if re.match(r"^(?:nasm|yasm)(?:-|$)", name):
                tags.add("assembler-build-input")
            if re.match(r"^(?:rustc|cargo|go|ghc|gfortran|ocaml|jdk|zig|mono|dotnet-sdk)(?:-|$)", name):
                tags.add("other-language-toolchain-input")
        for name in inputs:
            if re.match(r"^(?:erlang|ghc|ocaml|mono|jre|jdk|libgfortran)(?:-|$)", name):
                tags.add("other-language-library-or-runtime-input")
        if m.get("broken"):
            tags.add("marked-broken-in-native-nixpkgs")
        if record.get("unavailableFields"):
            tags.add("incomplete-metadata")
        if m.get("doCheck"):
            tags.add("native-check-enabled")
        if m.get("doInstallCheck"):
            tags.add("native-install-check-enabled")
        for lang in ("python", "node"):
            if hints.get(lang):
                tags.add(f"{lang}-package-builder")
        if any(name.startswith("python-imports-check-hook") for name in native):
            tags.add("python-package-builder")

        unsupported = [lang for lang in ("go", "haskell", "ocaml") if hints.get(lang)]
        if hints.get("rust"):
            tags.add("rust-dependencies-declared")
            # cargoDeps also appears on C programs with optional Rust components,
            # such as Ruby's YJIT. Only the active Rust build hook is decisive.
            if any(name.startswith("cargo-build-hook") for name in native):
                unsupported.append("rust")
        for hook, language in (("dotnet-build-hook", "dotnet"), ("dart-build-hook", "dart")):
            if any(name.startswith(hook) for name in native):
                unsupported.append(language)
        # The compilers/runtimes themselves can evade their ecosystem builders.
        if pname in {"go", "rustc", "cargo", "ghc", "ocaml", "erlang", "zig"} and not unsupported:
            unsupported.append(pname)
        kernel = kernel_metadata(m, source_file)
        binary = any(s in {"binaryNativeCode", "binaryBytecode", "binaryFirmware"}
                     for s in (m.get("sourceProvenance") or []))
        c_clues = "c-build-mentioned" in tags or any(
            re.match(r"^(?:cmake|meson|autoreconf)(?:-|$)", name) for name in native)
        if m.get("availableOnLinux") is False:
            decision, reasons = "excluded", ["unavailable on x86_64-linux according to native metadata"]
        elif kernel:
            decision, reasons = "excluded", ["Linux kernel; outside the Fil-C userspace runtime"]
        elif unsupported:
            decision, reasons = "excluded", ["active non-C/C++ builder or implementation: " + ", ".join(unsupported)]
        elif binary:
            decision, reasons = "excluded", ["declared prebuilt code or firmware"]
        elif m.get("hasSource") is False and not c_clues:
            decision, reasons = "deferred", ["no source or C/C++ build evidence; often a wrapper or aggregate"]
        elif m.get("hasCompiler") is False and not c_clues:
            decision, reasons = "deferred", ["no C/C++ compiler in stdenv and no packaging clue for C/C++ compilation"]
        elif m.get("dontBuild") and not c_clues:
            decision, reasons = "deferred", ["build phase disabled and no C/C++ build clue"]
        elif ("python-package-builder" in tags or hints.get("node")
              or "script-package-builder-mentioned" in tags
              or "rust-dependencies-declared" in tags
              or "other-language-toolchain-input" in tags
              or "other-language-builder-mentioned" in tags
              or record.get("unavailableFields")):
            decision, reasons = "uncertain", ["possible C/C++ or mixed build; include for discovery"]
        elif m.get("hasCompiler") and m.get("hasSource"):
            decision, reasons = "candidate", ["source package with a C/C++ standard environment"]
        else:
            decision, reasons = "uncertain", ["packaging suggests compilation; include for discovery"]
    row.update(decision=decision, selected=decision in SELECTED, reasons=reasons, tags=sorted(tags))
    return row


def render_report(output):
    run = json.loads((output / "run.json").read_text())
    records = read_jsonl(output / "metadata.jsonl")
    attributes = [tuple(row["attrPath"]) for row in records]
    if len(set(attributes)) != len(attributes):
        raise ValueError("metadata contains duplicate attribute paths")
    if not set(attributes) <= {(name,) for name in run["universe"]}:
        raise ValueError("metadata contains attributes outside the recorded universe")
    rows = []
    source_cache = {}
    for record in sorted(records, key=lambda r: r["attrPath"]):
        m = record.get("metadata", {})
        position = m.get("position")
        if position not in source_cache:
            source_cache[position] = source_evidence(m, Path(run["nixpkgsPath"]))
        rows.append(classify(record, *source_cache[position]))
    counts = Counter(row["decision"] for row in rows)
    candidates = [row for row in rows if row["selected"]]
    tags = Counter(tag for row in candidates for tag in row["tags"])
    reasons = Counter(reason for row in rows if not row["selected"] for reason in row["reasons"])
    manifest = {
        "schemaVersion": 1, "policyVersion": POLICY_VERSION,
        "nixpkgs": run["nixpkgs"], "system": "x86_64-linux",
        "scope": run["scope"], "complete": len(records) == len(run["universe"]),
        "metadataSha256": digest((output / "metadata.jsonl").read_bytes()),
        "policySha256": digest(Path(__file__).read_bytes()),
        "counts": dict(counts), "selected": len(candidates),
        "attrPaths": [row["attrPath"] for row in candidates],
    }
    write_json(output / "candidates.json", manifest)
    (output / "inventory.jsonl").write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    (output / "candidates.txt").write_text("".join(row["attrPath"][0] + "\n" for row in candidates))
    (output / "policy.py").write_bytes(Path(__file__).read_bytes())
    lines = ["# Fil-C package inventory", "",
             f"Nixpkgs: `{run['nixpkgs']['rev']}`. Scope: {run['scope']}.", "",
             f"Recorded **{len(records):,} / {len(run['universe']):,}** top-level attributes; "
             f"selected **{len(candidates):,}** package attributes for later attempts.", "",
             "| Decision | Attributes |", "| --- | ---: |"]
    lines += [f"| {key} | {counts[key]:,} |" for key in ("candidate", "uncertain", "excluded", "deferred", "unresolved")]
    lines += ["", "Candidate and uncertain entries are both in `candidates.json`. "
              "Assembly clues never exclude an entry. Counts are attributes, not distinct derivations or successful builds.", "",
              "## Annotations among selected inputs", "", "| Annotation | Attributes |", "| --- | ---: |"]
    lines += [f"| {tag} | {count:,} |" for tag, count in tags.most_common()]
    lines += ["", "## Reasons for leaving entries outside the initial list", "", "| Reason | Attributes |", "| --- | ---: |"]
    lines += [f"| {reason} | {count:,} |" for reason, count in reasons.most_common()]
    examples = defaultdict(list)
    for row in rows:
        if len(examples[row["decision"]]) < 20:
            examples[row["decision"]].append(row["attrPath"][0])
    lines += ["", "## Examples", ""]
    lines += [f"- {key}: " + ", ".join(f"`{name}`" for name in values) for key, values in sorted(examples.items())]
    assembly = [r["attrPath"][0] for r in candidates if {"assembly-mentioned", "assembler-build-input"} & set(r["tags"])]
    lines += ["", "Selected assembly examples: " + ", ".join(f"`{name}`" for name in assembly[:40]), "",
              "## What this establishes", "",
              "This is a permissive selection from native Nixpkgs metadata and packaging files. "
              "Nested package collections are not recursively enumerated. Deprecated aliases are disabled, "
              "but other aliases/variants remain. Exact derivation deduplication belongs to build planning.", "",
              "Classification inspects packaging files, not upstream source trees. No Fil-C package derivations "
              "were evaluated and no builds or tests were requested. Check flags describe the native recipe only. "
              "Assembly/JIT tags are clues, including disabled paths and nearby patches; absence is not evidence of absence. "
              "Dependency lists retain their roles but are not a transitive dependency audit.", "",
              "`run.json` records the pin, complete attribute universe, evaluator and Filnix context. "
              "`metadata.jsonl` retains raw observations; `inventory.jsonl` adds decisions and evidence. "
              "`candidates.json` is the machine-readable input set; `candidates.txt` is its readable attribute list. "
              "`diagnostics.jsonl` retains evaluator diagnostics. Policy and expression copies accompany the results.", ""]
    (output / "REPORT.md").write_text("\n".join(lines))
    print(json.dumps({"output": str(output), "selected": len(candidates), "counts": dict(counts)}, sort_keys=True), flush=True)
    return rows


def positive(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--packages", nargs="+", help="restrict to these exact top-level attribute names")
    parser.add_argument("--limit", type=positive, help="inspect the first N sorted attributes (for calibration)")
    parser.add_argument("--batch-size", type=positive, default=128)
    parser.add_argument("--eval-timeout", type=positive, default=45)
    parser.add_argument("--memory-mib", type=positive, default=4096)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--report-only", action="store_true", help="reclassify saved metadata without invoking Nix")
    args = parser.parse_args()
    output = args.output.resolve()
    if args.report_only:
        render_report(output)
        return
    if output.exists() and not args.resume:
        parser.error("output already exists; choose another directory or use --resume / --report-only")
    evaluator = Evaluator(timeout=args.eval_timeout, memory_mib=args.memory_mib)
    nixpkgs = evaluator.resolve()
    lock = json.loads((ROOT / "flake.lock").read_text())["nodes"]["nixpkgs"]["locked"]
    names, _ = evaluator.metadata(None)
    if args.packages:
        missing = set(args.packages) - set(names)
        if missing:
            parser.error("unknown top-level attributes: " + ", ".join(sorted(missing)))
        names = sorted(set(args.packages))
    if args.limit:
        names = names[:args.limit]
    identity = {"nixpkgs": lock, "nixpkgsPath": nixpkgs, "universe": names,
                "evaluatorSha256": digest(EXPRESSION.read_bytes())}
    if args.resume:
        run = json.loads((output / "run.json").read_text())
        if any(run.get(key) != value for key, value in identity.items()):
            parser.error("resume requires the same pin, universe, and evaluator; use a new output directory")
    else:
        output.mkdir(parents=True)
        diff = subprocess.check_output(["git", "diff", "HEAD", "--binary"], cwd=ROOT)
        (output / "filnix-context.patch").write_bytes(diff)
        (output / "evaluator.nix").write_bytes(EXPRESSION.read_bytes())
        write_json(output / "run.json", {**identity, "schemaVersion": 1,
                   "createdAt": datetime.now(timezone.utc).isoformat(),
                   "scope": "explicit top-level subset" if args.packages or args.limit else "native x86_64-linux top-level package set, aliases disabled",
                   "filnixRevision": command(["git", "rev-parse", "HEAD"]),
                   "filnixContextDiffSha256": digest(diff),
                   "filcCorePin": json.loads((ROOT / "lib/filc-upstream.json").read_text())["coreRev"],
                   "filcPortsPin": json.loads((ROOT / "ports/upstream.json").read_text())["portsRev"],
                   "nixVersion": command(["nix", "--version"]),
                   "limits": {"evaluatorAddressSpaceMiB": args.memory_mib,
                              "evaluatorCPUs": evaluator.cpus, "batchTimeoutSeconds": args.eval_timeout},
                   "buildsAllowed": False})
    raw = output / "metadata.jsonl"
    done = {tuple(r["attrPath"]) for r in read_jsonl(raw, recover_tail=True)} if raw.exists() else set()
    remaining = [name for name in names if (name,) not in done]
    print(f"Inventory: {len(names)} attributes, {len(done)} already recorded; evaluation only.", flush=True)
    with raw.open("a") as data, (output / "diagnostics.jsonl").open("a") as log:
        for start in range(0, len(remaining), args.batch_size):
            batch = remaining[start:start + args.batch_size]
            records = evaluator.batch(batch, log)
            for row in records:
                data.write(json.dumps(row, sort_keys=True) + "\n")
            data.flush()
            print(f"Recorded {len(done) + start + len(batch)}/{len(names)}", flush=True)
    render_report(output)


if __name__ == "__main__":
    main()
