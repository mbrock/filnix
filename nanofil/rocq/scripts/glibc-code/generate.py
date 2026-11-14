#!/usr/bin/env python3
"""Regenerate glibc code fixtures from the per-directory code.toml manifests."""
import argparse
import difflib
import importlib.util
import json
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile
import tomllib


HERE = Path(__file__).resolve().parent
NF = HERE.parents[2]
GLIBC = NF / "rocq/glibc"
shared = runpy.run_path(str(HERE / "prelude.py"))["shared"]
source_tables = runpy.run_path(str(HERE / "source.py"))["source_tables"]
layout_tables = runpy.run_path(str(HERE / "layout.py"))["layout_tables"]
block_tables = runpy.run_path(str(HERE / "block-facts.py"))["block_tables"]
PRELUDE = GLIBC / "CodePrelude.v"


def run(args, *, cwd=NF, data=None, env=None):
    return subprocess.run(list(map(str, args)), cwd=cwd, input=data or "",
                          text=True, stdout=subprocess.PIPE, check=True, env=env).stdout


def rows(text):
    return [line.strip() for line in text.splitlines() if line.strip()]


def units(text):
    for line in rows(text):
        obj, *paths = line.split()
        if obj == "-":
            for path in paths:
                yield "glibc_" + re.sub(r"\.o[sS]$", "", Path(path).name).replace("-", "_"), path
        else:
            if len(paths) != 1:
                raise ValueError(f"expected OBJECT UNIT: {line}")
            yield obj, paths[0]


def fixture_prefix(name):
    return {"HiAtexit": "hi_atexit", "PrintfState": "printf_state",
            "PrintfBufferIo": "printf_buffer_io", "PrintfBufferFile": "printf_buffer_file"}.get(name, name.lower())


def decoded(prefix, fns, layout):
    text = f'''
From Nanofil Require Import Syntax Transport Semantics.

(** {"The module, decoded." if layout == "string" else "The functions, decoded as a module."} *)
Definition {prefix}_module : module := Eval vm_compute in
  match decode_module {prefix}_term with Some md => md | None => [] end.

(** The term decodes to the module. *)
Lemma {prefix}_decodes : decode_module {prefix}_term = Some {prefix}_module.
Proof. vm_compute. reflexivity. Qed.

(** The function named n of the module, or an empty one. *)
Definition {prefix}_fn (n : string) : func :=
  match find_direct (TAtom n) {prefix}_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.
'''
    for fn in fns.split():
        stem = re.sub(r"^__GI_", "", fn)
        g = ("glibc" + re.sub(r"^_*", "_", stem) if layout == "string"
             else "glibc_" + stem.replace("#", "_"))
        text += f'''
(** glibc's `{fn}`. *)
Definition {g} : func := Eval vm_compute in {prefix}_fn "{fn}".
'''
        if layout == "string":
            text += f'''(** The module defines `{fn}` as [{g}]. *)
Lemma {g}_found : find_direct (TAtom "{fn}") {prefix}_module = Some (Defined {g}).
Proof. vm_compute. reflexivity. Qed.
'''
    return text


def stdio(text, prefix, fns, layout):
    buffer = layout == "buffer"
    _, body = text.split("*)", 1)
    body = body.replace("(** The one-character atom with code n. *)",
                        "(** This helper constructs the atom containing one character with code n. *)")
    body = body.replace("(** The module term. *)",
                        "(** This term contains the selected checked function bodies. *)")
    header = '''(** These checked bodies implement cancellation-state changes and printf-buffer
    completion in user-glibc 2.44. The fixture supports instruction proofs
    without treating either function as an external contract.

    rocq/glibc/stdio/code.sh reproduces these terms from the pinned capture
    with gallina.pl. Regenerate this file rather than editing it. *)'''
    if buffer:
        header = '''(** These checked bodies implement printf-buffer operations in user-glibc 2.44.
    They retain the source's failure paths and calls into stream operations;
    decoding these bodies does not establish contracts for those calls.

    rocq/glibc/stdio/buffer-code.sh reproduces these terms from the pinned
    capture with gallina.pl. Regenerate this file rather than editing it. *)'''
    tail = f'''
From Nanofil Require Import Syntax Transport Semantics.

(** {"Decoding gives the actual checked bodies used by instruction proofs." if buffer else "Decoding gives the actual checked function bodies, not their specifications."} *)
Definition {prefix}_module : module := Eval vm_compute in
  match decode_module {prefix}_term with Some md => md | None => [] end.

(** {"Computation rules out the empty fallback in the decoded module." if buffer else "Computation checks that decoding did not take the empty fallback."} *)
Lemma {prefix}_decodes : decode_module {prefix}_term = Some {prefix}_module.
Proof. vm_compute. reflexivity. Qed.

(** {"Function lookup selects a checked body without supplying its specification." if buffer else "Function lookup selects a decoded body for the subsequent instruction proofs."} *)
Definition {prefix}_fn (n : string) : func :=
  match find_direct (TAtom n) {prefix}_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.
'''
    functions = fns.split()
    if not buffer:
        # The original state fixture presents cancellation before completion.
        functions = sorted(functions, key=lambda f: f != "__GI___pthread_setcancelstate")
    witnesses = []
    for fn in functions:
        short = fn.removeprefix("__GI_").lstrip("_")
        g = "glibc___" + short
        comment = {
            "__GI___pthread_setcancelstate": "This body changes the thread's cancellation flag and optionally saves its old value.",
            "__printf_buffer_done": "This body returns the accumulated count or reports failure and integer overflow.",
        }.get(fn, f"This definition selects the checked body of [{fn}].")
        tail += f'''
(** {comment} *)
Definition {g} : func := Eval vm_compute in
  {prefix}_fn "{fn}".
'''
        label, comment = {
            "__GI___pthread_setcancelstate": ("cancel", "Lookup finds the cancellation body rather than the empty fallback."),
            "__printf_buffer_done": ("done", "Lookup finds the completion body rather than the empty fallback."),
        }.get(fn, (short, "Computation checks that lookup found the body rather than its fallback."))
        rhs = f"{prefix}_module = Some (Defined {g})." if buffer else f"{prefix}_module =\n  Some (Defined {g})."
        witness = f'''
(** {comment} *)
Lemma {prefix}_find_{label} :
  find_direct (TAtom "{fn}") {rhs}
Proof. vm_compute. reflexivity. Qed.
'''
        if buffer:
            tail += witness
        else:
            witnesses.append(witness)
    return header + body + tail + "".join(witnesses)


class Generator:
    def __init__(self, capture, work, sources=False):
        self.capture = capture
        self.work = work
        self.sources = sources
        self.env = os.environ.copy()
        for name in ("NANOFIL_STD", "NANOFIL_COMMON", "NANOFIL_MATH_ERRNO", "NANOFIL_STATE"):
            self.env.pop(name, None)
        self.swipl = self.env.get("SWIPL", "swipl")
        state = work / "nanofil.state"
        run([NF / "bin/nanofil", "--save-state", state], cwd=NF / "src", env=self.env)
        self.env["NANOFIL_STATE"] = str(state)
        spec = importlib.util.spec_from_file_location("survey", NF / "survey/glibc/run.py")
        self.survey = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.survey)
        self.compiled = {}
        self.layout_files = {}

    def layouts(self, paths, functions):
        specs = []
        for obj, unit in units(paths):
            source = self.capture / (unit + '.i')
            if source not in self.layout_files:
                env = self.env.copy()
                extra, flags = self.survey.cc_options(Path(str(source)[:-2] + '.cmd').read_text())
                env.update(extra)
                path = self.work / f'layout{len(self.layout_files)}.term'
                path.write_text(run([NF / 'bin/nanofil', *flags, 'cc-layouts', source],
                                    cwd=NF / 'src', env=env))
                self.layout_files[source] = path
            specs.append(f'{obj}={self.layout_files[source]}')
        return json.loads(run([self.swipl, HERE / 'layout.pl', ','.join(functions), *specs], env=self.env))

    def compile(self, source, mode, captured=True):
        key = (str(source), mode, captured)
        if key in self.compiled:
            return self.compiled[key]
        env, flags = self.env.copy(), []
        if captured and mode != "outcomes":
            extra, flags = self.survey.cc_options(Path(str(source)[:-2] + ".cmd").read_text())
            env.update(extra)
        command = [NF / "bin/nanofil"]
        if mode == "checked" and not self.sources:
            text = run(command + ["-O", *flags, "checked-terms", source], cwd=NF / "src", env=env)
        else:
            ir = self.work / f"unit{len(self.compiled)}.ir"
            ir.write_text(run(command + (["-O"] if mode in ("trap", "checked") else []) +
                              flags + ["cc-ir", source], cwd=NF / "src", env=env))
            args = (["--script", "../bench/trap-checked.pl", ir] if mode in ("trap", "checked")
                    else ["-O", "outcomes", ir])
            text = run(command + args, cwd=NF / "src", env=env)
            if mode == "outcomes":
                text = "\n".join(line for line in text.splitlines() if line.startswith("module(")) + "\n"
        path = self.work / f"unit{len(self.compiled)}.term"
        path.write_text(text)
        self.compiled[key] = path
        return path

    def prolog(self, script, args, data=None):
        return run([self.swipl, NF / "rocq/scripts" / script, *args], data=data, env=self.env)

    def link(self, cfg, name, roots, paths, source):
        """Link a manifest fixture before selecting or printing any bodies."""
        lower, layout = fixture_prefix(name), cfg["layout"]
        mode = cfg.get("mode", "checked")
        specs = []
        if source:
            specs.append(f"{lower}={self.compile(NF / source, mode, False)}")
        for obj, unit in units(paths):
            specs.append(f"{obj}={self.compile(self.capture / (unit + '.i'), mode)}")
        entry = roots
        if not source and layout != "getopt":
            entry = {"libio": "libio_roots", "stdio": "stdio_roots", "buffer": "buffer_roots", "stdlib": "stdlib_root"}.get(layout, lower + "_roots")
            items = ",".join(f"item(p,sym('{r}',0))" for r in roots.split())
            root = self.work / "roots.term"
            root.write_text(f"module([data({entry},ro(export),8,[{items}])]).\n")
            specs.insert(0, f"{'root' if layout == 'stdlib' else 'roots'}={root}")
        return self.prolog("link.pl", (["--context"] if self.sources else []) +
                           (["--ctors"] if cfg.get("ctors") else []) + [entry, *specs])

    def generate(self, manifest, output, cfg=None):
        if cfg is None:
            cfg = tomllib.loads(manifest.read_text())
            for batch in cfg.pop("batch", []):
                self.generate(manifest, output, batch)
        layout = cfg["layout"]
        checker = str(manifest.parent.relative_to(NF) / ("buffer-code.sh" if layout == "buffer" else "code.sh"))
        if layout in ("stdio", "buffer"):
            run(["sha256sum", "-c", manifest.parent / ("buffer-fixtures.sha256" if layout == "buffer" else "fixtures.sha256")], cwd=self.capture)
        linked_cache = {}
        for row in rows(cfg["fixtures"]):
            fields = row.split("|")
            if len(fields) not in (4, 5):
                raise ValueError(f"expected NAME|ROOTS|UNITS|FUNCTIONS[|PROGRAM]: {row}")
            name, roots, paths, fns, *program = fields
            roots = roots or cfg.get("roots", "")
            unit_rows = "- " + paths if paths else cfg.get("units", "")
            lower = fixture_prefix(name)
            source = program[0] if program else ""
            if self.sources and cfg.get('layouts', False):
                layouts = self.layouts(unit_rows, fns.split())
                (output / (name + 'Layout.v')).write_text(layout_tables(name, layouts))
                tags = {r['tag'] for r in layouts if not r.get('missing', False)}
                missing = sorted({r['tag'] for r in layouts if r.get('missing', False)} - tags)
                print(f'{name}Layout: {len(tags)} record entries; unavailable {missing}', flush=True)
            cache_key = (roots, unit_rows, source)
            if cache_key not in linked_cache:
                linked_cache[cache_key] = self.link(cfg, name, roots, unit_rows, source)
            linked = linked_cache[cache_key]
            if self.sources:
                term = self.work / "source.term"
                term.write_text(linked)
                facts = json.loads(run([self.swipl, HERE / "source.pl", term, *fns.split()], env=self.env))
                for filename, text in source_tables(name, lower, facts, layout, NF).items():
                    (output / filename).write_text(text)
                block_facts = json.loads(run([NF / 'bin/nanofil', '--script', HERE / 'block-facts.pl',
                                              term, *fns.split()], env=self.env))
                for filename, text in block_tables(name, block_facts).items():
                    (output / filename).write_text(text)
                bs = [b for r in block_facts for b in r['blocks']]
                accesses = [a for b in bs for a in b['footprint']]
                print(f'{name}Blocks: functions {len(block_facts)}; blocks {len(bs)}; '
                      f'live-in {sum(len(b["live_in"]) for b in bs)}; '
                      f'live-out {sum(len(b["live_out"]) for b in bs)}; accesses {len(accesses)}; '
                      f'rooted {sum(a["root"] is not None for a in accesses)}; '
                      f'constant-root-offset {sum(a["root_offset"] is not None for a in accesses)}', flush=True)
                located = sum(r["source"] is not None for r in facts)
                blocks = sum(r["blocks"] for r in facts)
                locations = sum(len(r["block_src"]) for r in facts)
                temps = sum(r["temps"] for r in facts)
                named = sum(len(r["temp_names"]) for r in facts)
                heads = sum(len(r["loop_heads"]) for r in facts)
                print(f"{name}Src: functions {located}/{len(facts)} located; "
                      f"blocks {locations}/{blocks} located; temps {named}/{temps} named; "
                      f"loop heads {heads}", flush=True)
            if fns.split():
                selected = self.work / "linked.term"
                selected.write_text(linked)
                try:
                    functions = run([self.swipl, HERE / "select.pl", selected, *fns.split()], env=self.env)
                except subprocess.CalledProcessError as error:
                    raise ValueError(f"{manifest}: fixture row {row}: function selection failed") from error
                if layout in ("libio", "stdio", "buffer"):
                    linked = functions
            unit_names = [re.sub(r"\.o[sS]$", "", Path(unit).name) for _, unit in units(unit_rows)]
            unit_description = " and ".join([", ".join(unit_names[:-1]), unit_names[-1]]) if len(unit_names) > 1 else "".join(unit_names)
            description = {
                "program": f"{source} with user glibc's {paths}, linked by rocq/scripts/link.pl",
                "string": f"user glibc's {paths}, linked from {roots} by rocq/scripts/link.pl",
                "libio": f"user glibc's narrow libio and exit units (rocq/glibc/libio/code.sh), linked from {roots} by rocq/scripts/link.pl, its functions {fns}",
                "stdlib": f"user glibc's {unit_description} units from the roots " + ",".join(roots.split()) + ", linked by rocq/scripts/link.pl",
                "hi_atexit": f"{source} linked with its {len(unit_names)} user glibc units by rocq/scripts/link.pl --ctors",
                "getopt": f"user glibc's {unit_description} units linked from {roots}",
                "stdio": "the pinned user-glibc 2.44 cancellation and printf-buffer completion units",
                "buffer": "the pinned user-glibc 2.44 printf-buffer units",
            }[layout]
            text = self.prolog("gallina.pl", ([] if layout in ("program", "stdlib") else ["--chunk"]) +
                               [lower, description, checker], linked)
            if layout in ("hi_atexit", "getopt"):
                whole = self.work / "whole.v"
                whole.write_text(text)
                run(["python3", "-I", HERE / "slice.py", whole, output, layout])
            else:
                if layout in ("string", "libio"):
                    text += decoded(lower, fns, layout)
                elif layout in ("stdio", "buffer"):
                    text = stdio(text, lower, fns, layout)
                if self.sources and layout in ("libio", "stdio", "buffer"):
                    text = text.replace("From Stdlib Require Import String ZArith List Ascii.",
                                        "From Glibc Require Import GlibcTactics.\n"
                                        "From Stdlib Require Import String ZArith List Ascii.")
                (output / (name + "Code.v")).write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture", type=Path, nargs="?")
    parser.add_argument("--directory", action="append", help="relative to rocq/glibc; repeatable")
    parser.add_argument("--tree", type=Path, default=GLIBC, help="tree to compare or update")
    parser.add_argument("--output", type=Path, help="write generated files to a separate tree")
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--form", choices=("shared-prelude",), default="shared-prelude",
                        help="output form (shared-prelude)")
    args = parser.parse_args()
    if args.output and args.update:
        parser.error("choose --output or --update")
    if args.capture is None:
        args.capture = Path("/tmp/glibc-pp")
        if not args.capture.is_dir():
            args.capture = Path(run(["nix", "build", "--no-link", "--print-out-paths", "-f",
                                     NF / "survey/glibc/capture.nix"]).strip())
    manifests = sorted(GLIBC.rglob("code.toml"))
    if args.directory:
        manifests = [m for m in manifests if str(m.parent.relative_to(GLIBC)) in args.directory]
        if len(manifests) != len(set(args.directory)):
            parser.error("unknown directory")
    status = 0
    prelude = (args.output or args.tree) / "CodePrelude.v"
    if args.output or args.update:
        prelude.parent.mkdir(parents=True, exist_ok=True)
        prelude.write_bytes(PRELUDE.read_bytes())
    elif not prelude.exists() or prelude.read_bytes() != PRELUDE.read_bytes():
        print(f"shared prelude differs or is missing: {prelude}")
        status = 1
    with tempfile.TemporaryDirectory(prefix="glibc-code-") as tmp:
        work = Path(tmp)
        generator = Generator(args.capture.resolve(), work, sources=True)
        for manifest in manifests:
            styles = tomllib.loads(manifest.read_text()).get("proof_styles", {})
            rel = manifest.parent.relative_to(GLIBC)
            out = work / "output" / rel
            out.mkdir(parents=True, exist_ok=True)
            generator.generate(manifest, out)
            generated = sorted(out.glob("*.v"))
            unknown = set(styles) - {p.name for p in generated}
            if unknown:
                raise ValueError(f"proof styles name nonexistent fixtures in {manifest}: {sorted(unknown)}")
            target = args.tree / rel
            stale = set()
            if not args.output and args.form == 'shared-prelude':
                for pattern in ('*Src[0-9]*.v', '*SrcFiles.v', '*Blocks[0-9]*.v'):
                    stale.update(p for p in target.glob(pattern) if not (out / p.name).exists())
            # Only numbered slices are exclusively owned by a slicer.
            for prefix in (() if args.output else ("HiAtexit", "Getopt")):
                if any(p.name.startswith(prefix + "Code") for p in generated):
                    stale.update(p for p in target.glob(prefix + "Code[0-9]*.v") if not (out / p.name).exists())
            different = 0
            for path in generated:
                text = computed_proofs(path.read_text(), styles.get(path.name, "vm_compute"))
                path.write_text(shared(text))
                destination = (args.output / rel if args.output else target) / path.name
                if args.output or args.update:
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes(path.read_bytes())
                elif not destination.exists() or destination.read_bytes() != path.read_bytes():
                    different += 1
                    print("".join(difflib.unified_diff(
                        destination.read_text().splitlines(True) if destination.exists() else [],
                        path.read_text().splitlines(True), str(destination), "regenerated/" + str(rel / path.name))), end="")
            for path in sorted(stale):
                print(f"stale fixture: {path}")
            if different or stale:
                status = 1
            if args.output or args.update:
                print(f"{rel}: {len(generated)} files written, {len(stale)} stale", flush=True)
            else:
                print(f"{rel}: {len(generated)} files, {different} differ, {len(stale)} stale", flush=True)
    raise SystemExit(status)


def computed_proofs(text, style):
    """Emit the manifest's closed-equality style, without reading the target."""
    if style == "vm_compute":
        return text
    if style != "vm_cast_no_check":
        raise ValueError(f"unknown computed proof style: {style}")
    lemma = re.compile(
        r"(^Lemma \w+\b.*?=\s*)(Some [^\n]+)\.\n"
        r"Proof\. vm_compute\. reflexivity\. Qed\.", re.M | re.S)
    result = lemma.sub(lambda m: m[1] + m[2] + ".\nProof. vm_cast_no_check (eq_refl (" +
                       m[2] + ")). Qed.", text)
    if "Proof. vm_compute. reflexivity. Qed." in result:
        raise ValueError("unrecognized generated computed equality")
    return result


if __name__ == "__main__":
    main()
