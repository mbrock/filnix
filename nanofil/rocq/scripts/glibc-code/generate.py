#!/usr/bin/env python3
"""Regenerate glibc code fixtures and their source hints from the per-directory code.toml manifests."""
import argparse
import difflib
import hashlib
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
GEN = GLIBC / "gen"
source_tables = runpy.run_path(str(HERE / "source.py"))["source_tables"]
layout_tables = runpy.run_path(str(HERE / "layout.py"))["layout_tables"]
block_definitions = runpy.run_path(str(HERE / "block-facts.py"))["block_definitions"]
name_tables = runpy.run_path(str(HERE / "names.py"))["name_tables"]
typed = runpy.run_path(str(HERE / "typed.py"))
PRELUDES = ("CodePrelude.v", "IRNotation.v", "IRBytes.v")
IMAGE_LAYOUTS = ("image", "linked_image", "hi_atexit")


def fixture_entry(layout, roots, prefix, program):
    if program or layout in ("getopt", *IMAGE_LAYOUTS):
        return roots
    return {
        "libio": "libio_roots", "stdio": "stdio_roots", "buffer": "buffer_roots",
        "stdlib": "stdlib_root",
    }.get(layout, prefix + "_roots")


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


def manifest_units(cfg, root=NF):
    """The manifest's unit rows, after the units listed in its units_files."""
    listed = [u for f in cfg.get("units_files", []) for u in rows((root / f).read_text())]
    return ("- " + " ".join(listed) + "\n" if listed else "") + cfg.get("units", "")


def check_units(capture, where, unit_rows):
    """Refuse a repeated or uncaptured unit before compiling any of them."""
    names = [unit for _, unit in units(unit_rows)]
    repeated = sorted({u for u in names if names.count(u) > 1})
    absent = [u for u in names if not (capture / (u + ".i")).is_file()]
    if repeated or absent:
        raise ValueError(f"{where}: units repeated {repeated}, absent from the capture {absent}")


def fixture_prefix(name):
    return {"HiAtexit": "hi_atexit", "PrintfState": "printf_state",
            "PrintfBufferIo": "printf_buffer_io", "PrintfBufferFile": "printf_buffer_file"}.get(name, name.lower())


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
        self.unit_names = {}
        self.layout_files = {}
        self.built = {}
        self.linked = {}
        self.printed = {}
        self.code = typed["TypedCode"]()
        self.model = self.env.get("MODEL")

    def layout_file(self, source, captured=True):
        if source not in self.layout_files:
            env, flags = self.env.copy(), []
            if captured:
                extra, flags = self.survey.cc_options(Path(str(source)[:-2] + '.cmd').read_text())
                env.update(extra)
            path = self.work / f'layout{len(self.layout_files)}.term'
            path.write_text(run([NF / 'bin/nanofil', *flags, 'cc-layouts', source],
                                cwd=NF / 'src', env=env))
            self.layout_files[source] = path
        return self.layout_files[source]

    def layouts(self, paths, functions):
        specs = [f'{obj}={self.layout_file(self.capture / (unit + ".i"))}'
                 for obj, unit in units(paths)]
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

    def objects(self, cfg):
        """Name a flake output's checked object terms as nix/hello-fixture.nix does."""
        if cfg["objects"] not in self.built:
            self.built[cfg["objects"]] = Path(run(["nix", "build", "--no-link", "--print-out-paths",
                                                   f"{NF.parent}#{cfg['objects']}"], cwd=NF.parent).strip())
        out = self.built[cfg["objects"]]
        terms = sorted(out.rglob("*.term"), key=lambda t: "./" + str(t.relative_to(out)))
        return [(t.name.removesuffix(".o.term").removeprefix(cfg.get("object_prefix", "")), t) for t in terms]

    def reference(self, spec):
        """Link the fixture row named DIRECTORY/NAME exactly as its own manifest does."""
        directory, name = spec.split("/")
        cfg = tomllib.loads((GEN / directory / "code.toml").read_text())
        row = next(r for r in rows(cfg["fixtures"]) if r.split("|")[0] == name)
        _, roots, paths, _, *program = row.split("|")
        linked, _ = self.link(cfg, name, roots or cfg.get("roots", ""),
                              "- " + paths if paths else manifest_units(cfg), program[0] if program else "")
        path = self.work / "reference.term"
        path.write_text(linked)
        return path

    def provenance(self, cfg, objects, unit_rows, linked, report):
        """Say where an image fixture came from and what the producer checked on it.

        Without a report, the fixture is the whole image, and the note says how
        the generator presents it instead of what it selected."""
        def digest(pairs):
            lines = "".join(f"{n} {hashlib.sha256(Path(p).read_bytes()).hexdigest()}\n" for n, p in pairs)
            return hashlib.sha256(lines.encode()).hexdigest()
        unit_terms = [(unit, self.compiled[(str(self.capture / (unit + ".i")), cfg.get("mode", "checked"), True)])
                      for _, unit in units(unit_rows)]
        checks = "".join(f"    - {line}\n" for line in report.splitlines()) if report is not None else ""
        selection = '''    The producer selected the items below from the full linked image.
    It checked that each selected name has one item and that its term
    agrees with the term in the `{compare}` fixture.

'''.format(compare=cfg.get("compare")) if report is not None else '''    The extracted module decoder reads the linked term. Its OCaml printer
    writes the resulting constructors as Gallina, and the generator assembles
    the named definitions in link order. Rocq checks these definitions and
    their zero runs. The digests identify the input to the printer.
'''
        return f'''
(** ## Provenance

    The producer linked GNU Hello's {len(objects)} checked objects with {len(unit_terms)} user glibc
    units by `rocq/scripts/link.pl --ctors {cfg.get("roots", "")}`. The objects come from the
    flake output `{cfg["objects"]}`, and the units come from
    the capture `{self.capture}`.
    These SHA-256 digests identify the inputs and the result:

    - objects, by name and term digest: `{digest(objects)}`
    - units, by name and term digest: `{digest(unit_terms)}`
    - the whole linked image: `{hashlib.sha256(linked.encode()).hexdigest()}`

{selection}{checks}*)
'''

    def prolog(self, script, args, data=None):
        return run([self.swipl, NF / "rocq/scripts" / script, *args], data=data, env=self.env)

    def link(self, cfg, name, roots, paths, source, origins=None):
        """Link a manifest fixture before selecting or printing any bodies."""
        lower, layout = fixture_prefix(name), cfg["layout"]
        mode = cfg.get("mode", "checked")
        specs = []
        owners = {}

        def add(obj, term, owner):
            if str(term) in owners:
                raise ValueError(f'{name}: repeated linker input {term}')
            specs.append(f"{obj}={term}")
            owners[str(term)] = owner

        access_units = []
        if cfg.get("objects"):
            for obj, term in self.objects(cfg):
                add(obj, term, (None, obj))
        if source:
            compiled = self.compile(NF / source, mode, False)
            add(lower, compiled, (None, lower))
            if self.sources:
                access_units.extend(['--unit', f'{lower}={compiled}={self.layout_file(NF / source, False)}'])
        for obj, unit in units(paths):
            previous = self.unit_names.setdefault(unit, obj)
            if previous != obj:
                raise ValueError(f"{unit}: inconsistent linker names {previous} and {obj}")
            unit_source = self.capture / (unit + '.i')
            compiled = self.compile(unit_source, mode)
            add(obj, compiled, (unit, obj))
            if self.sources and layout not in ("image", "linked_image"):
                access_units.extend(['--unit', f'{obj}={compiled}={self.layout_file(unit_source)}'])
        entry = fixture_entry(layout, roots, lower, source)
        if not source and layout not in ("getopt", *IMAGE_LAYOUTS):
            items = ",".join(f"item(p,sym('{r}',0))" for r in roots.split())
            root = self.work / "roots.term"
            root.write_text(f"module([data({entry},ro(export),8,[{items}])]).\n")
            obj = 'root' if layout == 'stdlib' else 'roots'
            add(obj, root, (None, 'roots'))
            specs.insert(0, specs.pop())
        flags = (["--context"] if self.sources and layout not in ("image", "linked_image") else []) + (
            ["--ctors"] if cfg.get("ctors") else [])
        if origins is not None:
            flags += ['--origins', origins]
        linked = self.prolog("link.pl", [*flags, entry, *specs])
        if origins is None:
            return linked, access_units
        rows = json.loads(origins.read_text())
        return linked, access_units, {symbol.encode(): owners[path] for path, symbol in rows}

    def records(self, linked):
        if linked not in self.printed:
            if not self.model:
                self.model = str(Path(run(
                    ["nix", "build", "--no-link", "--print-out-paths",
                     f"{NF.parent}#checks.x86_64-linux.nanofil-rocq.model.driver"]
                ).strip()) / "bin/nanofil-model")
            self.printed[linked] = list(typed['records'](run([self.model, "--gallina"], data=linked)))
        return self.printed[linked]

    def generate(self, manifest, output, views, cfg=None):
        if cfg is None:
            cfg = tomllib.loads(manifest.read_text())
            for batch in cfg.pop("batch", []):
                self.generate(manifest, output, views, batch)
        layout = cfg["layout"]
        rel = manifest.parent.relative_to(GEN)
        dest = output / rel
        if views:
            dest.mkdir(parents=True, exist_ok=True)
        if layout in ("stdio", "buffer", "formatter"):
            run(["sha256sum", "-c", manifest.parent / ("buffer-fixtures.sha256" if layout == "buffer" else "fixtures.sha256")], cwd=self.capture)
        for row in rows(cfg["fixtures"]):
            fields = row.split("|")
            if len(fields) not in (4, 5):
                raise ValueError(f"expected NAME|ROOTS|UNITS|FUNCTIONS[|PROGRAM]: {row}")
            name, roots, paths, fns, *program = fields
            if layout == "formatter" and name != "Formatter":
                raise ValueError("formatter layout owns the Formatter fixture")
            if layout == "linked_image" and fns.split():
                raise ValueError(f"{manifest}: linked_image fixture {name} cannot select functions")
            roots = roots or cfg.get("roots", "")
            unit_rows = "- " + paths if paths else manifest_units(cfg)
            lower = fixture_prefix(name)
            source = program[0] if program else ""
            if views and cfg.get('layouts', False):
                layouts = self.layouts(unit_rows, fns.split())
                (dest / (name + 'Layout.v')).write_text(layout_tables(name, layouts))
                tags = {r['tag'] for r in layouts if not r.get('missing', False)}
                missing = sorted({r['tag'] for r in layouts if r.get('missing', False)} - tags)
                print(f'{name}Layout: {len(tags)} record entries; unavailable {missing}', flush=True)
            entry = fixture_entry(layout, roots, lower, source)
            cache_key = (entry, roots, unit_rows, source, cfg.get("objects"), cfg.get("object_prefix"),
                         cfg.get("mode", "checked"), cfg.get("ctors", False))
            if layout in ("image", "linked_image"):
                check_units(self.capture, f"{manifest}: fixture row {row}", unit_rows)
            if cache_key not in self.linked:
                self.linked[cache_key] = self.link(cfg, name, roots, unit_rows, source, self.work / "origins.json")
            linked, access_units, owners = self.linked[cache_key]
            provenance = ""
            if layout == "image":
                whole, report = self.work / "image.term", self.work / "image.report"
                whole.write_text(linked)
                try:
                    selection = run([self.swipl, HERE / "image.pl", whole, self.reference(cfg["compare"]),
                                     report, *fns.split()], env=self.env)
                except subprocess.CalledProcessError as error:
                    raise ValueError(f"{manifest}: fixture row {row}: image selection failed") from error
                provenance = self.provenance(cfg, self.objects(cfg), unit_rows, linked, report.read_text())
                linked = selection
            elif layout == "linked_image":
                provenance = self.provenance(cfg, self.objects(cfg), unit_rows, linked, None)

            records = self.records(linked)
            names = fns.split()
            defined = {r.symbol.decode() for r in records if r.is_function}
            missing = set(names) - defined if layout != "image" else set()
            if missing:
                raise ValueError(f"{manifest}: fixture row {row}: missing function in linked units: {sorted(missing)}")
            if layout in ("libio", "stdio", "buffer"):
                records = [r for r in records if r.is_function and r.symbol.decode() in names]
            items = []
            for record in records:
                unit, obj = owners[record.symbol]
                if unit:
                    file = typed['unit_file'](unit)
                    description = f'This file defines checked IR from glibc’s `{unit}` object.'
                else:
                    file = rel / (name + '_' + typed['file_identifier'](obj))
                    description = f'This file defines checked IR from the `{obj}` object of {name}.'
                items.append(self.code.add(file, description, record))
            if views:
                module = {"HiAtexit": "hi_linked", "HelloImage": "hello_image_linked"}.get(name, lower + "_module")
                self.code.write_view(output, rel / (name + "Code"), module, items, provenance, name == "HelloImage")

            if views and layout not in ("image", "linked_image"):
                term = self.work / "source.term"
                term.write_text(linked)
                facts = json.loads(run([self.swipl, HERE / "source.pl", term, *names], env=self.env))
                block_facts = json.loads(run([NF / 'bin/nanofil', '--script', HERE / 'block-facts.pl',
                                              term, *names, *access_units], env=self.env))
                functions = {r.symbol.decode(): (file.name, r.identifier) for file, r in items if r.is_function}
                for filename, text in source_tables(name, facts, functions, NF, block_definitions(block_facts)).items():
                    (dest / filename).write_text(text)
                bs = [b for r in block_facts for b in r['blocks']]
                accesses = [a for b in bs for a in b['footprint']]
                print(f'{name}Blocks: functions {len(block_facts)}; blocks {len(bs)}; '
                      f'live-in {sum(len(b["live_in"]) for b in bs)}; '
                      f'live-out {sum(len(b["live_out"]) for b in bs)}; accesses {len(accesses)}; '
                      f'rooted {sum(a["root"] is not None for a in accesses)}; '
                      f'constant-root-offset {sum(a["root_offset"] is not None for a in accesses)}; '
                      f'paths {sum(a["path"] != "opaque" for a in accesses)}/{len(accesses)}', flush=True)
                located = sum(r["source"] is not None for r in facts)
                blocks = sum(r["blocks"] for r in facts)
                locations = sum(len(r["block_src"]) for r in facts)
                temps = sum(r["temps"] for r in facts)
                named = sum(len(r["temp_names"]) for r in facts)
                heads = sum(len(r["loop_heads"]) for r in facts)
                print(f"{name}Src: functions {located}/{len(facts)} located; "
                      f"blocks {locations}/{blocks} located; temps {named}/{temps} named; "
                      f"loop heads {heads}", flush=True)
                for r in facts:
                    k = r["key_kinds"]
                    print(f'  {r["function"]}: temporaries {k["current"]}; named {k["named"]}; '
                          f'addresses {k["address"]}; derived {k["derived"]}; fallback {k["raw"]}', flush=True)
                if cfg.get("names", False):
                    text, counts = name_tables(name, facts, block_facts)
                    (dest / (name + "Names.v")).write_text(text)
                    print(f"{name}Names: functions {len(counts)}", flush=True)
                    for fn, k in counts.items():
                        print(f'  {fn}: named {k["named"]}; derived {k["derived"]}; '
                              f'suffixed {k["suffixed"]}; unnamed {k["raw"]}', flush=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture", type=Path, nargs="?")
    parser.add_argument("--directory", action="append", help="relative to rocq/glibc/gen; repeatable")
    parser.add_argument("--tree", type=Path, default=GEN, help="tree to compare or update")
    parser.add_argument("--output", type=Path, help="write generated files to a separate tree")
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if args.output and args.update:
        parser.error("choose --output or --update")
    if args.capture is None:
        args.capture = Path("/tmp/glibc-pp")
        if not args.capture.is_dir():
            args.capture = Path(run(["nix", "build", "--no-link", "--print-out-paths", "-f",
                                     NF / "survey/glibc/capture.nix"]).strip())
    manifests = sorted(GEN.rglob("code.toml"))
    directories = {m.parent.relative_to(GEN) for m in manifests}
    selected = set(map(Path, args.directory)) if args.directory else directories
    if not selected <= directories | {Path("glibc")}:
        parser.error("unknown directory")
    status = 0
    prelude_dir = args.output or (GLIBC if args.tree.resolve() == GEN.resolve() else args.tree)
    for name in PRELUDES:
        source, destination = GLIBC / name, prelude_dir / name
        if source.resolve() == destination.resolve():
            continue
        if args.output or args.update:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(source.read_bytes())
        elif not destination.is_file() or destination.read_bytes() != source.read_bytes():
            print(f"shared prelude differs or is missing: {destination}")
            status = 1
    with tempfile.TemporaryDirectory(prefix="glibc-code-") as tmp:
        work = Path(tmp)
        generator = Generator(args.capture.resolve(), work, sources=True)
        out = work / "output"
        for manifest in manifests:
            generator.generate(manifest, out, manifest.parent.relative_to(GEN) in selected)
        for file in sorted(generator.code.units):
            if file.parent == Path("glibc") or file.parent in selected:
                generator.code.write_unit(out, file)
        for rel in sorted(selected | {Path("glibc")}):
            target = (args.output or args.tree) / rel
            generated = {p.name: p for p in (out / rel).glob("*.v")}
            stale = sorted(p for p in target.glob("*.v") if p.name not in generated)
            different = 0
            for name, path in sorted(generated.items()):
                destination = target / name
                if args.output or args.update:
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes(path.read_bytes())
                elif not destination.exists() or destination.read_bytes() != path.read_bytes():
                    different += 1
                    print("".join(difflib.unified_diff(
                        destination.read_text().splitlines(True) if destination.exists() else [],
                        path.read_text().splitlines(True), str(destination), "regenerated/" + str(rel / name))), end="")
            for path in stale:
                print(f"stale fixture: {path}")
                if args.update:
                    path.unlink()
            if different or (stale and not args.update):
                status = 1
            print(f"{rel}: {len(generated)} files, {different} differ, {len(stale)} stale", flush=True)
    raise SystemExit(status)


if __name__ == "__main__":
    main()
