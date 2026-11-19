"""Write typed Rocq definitions for linked IR and assemble them in link order."""
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
import re


IMPORTS = """From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
"""
SCOPES = """Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
"""


def listing(values):
    """Bound the parser stack even for a function with thousands of blocks."""
    if len(values) <= 64:
        return '[' + ';\n  '.join(values) + ']'
    mid = len(values) // 2
    return f'(app {listing(values[:mid])} {listing(values[mid:])})'


def packs(entries, budget):
    pack, used = [], 0
    for entry in entries:
        if pack and used + len(entry) > budget:
            yield pack
            pack, used = [], 0
        pack.append(entry)
        used += len(entry)
    if pack:
        yield pack


def identifier(raw):
    # Escape every punctuation byte other than underscore, including apostrophes.
    return ''.join(chr(c) if c < 128 and (chr(c).isalnum() or c == 95)
                   else f"'{c:02x}" for c in raw)


@dataclass(frozen=True)
class Record:
    kind: str
    symbol: bytes
    body: str
    blocks: tuple[str, ...]

    @property
    def is_function(self):
        return self.kind in ('func', 'func_raw')

    @property
    def identifier(self):
        return ('fn_' if self.is_function else 'item_') + identifier(self.symbol)


def records(text):
    blocks = []
    owner = None
    for row in filter(None, text.split('\x1e')):
        kind, spelling, body = row.split('\t', 2)
        symbol = bytes.fromhex(spelling)
        if blocks and (symbol != owner or kind == 'item'):
            raise ValueError('block owner differs from the enclosing function')
        if kind == 'block':
            owner = symbol
            blocks.append(body)
            continue
        if kind not in ('func', 'func_raw', 'item'):
            raise ValueError(f'invalid Gallina record {kind!r}')
        yield Record(kind, symbol, body, tuple(blocks))
        blocks.clear()
    if blocks:
        raise ValueError('unterminated function in Gallina records')


def file_identifier(value):
    return re.sub(r'[^a-zA-Z0-9_]|Z', lambda m: f'Z{ord(m[0]):02x}', value)


def unit_file(unit):
    path = Path(unit)
    stem = '_'.join(file_identifier(p) for p in path.with_suffix('').parts)
    return Path('glibc', 'Unit_' + stem + '_' + path.suffix[1:])


def write(root, file, description, body, imports=()):
    deps = sorted(set(imports))
    requirements = ''.join('From Glibc Require Import ' + ' '.join(deps[i:i + 8]) + '.\n'
                           for i in range(0, len(deps), 8))
    destination = (root / file).with_suffix('.v')
    destination.parent.mkdir(parents=True, exist_ok=True)
    header = f'(** {description}\n    The glibc code generator reproduces this file. Do not edit. *)\n\n'
    destination.write_text((header + IMPORTS + requirements + SCOPES + '\n' + body).rstrip() + '\n')


class TypedCode:
    def __init__(self, budget=64_000):
        self.budget = budget
        self.units = defaultdict(dict)
        self.descriptions = {}
        self.groups = {}

    def add(self, file, description, record, *, group=None):
        if not record.symbol:
            raise ValueError(f'{file}: the linker must supply an atomic symbol')
        if self.groups.setdefault(file, group) != group:
            raise ValueError(f'{file}: only one fixture may use a grouped object')
        old = self.units[file].setdefault(record.symbol, record)
        if old != record:
            raise ValueError(f'{file}: linked copies of {record.symbol!r} differ')
        previous = self.descriptions.setdefault(file, description)
        if previous != description:
            raise ValueError(f'{file}: different objects map to the same Rocq file')
        return file, record

    def write_unit(self, root, file):
        body, deps = self.unit_body(root, file)
        write(root, file, self.descriptions[file], body, deps)

    def write_units(self, root, directories):
        groups = defaultdict(list)
        for file in sorted(self.units):
            group = self.groups[file]
            if (group or file).parent not in directories:
                continue
            if group is None:
                self.write_unit(root, file)
            else:
                groups[group].append(file)
        for group, files in sorted(groups.items()):
            modules, deps = [], []
            for file in files:
                body, imports = self.unit_body(root, file)
                modules.append(f'(** {self.descriptions[file]} *)\n'
                               f'Module {file.name}.\n{body}End {file.name}.\n')
                deps.extend(imports)
            write(root, group, 'This file defines captured glibc objects used only by one linked image.',
                  '\n'.join(modules), deps)

    def unit_body(self, root, file):
        definitions, deps = [], []
        for record in sorted(self.units[file].values(), key=lambda record: record.symbol):
            ident, body = record.identifier, record.body
            if '%irbytes' in body:
                deps.append('IRBytes')
            if record.is_function:
                deps.append('IRNotation')
                body += self.function_blocks(root, file, record, deps)
            ty = 'func' if record.is_function else 'item'
            definitions.append(f'Definition {ident} : {ty} :=\n  {body}.\n')
        return '\n'.join(definitions), deps

    def function_blocks(self, root, file, record, deps):
        blocks = record.blocks
        parts = list(packs(blocks, self.budget))
        structured = record.kind == 'func'
        if structured and len(parts) <= 1 and 0 < len(blocks) <= 64:
            return ' {\n  ' + ';\n  '.join(blocks) + '\n} }'

        def block_list(part):
            return listing(['ir_blk{ ' + block + ' }' for block in part])

        if len(parts) <= 1:
            expression = f'({block_list(blocks)})'
        else:
            refs = []
            for i, part in enumerate(parts, 1):
                ref = f"{record.identifier}'blocks{i}"
                # File names avoid apostrophes so tools can pass them to the shell.
                digest = record.symbol.hex()
                page = file.with_name(f'{file.name}_Blocks_{digest}_{i}')
                write(root, page, 'These blocks form part of one captured function.',
                      f'Definition {ref} : list block :=\n  {block_list(part)}.\n', ['IRNotation'])
                refs.append(ref)
                deps.append(page.name)
            expression = '(' + ' ++ '.join(refs) + ')'
        return f' blocks {expression} }}' if structured else ' ' + expression

    def write_view(self, root, file, prefix, items, provenance='', check_zero=False):
        definitions, refs, deps, proofs = [], [], [], []
        description = 'This module assembles the selected IR items in link order.'
        chunks = [items[start:start + 64] for start in range(0, len(items), 64)]
        if len(chunks) <= 1 and not check_zero:
            expressions, imports = self.item_refs(items)
            write(root, file, description, f'{provenance}Definition {prefix} : module :=\n'
                  f'  {listing(expressions)}.\n', imports)
            return
        for index, chunk in enumerate(chunks, 1):
            ref = f'{prefix}_items_{index:02}'
            expressions, imports = self.item_refs(chunk)
            deps.extend(imports)
            definitions.append(f'Local Definition {ref} : module :=\n  {listing(expressions)}.\n')
            if check_zero:
                proof = ref + '_zero'
                definitions.append(f'Local Lemma {proof} : zero_nonneg {ref} = true.\n'
                                   'Proof. reflexivity. Qed.\n')
                proofs.append(proof)
            refs.append(ref)
        definitions.append(f'Definition {prefix} : module := ' + (' ++ '.join(refs) or '[]') + '.\n')
        body = provenance + '\n'.join(definitions)
        if check_zero:
            deps.extend(['ImageChunks', 'ImageEraseMem'])
            body += f'\nLemma {prefix}_zero : zero_nonneg {prefix} = true.\nProof.\n'
            body += f'  unfold {prefix}. '
            if proofs:
                body += 'rewrite ?zero_nonneg_app, ' + ', '.join(proofs) + '. '
            body += 'reflexivity.\nQed.\n'
        write(root, file, description, body, deps)


    def item_refs(self, items):
        expressions, imports = [], []
        for file, record in items:
            if file is None:
                expressions.append(record.body)
                continue
            group = self.groups[file]
            module = f'{group.name}.{file.name}' if group else file.name
            ref = f'{module}.{record.identifier}'
            expressions.append('IFunc ' + ref if record.is_function else ref)
            imports.append((group or file).name)
        return expressions, imports
