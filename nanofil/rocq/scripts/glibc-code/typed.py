"""Lay out the extracted model's Gallina expressions in independently compiled files."""
from collections import defaultdict
import re


HEADER = """(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
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


def packs(entries, size, budget):
    pack, used = [], 0
    for entry in entries:
        cost = size(entry)
        if pack and used + cost > budget:
            yield pack
            pack, used = [], 0
        pack.append(entry)
        used += cost
    if pack:
        yield pack


def identifier(raw):
    # Apostrophes are legal inside a Rocq identifier and always introduce
    # exactly two hex digits here, including when the input contains one.
    return ''.join(chr(c) if c < 128 and (chr(c).isalnum() or c == 95)
                   else f"'{c:02x}" for c in raw)


def family(raw):
    # Proofs import a symbol family by name, independent of packing or link order.
    stem = raw.rsplit(b'#', 1)[-1].removeprefix(b'__GI_').lstrip(b'_')
    letters = re.match(rb'[A-Za-z]{1,2}', stem)
    return letters[0].decode().upper() if letters else 'Other'


def typed_image(output, name, records, provenance='', budget=64_000):
    prefix = {'HiAtexit': 'hi', 'HelloImage': 'hello_image'}[name]
    check_zero = name == 'HelloImage'
    groups = defaultdict(list)
    order, blocks, seen = [], [], set()

    def write(stem, body, imports=(), exports=()):
        def require(action, names):
            return f"From Glibc Require {action} {' '.join(sorted(set(names)))}.\n" if names else ''
        header = HEADER + require('Import', imports) + require('Export', exports)
        (output / (stem + '.v')).write_text((header + SCOPES + '\n' + body).rstrip() + '\n')

    block_owner = None
    for row in records.split('\x1e'):
        if not row:
            continue
        kind, spelling, body = row.split('\t', 2)
        raw = bytes.fromhex(spelling)
        if block_owner is not None and (raw != block_owner or kind not in ('block', 'func')):
            raise ValueError('block owner differs from the enclosing function')
        if kind == 'block':
            block_owner = raw
            blocks.append(body)
            continue
        if kind not in ('func', 'item') or (blocks and kind != 'func'):
            raise ValueError(f'invalid Gallina record {kind!r}')
        tag = 'fn' if kind == 'func' else 'item'
        ident = f'{prefix}_{tag}_{identifier(raw)}'
        if ident in seen or not raw:
            ident += f"'n{len(order)}"
        seen.add(ident)
        stem = name + 'Typed' + (family(raw) if kind == 'func' else 'Objects')
        imports = []
        if kind == 'func':
            parts = list(packs(blocks, len, budget))
            if len(parts) <= 1:
                body += ' ' + listing(blocks)
            else:
                refs = []
                for i, part in enumerate(parts, 1):
                    ref = f"{ident}'blocks{i}"
                    file = f'{stem}Blocks{len(order)}x{i}'
                    write(file, f'Definition {ref} : list block :=\n  {listing(part)}.\n')
                    refs.append(ref)
                    imports.append(file)
                body += ' (' + ' ++ '.join(refs) + ')'
            blocks = []
            block_owner = None
        definition = f'Definition {ident} : {kind} :=\n  {body}.\n'
        groups[stem].append((definition, imports, ident))
        order.append((ident, 'IFunc ' + ident if kind == 'func' else ident))
    if blocks:
        raise ValueError('unterminated function in Gallina records')

    owners = {}
    for stem, definitions in groups.items():
        pages = list(packs(definitions, lambda row: len(row[0]), budget))
        files = []
        for i, page in enumerate(pages, 1):
            file = stem if len(pages) == 1 else f'{stem}{i:02}'
            write(file, '\n'.join(d for d, _, _ in page), [p for _, deps, _ in page for p in deps])
            owners.update((ident, file) for _, _, ident in page)
            files.append(file)
        if len(files) > 1:
            write(stem, '', exports=files)

    parts, refs, proofs = [], [], []
    for start in range(0, len(order), 64):
        chunk = order[start:start + 64]
        index = start // 64 + 1
        part = f'{name}TypedItems{index:02}'
        ref = f'{prefix}_items_{index:02}'
        body = f'Definition {ref} : module :=\n  {listing([expr for _, expr in chunk])}.\n'
        imports = [owners[ident] for ident, _ in chunk]
        if check_zero:
            imports.append('HelloImageEraseMem')
            proof = ref + '_zero'
            body += f'\nLemma {proof} : zero_nonneg {ref} = true.\nProof. reflexivity. Qed.\n'
            proofs.append(proof)
        write(part, body, imports)
        parts.append(part)
        refs.append(ref)

    decoded = prefix + '_decoded'
    body = provenance + f'\nDefinition {decoded} : module := ' + (' ++ '.join(refs) or '[]') + '.\n'
    if check_zero:
        parts.extend(['HelloImageChunks', 'HelloImageEraseMem'])
        body += f'\nLemma {decoded}_zero : zero_nonneg {decoded} = true.\nProof.\n'
        body += f'  unfold {decoded}. '
        if proofs:
            body += 'rewrite ?zero_nonneg_app, ' + ', '.join(proofs) + '. '
        body += 'reflexivity.\nQed.\n'
    write(name + 'Code', body, parts)
