"""Print advisory block facts without adding executable IR or proof premises."""
from pathlib import Path
import re
import runpy

helpers = runpy.run_path(str(Path(__file__).with_name('source.py')))
string, atom, listing = (helpers[n] for n in ('string', 'atom', 'listing'))


def block_tables(name, functions):
    header = '''(** An executor needs to know which values and memory regions a block may use.
    These tables list live temporaries and explicit memory accesses to guide that choice.
    Wrong hints can stop execution, but they cannot justify a memory access.
    No soundness theorem may assume that these tables are correct.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

'''
    checks = []
    groups = []
    for row in functions:
        fn = row['function']
        ident = 'fn_' + re.sub('[^a-zA-Z0-9_]', '_', fn)
        text = f'\nModule {ident}.\n'
        for field in ('live_in', 'live_out'):
            values = listing(f'({atom(b["label"])}, {listing(atom(t) for t in b[field])})'
                             for b in row['blocks'])
            text += f'\nDefinition {field} : list (name * list name) :=\n  {values}.\n'
        blocks = []
        for block in row['blocks']:
            accesses = []
            for access in block['footprint']:
                address = access['address']
                a = ('(TInt (' + str(address['name']) + '))' if address['kind'] == 'const' else
                     f'(TApp {string(address["kind"])} [{atom(address["name"])}])')
                root = 'None' if access['root'] is None else f'(Some {atom(access["root"])})'
                width = 'None' if access['width'] is None else f'(Some {access["width"]})'
                distance = 'None' if access['root_offset'] is None else f'(Some ({access["root_offset"]}))'
                reads, writes = str(access['read']).lower(), str(access['write']).lower()
                accesses.append(f'({access["index"]}%N, {a}, ({access["offset"]}), {width}, '
                                f'{reads}, {writes}, {root}, {distance})')
            blocks.append(f'({atom(block["label"])}, {listing(accesses)})')
        text += f'''
(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  {listing(blocks)}.

End {ident}.
'''
        groups.append(text)
        checks.append(f'({string(fn)}, app (map fst {ident}.live_in) '
                      f'(app (map fst {ident}.live_out) (map fst {ident}.footprint)))')
    footer = f'''
(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  {listing(checks)}.

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) {name}Src.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End {name}Blocks.
'''
    if len(groups) <= 32 and sum(map(len, groups)) <= 60000:
        return {name + 'Blocks.v': header + f'\nFrom Glibc Require Import {name}Src.\n' +
                f'Module {name}Blocks.\n' + ''.join(groups) + footer}
    chunks = []
    for group in groups:
        if not chunks or len(chunks[-1]) >= 24 or sum(map(len, chunks[-1])) + len(group) > 60000:
            chunks.append([])
        chunks[-1].append(group)
    output, parts = {}, []
    for i, chunk in enumerate(chunks, 1):
        part = f'{name}Blocks{i:02d}'
        parts.append(part)
        output[part + '.v'] = (header + f'\nModule {part}.\n' +
                              ''.join(chunk) + f'\nEnd {part}.\n')
    output[name + 'Blocks.v'] = (header + f'\nFrom Glibc Require Import {name}Src ' +
                                ' '.join(parts) + f'.\nModule {name}Blocks.\n' +
                                ''.join(f'Include {p}.\n' for p in parts) + footer)
    return output
