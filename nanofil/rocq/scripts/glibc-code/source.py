"""Print source tables, a kind of source hint, and closed label-membership witnesses."""
import re


def string(value):
    if not all(32 <= ord(c) <= 126 for c in value):
        raise ValueError(f"source tables require printable ASCII: {value!r}")
    return '"' + value.replace('"', '""') + '"'


def atom(value):
    return '(TAtom ' + string(value) + ')'


def listing(values):
    return '[' + '; '.join(values) + ']'


def source_tables(name, functions, bodies, root, block_definitions):
    files = sorted({f for row in functions for _, f, _ in row['block_src']} |
                   {row['source'][0] for row in functions if row['source'] is not None})
    file_names = {f: f'file_{i}' for i, f in enumerate(files)}

    def filename(value):
        return file_names[value]

    imports = ' '.join(sorted({file for file, _ in bodies.values()}))
    required = f'From Glibc Require Import {imports}.\n' if imports else ''
    header = '''(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

'''
    text = ''
    for f in files:
        text += f'\nDefinition {file_names[f]} : string := {string(f.removeprefix(str(root) + "/"))}.\n'
    identifiers = set()
    checks = []
    groups = []
    for row in functions:
        fn = row['function']
        ident = 'fn_' + re.sub('[^a-zA-Z0-9_]', '_', fn)
        if ident in identifiers:
            raise ValueError(f"source table identifier collision: {fn}")
        identifiers.add(ident)
        tables = [f'map fst {ident}.{table}' for table in ('block_src', 'live_in', 'live_out', 'footprint')]
        labels = f'{ident}.loop_heads'
        for table in reversed(tables):
            labels = f'app ({table}) ({labels})'
        checks.append(f'({string(fn)}, {labels})')
        loc = row['source']
        source = 'None' if loc is None else f'Some ({filename(loc[0])}, {loc[1]}%N)'
        blocks = listing(f'({atom(l)}, ({filename(f)}, {n}%N))' for l, f, n in row['block_src'])
        temps = listing(f'({atom(t)}, {string(n)})' for t, n in row['temp_names'])
        heads = listing(atom(l) for l in row['loop_heads'])
        keys = listing(f'({atom(t)}, ({atom(r)}, {string(k)}, {o if o >= 0 else "(" + str(o) + ")"}))'
                       for t, r, k, o in row['temp_keys'])
        groups.append(f'''
Module {ident}.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := {source}.

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  {blocks}.

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  {temps}.

(** Each row gives a temporary of the body its root temporary, a key and an offset.
    The temporary holds the value of its root, moved by the offset.
    The key is the C variable that the root holds, or "&" and the variable whose address it holds.
    The key of a root without a C variable is the root's own name.
    A temporary without a row is its own root and has no C variable. *)
Definition temp_keys : list (name * (name * string * Z)) :=
  {keys}.

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := {heads}.

{block_definitions[fn]}
End {ident}.
''')
    block_labels = []
    for row in functions:
        symbol = row['function']
        file, body = bodies[symbol]
        block_labels.append(f'({string(symbol)}, map b_label (fn_blocks {file}.{body}))')
    footer = f'''
(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * list name) := Eval lazy in
  {listing(block_labels)}.

(** Projection keeps live sets and memory access records out of the membership computation. *)
Definition table_labels : list (string * list name) := Eval lazy in
  {listing(checks)}.

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) table_labels = true.
Proof. vm_compute. reflexivity. Qed.
'''
    chunks = []
    for group in groups:
        if not chunks or sum(map(len, chunks[-1])) + len(group) > 100000:
            chunks.append([])
        chunks[-1].append(group)
    if len(chunks) == 1:
        return {name + 'Src.v': header + required + f'\nModule {name}Src.\n' +
                text + ''.join(groups) + footer + f'\nEnd {name}Src.\n'}
    common = name + 'SrcFiles'
    output = {common + '.v': header + f'\nModule {common}.\n' + text + f'\nEnd {common}.\n'}
    parts = []
    for i, chunk in enumerate(chunks, 1):
        part = f'{name}Src{i:02d}'
        parts.append(part)
        output[part + '.v'] = (header + f'\nFrom Glibc Require Import {common}.\n' +
                              f'Import {common}.\nModule {part}.\n' +
                              ''.join(chunk) + f'\nEnd {part}.\n')
    output[name + 'Src.v'] = (header + required + f'\nFrom Glibc Require Import {common} ' +
                             ' '.join(parts) + f'.\nModule {name}Src.\n' +
                             f'Include {common}.\n' + ''.join(f'Include {p}.\n' for p in parts) +
                             footer + f'\nEnd {name}Src.\n')
    return output
