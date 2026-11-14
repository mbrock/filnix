"""Print advisory source tables and closed label-membership witnesses."""
import re


def string(value):
    if not all(32 <= ord(c) <= 126 for c in value):
        raise ValueError(f"source tables require printable ASCII: {value!r}")
    return '"' + value.replace('"', '""') + '"'


def atom(value):
    return '(TAtom ' + string(value) + ')'


def listing(values):
    return '[' + '; '.join(values) + ']'


def source_tables(name, prefix, functions, layout, root):
    files = sorted({f for row in functions for _, f, _ in row['block_src']} |
                   {row['source'][0] for row in functions if row['source'] is not None})
    file_names = {f: f'file_{i}' for i, f in enumerate(files)}

    def filename(value):
        return file_names[value]

    # Sliced fixtures assemble their module term in a Term file.
    code = name + ('Term' if layout in ('hi_atexit', 'getopt') else 'Code')
    term = 'hi_atexit_term' if layout == 'hi_atexit' else prefix + '_term'
    decoded = prefix + '_module'
    if layout in ('hi_atexit', 'getopt'):
        code = name + 'Module'
        decoded = 'hi_module' if layout == 'hi_atexit' else 'getopt_module'
    header = '''(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.

'''
    text = ''
    for f in files:
        text += f'\nDefinition {file_names[f]} : string := {string(f.removeprefix(str(root) + "/"))}.\n'
    if layout not in ('libio', 'stdio', 'buffer', 'string', 'hi_atexit', 'getopt'):
        decoded = 'source_module'
        text += f'''
(** Decoding once lets all source tables share the same checked function bodies. *)
Definition source_module : module := Eval vm_compute in code_module {term}.
'''
    identifiers = set()
    checks = []
    groups = []
    for row in functions:
        fn = row['function']
        ident = 'fn_' + re.sub('[^a-zA-Z0-9_]', '_', fn)
        if ident in identifiers:
            raise ValueError(f"source table identifier collision: {fn}")
        identifiers.add(ident)
        checks.append(f'({string(fn)}, app (map fst {ident}.block_src) {ident}.loop_heads)')
        loc = row['source']
        source = 'None' if loc is None else f'Some ({filename(loc[0])}, {loc[1]}%N)'
        blocks = listing(f'({atom(l)}, ({filename(f)}, {n}%N))' for l, f, n in row['block_src'])
        temps = listing(f'({atom(t)}, {string(n)})' for t, n in row['temp_names'])
        heads = listing(atom(l) for l in row['loop_heads'])
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

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := {heads}.

End {ident}.
''')
    names = listing(string(row['function']) for row in functions)
    footer = f'''
(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) {decoded} with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) {names}.

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) {listing(checks)} = true.
Proof. vm_compute. reflexivity. Qed.
'''
    if len(groups) <= 32:
        return {name + 'Src.v': header + f'\nFrom Glibc Require Import {code}.\nModule {name}Src.\n' +
                text + ''.join(groups) + footer + f'\nEnd {name}Src.\n'}
    common = name + 'SrcFiles'
    output = {common + '.v': header + f'\nModule {common}.\n' + text + f'\nEnd {common}.\n'}
    parts = []
    for i in range(0, len(groups), 24):
        part = f'{name}Src{i // 24 + 1:02d}'
        parts.append(part)
        output[part + '.v'] = (header + f'\nFrom Glibc Require Import {common}.\n' +
                              f'Import {common}.\nModule {part}.\n' +
                              ''.join(groups[i:i + 24]) + f'\nEnd {part}.\n')
    output[name + 'Src.v'] = (header + f'\nFrom Glibc Require Import {code} {common} ' +
                             ' '.join(parts) + f'.\nModule {name}Src.\n' +
                             f'Include {common}.\n' + ''.join(f'Include {p}.\n' for p in parts) +
                             footer + f'\nEnd {name}Src.\n')
    return output
