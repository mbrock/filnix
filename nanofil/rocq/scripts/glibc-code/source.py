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
    def filename(value):
        return string(value.removeprefix(str(root) + '/'))

    # Sliced fixtures assemble their module term in a Term file.
    code = name + ('Term' if layout in ('hi_atexit', 'getopt') else 'Code')
    term = 'hi_atexit_term' if layout == 'hi_atexit' else prefix + '_term'
    text = f'''(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude {code}.
Import ListNotations.
Open Scope string_scope.

Module {name}Src.
'''
    identifiers = set()
    for row in functions:
        fn = row['function']
        ident = 'fn_' + re.sub('[^a-zA-Z0-9_]', '_', fn)
        if ident in identifiers:
            raise ValueError(f"source table identifier collision: {fn}")
        identifiers.add(ident)
        loc = row['source']
        source = 'None' if loc is None else f'Some ({filename(loc[0])}, {loc[1]}%nat)'
        blocks = listing(f'({atom(l)}, ({filename(f)}, {n}%nat))' for l, f, n in row['block_src'])
        temps = listing(f'({atom(t)}, {string(n)})' for t, n in row['temp_names'])
        heads = listing(atom(l) for l in row['loop_heads'])
        text += f'''
Module {ident}.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := {source}.

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  {blocks}.

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  {temps}.

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := {heads}.

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom {string(fn)}) (code_module {term}) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End {ident}.
'''
    return text + f'\nEnd {name}Src.\n'
