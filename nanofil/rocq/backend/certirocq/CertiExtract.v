(** # The backend's compiler, compiled to C by CertiRocq

    As Extract.v for OCaml and crane/CraneExtract.v for Crane: the
    reader of IR text and the three compilers, with what main.c needs
    to print their lines (docs/gallina-backend.md, M8).

    [--anf-variant 8] skips the general [inline_shrink_loop] passes,
    which do not finish on the 22-module backend AST, while keeping
    [Shrink], [Uncurry], [Inline uncurry wrappers], [Lambda lift],
    [Closure conversion and hoisting], [Dead parameter elimination],
    and [Merge duplicate functions]. *)

From CertiRocq.Plugin Require Import Loader.
From Stdlib Require Import String List Ascii.
From Nanofil Require Import Term.
From Backend Require Import Asm Layout Compile IrText.

Record entry_points : Type := EntryPoints {
  ep_read_text : chunked -> option term;
  ep_compile : term -> compiled;
  ep_compile_promoted : term -> compiled;
  ep_compile_allocated : term -> compiled;
  ep_rev_lines_parts : list line -> list string -> list string;
  ep_first_todo : list line -> option string
}.

Definition backend_entries : entry_points :=
  EntryPoints read_text compile compile_promoted compile_allocated
    rev_lines_parts first_todo.

Set CertiRocq Build Directory ".".
CertiRocq Compile --time --time-anf -O 1 --anf-variant 8 --output "nb" backend_entries.
CertiRocq Generate Glue --output "glue" [
  bool, option, list, ascii, string, chunked, term, compiled, entry_points
].
