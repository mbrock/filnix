(** # The Gallina backend's driver, for the arena

    Milestone M3 of docs/lambda-anf.md: what rocq/backend's OCaml
    driver (extraction/main.ml) does for `compile`, `compile-promoted`
    and `compile-allocated FILE.ir`, written in Gallina, so that
    CertiRocq's λANF of it, lowered by anf/lower/AnfLower.v, is the
    whole program but for reading the file and writing the bytes
    (driver.c).

    [run] takes the command and the file's bytes, in pieces, and gives
    a stream: the parts of the assembly a chunk of lines at a time,
    then how the run ends, as the OCaml driver ends it: 0, or 1 for a
    module that is refused (or text that is not read), or 3 for one
    that is outside the compiler, with what it says. Each chunk is
    printed before the next is computed, so its lines die young. *)

From Stdlib Require Import String List Ascii.
From Nanofil Require Import Term.
From Backend Require Import Text Asm Layout Compile IrText.
Import ListNotations.

(** What a run prints: a chunk of parts, then what comes after it; or
    the end, with the exit status and, when it is not 0, what to say
    on stderr. *)
Inductive out : Type :=
| Done (code : nat) (why : string)
| Chunk (ps : parts) (next : unit -> out).

(** The command and the IR text, as the pieces of the file's bytes
    (1 MB each, as main.ml reads them): [cmd] 0 is `compile`, 1
    `compile-promoted`, 2 `compile-allocated`. *)
Record args := mkargs { cmd : nat; input : list string }.

(** The text of the pieces, as IrText.v reads it: each piece a list
    of characters only when the reader asks for it. *)
Fixpoint chunks (l : list string) : chunked :=
  match l with
  | [] => TextEnd
  | c :: r => TextPiece (list_ascii_of_string c) (fun _ => chunks r)
  end.

(** The lines ls, 64 at a time, with the n lines that fit in the chunk
    so far and those in it, last first; then k. *)
Fixpoint emit_lines (n : nat) (rev : list line) (ls : list line) (k : unit -> out) : out :=
  match ls with
  | [] => match rev with [] => k tt | _ => Chunk (rev_lines_parts rev []) k end
  | l :: ls' =>
      match n with
      | O => Chunk (rev_lines_parts rev []) (fun _ => emit_lines 63 [l] ls' k)
      | S n' => emit_lines n' (l :: rev) ls' k
      end
  end.

(** The lists of lines of a piece, each checked for a form that is not
    ported before it is printed; then k. *)
Fixpoint emit_lists (lists : list (list line)) (k : unit -> out) : out :=
  match lists with
  | [] => k tt
  | ls :: rest =>
      match first_todo ls with
      | Some what => Done 3 ("not ported: " ++ what)
      | None => emit_lines 64 [] ls (fun _ => emit_lists rest k)
      end
  end.

(** The pieces of a compiled module, each computed when the one before
    it is printed. *)
Fixpoint emit_pieces (ps : list (unit -> option (list (list line)))) : out :=
  match ps with
  | [] => Done 0 ""
  | p :: rest =>
      match p tt with
      | None => Done 3 "a function is outside the subset or has no plan"
      | Some lists => emit_lists lists (fun _ => emit_pieces rest)
      end
  end.

(** A run of the command on the text. *)
Definition run (a : args) : out :=
  match read_text (chunks (input a)) with
  | None => Done 1 "the IR text is not read"
  | Some m =>
      match (match cmd a with
             | O => compile
             | 1 => compile_promoted
             | _ => compile_allocated
             end) m with
      | Refused why => Done 1 why
      | Outside why => Done 3 why
      | Pieces ps => emit_pieces ps
      end
  end.
