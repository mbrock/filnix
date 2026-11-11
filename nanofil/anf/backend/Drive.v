(** # The Gallina backend's driver, for the arena

    This file is the program that the λANF build of the Gallina backend
    runs, for milestones M3 and M4 of docs/lambda-anf.md. It does what
    the OCaml driver of rocq/backend does for the commands `compile`,
    `compile-promoted`, `compile-allocated`, `shared-allocated` and
    `object-allocated`. It also compiles the bytecode of PCRE2 patterns
    with the regex compiler of anf/rx/Rx.v. CertiRocq's λANF of this
    file, lowered by anf/lower/AnfLower.v, is the whole program. Only
    reading the input and writing the bytes are left to C, in
    anf/backend/driver.c and anf/lib/libnanofil.c.

    The function [run] takes the command and the input in pieces, and
    it gives a stream. The stream holds the output a chunk of lines at a
    time, and then the status that the OCaml driver exits with, with
    what it says on stderr. The status is 0, or 1 for a module that is
    refused or a text that is not read, or 3 for a module that is
    outside the compiler. Each chunk is printed before the next is
    computed, so its lines die young. *)

From Stdlib Require Import String List Ascii ZArith NArith.
From Nanofil Require Import Term.
From Backend Require Import Text Asm Layout Compile IrText Encode Elf.
From AnfBackend Require Rx.
Import ListNotations.

(** What a run prints: a chunk of parts, then what comes after it; or
    the end, with the exit status and, when it is not 0, what to say
    on stderr. *)
Inductive out : Type :=
| Done (code : nat) (why : string)
| Chunk (ps : parts) (next : unit -> out).

(** The command and the IR text, as the pieces of the file's bytes
    (1 MB each, as main.ml reads them): [cmd] 0 is `compile`, 1
    `compile-promoted`, 2 `compile-allocated`, 3 `shared-allocated`
    (the bytes of the shared object, not a file), 4
    `object-allocated` and 5 `regex`, whose text is not IR but the
    terms of experiments/regex-nanofil/pcre2_rx_terms.h. *)
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

(** The lines of every piece, last first in front of [acc], or [None]
    when a function is outside the subset: a loop, as the lines of a
    module are many. *)
Fixpoint all_lines_rev (ps : list (unit -> option (list (list line)))) (acc : list line) : option (list line) :=
  match ps with
  | [] => Some acc
  | p :: rest =>
      match p tt with
      | Some lists => all_lines_rev rest (fold_left (fun a ls => rev_append ls a) lists acc)
      | None => None
      end
  end.

(** Bytes as the strings of a stream, 4096 bytes to a part. A part is
    cut with Encode.v's loops, as the stdlib's [firstn] and [map] are
    as deep as the part is long in the λANF build. *)
Fixpoint byte_parts (fuel : nat) (bs : list Z) : parts :=
  match fuel with
  | O => []
  | S fuel' =>
      match bs with
      | [] => []
      | _ => string_of_list_ascii (map_tr (fun b => ascii_of_N (Z.to_N b)) (take 4096 bs))
               :: byte_parts fuel' (skipn 4096 bs)
      end
  end.

(** What `shared-allocated` ([shared]) and `object-allocated` give for
    the compiled module: the object Encode.v makes of its lines, as
    the bytes of the shared object Elf.v links or as the text of the
    gate (tests/encode.sh); or why it cannot. Both are main.ml's
    object_file, message for message. *)
Definition object_out (shared : bool) (ps : list (unit -> option (list (list line)))) : out :=
  match all_lines_rev ps [] with
  | None => Done 3 "a function is outside the subset or has no plan"
  | Some rev_lines =>
      match encode_lines false (rev' rev_lines) with
      | inr why => Done 3 ("no encoding for: " ++ why)
      | inl o =>
          if shared then
            match so_image o with
            | inl bs => Chunk (byte_parts (length bs) bs) (fun _ => Done 0 "")
            | inr why => Done 3 ("not linked: " ++ why)
            end
          else Chunk (dump_parts o) (fun _ => Done 0 "")
      end
  end.

(** The characters of the pieces. *)
Definition text_of (l : list string) : list ascii :=
  rev' (fold_left (fun acc s => rev_append (list_ascii_of_string s) acc) l []).

(** The functions among the outcomes, last first in front of [acc],
    and the comments rx.pl prints for the patterns it does not
    compile, last first in front of [why]. *)
Fixpoint rx_parts (os : list Rx.outcome) (acc : list term) (why : list string) : list term * list string :=
  match os with
  | [] => (acc, why)
  | Rx.Func f :: r => rx_parts r (f :: acc) why
  | Rx.Unsupported nm w :: r => rx_parts r acc (String.concat ""%string ["% "%string; nm; ": unsupported: "%string; w; nl] :: why)
  | Rx.Failed :: r => rx_parts r acc why
  end.

(** This number bounds the blocks of a function that `regex` compiles.
    A program waits in pcre2_jit_compile while the library compiles,
    and a compile's time grows faster than its function. The functions
    that rx.pl makes of PCRE2's tests compile in at most 5 seconds when
    they have up to 609 blocks. The next ones, of 830 to 1,029 blocks,
    take 6 to 13 seconds. rxc stops rx.pl and nanofil-backend after 10
    seconds, and this bound plays the same part: a larger pattern stays
    on PCRE2's interpreter. *)
Definition regex_max_blocks : nat := 620.

(** The name and the number of blocks of a function's term. *)
Definition func_size (f : term) : string * nat :=
  match f with
  | TApp _ [TAtom nm; _; _; _; TList bs] => (nm, length bs)
  | _ => (""%string, 0)
  end.

(** What `regex` gives for the terms [cs]: the shared object of the
    functions Rx.v makes of them, as experiments/regex-nanofil/rxc
    links rx.pl's; or 1 with rx.pl's comments when it does not compile
    a pattern, with a reason when rx.pl fails on the terms, or with the
    first function of more than [regex_max_blocks] blocks; or what
    compiling the module gives when it is not compiled. *)
Definition regex_out (cs : list ascii) : out :=
  let os := Rx.rx_outcomes cs in
  if existsb (fun o => match o with Rx.Failed => true | _ => false end) os
  then Done 1 "rx.pl fails on the terms"
  else
    match rx_parts os [] [] with
    | (_, (_ :: _) as why) => Done 1 (String.concat "" (rev' why))
    | (rfs, []) =>
        let fs := rev' rfs in
        match find (fun f => Nat.ltb regex_max_blocks (snd (func_size f))) fs with
        | Some f =>
            Done 1 (String.concat "" [fst (func_size f); " has "%string; decimal (Z.of_nat (snd (func_size f)));
                                      " blocks, more than the "%string; decimal (Z.of_nat regex_max_blocks);
                                      " that are compiled in process"%string])
        | None =>
            match compile_allocated (TApp "module" [TList fs]) with
            | Refused why => Done 1 why
            | Outside why => Done 3 why
            | Pieces ps => object_out true ps
            end
        end
    end.

(** A run of the command on the text. *)
Definition run (a : args) : out :=
  if Nat.eqb (cmd a) 5 then regex_out (text_of (input a)) else
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
      | Pieces ps =>
          if Nat.eqb (cmd a) 3 then object_out true ps
          else if Nat.eqb (cmd a) 4 then object_out false ps
          else emit_pieces ps
      end
  end.
