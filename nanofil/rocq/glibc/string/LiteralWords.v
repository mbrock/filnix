(** Glibc’s string routines read literals a machine word at a time.
    The loader appends a terminator and pads the last word with zeros.
    These functions compute the words from the literal’s bytes. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** This function reads byte i of s followed by its terminator, and it
    gives zero past the end. *)
Definition lit_byte (s : list Z) (i : nat) : Z := nth i (s ++ [0]) 0.

(** These are the little-endian words that hold s, its terminator and the
    padding. *)
Definition lit_words (s : list Z) : list Z :=
  map (fun k => fold_right (fun j acc => lit_byte s (8 * k + j) + 256 * acc) 0 (seq 0 8))
    (seq 0 ((List.length s + 8) / 8)).
