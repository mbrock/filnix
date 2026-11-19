(** The glibc proofs use byte-valued character atoms when they name individual
    bytes in strings and data initializers. This file supplies the shared
    constructor for those atoms. *)

From Stdlib Require Import String Ascii.
From Nanofil Require Export Term Syntax Semantics.

(** A character atom preserves the byte with the given code. *)
Definition chr (n : nat) : term := TAtom (String (ascii_of_nat n) EmptyString).
