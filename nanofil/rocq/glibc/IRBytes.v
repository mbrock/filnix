(** A string literal can spell the bytes of a static initializer. Its printer
    checks the range of each integer before converting it back to a byte. *)

From Stdlib Require Import ZArith List Strings.Byte.
From Nanofil Require Import Syntax.
Import ListNotations.

Definition literal_bytes (xs : list byte) : data_item :=
  Str (map (fun x => Z.of_N (Byte.to_N x)) xs).

Fixpoint bytes_of_integers (xs : list Z) : option (list byte) :=
  match xs with
  | [] => Some []
  | x :: rest =>
      if Z.ltb x 0 then None else
      match Byte.of_N (Z.to_N x), bytes_of_integers rest with
      | Some b, Some bs => Some (b :: bs)
      | _, _ => None
      end
  end.

Definition bytes_of_literal (item : data_item) : option (list byte) :=
  match item with Str xs => bytes_of_integers xs | _ => None end.

Declare Scope irbytes_scope.
Delimit Scope irbytes_scope with irbytes.
String Notation data_item literal_bytes bytes_of_literal : irbytes_scope.
