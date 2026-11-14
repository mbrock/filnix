(** Generated glibc fixtures encode checked instructions as terms before decoding
    them into functions. This file supplies their character constructor and
    decoding fallbacks, so every fixture uses the same definitions. *)

From Stdlib Require Import String Ascii List.
From Nanofil Require Export Term Syntax Transport Semantics.
Import ListNotations.

(** A character atom preserves the byte with the given code. *)
Definition chr (n : nat) : term := TAtom (String (ascii_of_nat n) EmptyString).

(** A malformed module term decodes to an empty module. Generated witnesses
    separately check that each fixture takes the successful decoding branch. *)
Definition code_module (t : term) : module :=
  match decode_module t with Some md => md | None => [] end.

(** A missing function name selects an empty body with that name. Generated
    lookup witnesses distinguish real bodies from this fallback. *)
Definition code_function (md : module) (n : string) : func :=
  match find_direct (TAtom n) md with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom n) (TAtom "export") (RClass W) [] []
  end.
